"""
LATTICE Adversarial Tests — Structural & Token Attacks (P2)

Tests for:
1. Circular dependency deadlock
2. Unbounded decomposition depth
3. Subscriber crash resilience
4. DCT signature forgery
5. DCT scope escalation
"""

import asyncio

import pytest
from pydantic import ValidationError

from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.models import (
    DelegationScope,
    RiskLevel,
    RoutingAction,
    SubTask,
    Trace,
)
from kovrin.engine.graph import ExecutionGraph
from kovrin.engine.tokens import ScopeViolationError, TokenAuthority
from kovrin.intent.schema import IntentV2


# ─── P2: Circular Dependency ─────────────────────────────

@pytest.mark.adversarial
class TestCircularDependency:
    """P2: Circular dependencies in task graph must not hang."""

    def test_circular_dependency_detected(self):
        """A → B → A cycle: execution_order returns incomplete waves (breaks cycle)."""
        graph = ExecutionGraph(intent_id="test")
        task_a = SubTask(id="a", description="Task A", dependencies=["b"])
        task_b = SubTask(id="b", description="Task B", dependencies=["a"])
        graph.add_node(task_a, dependencies={"b"})
        graph.add_node(task_b, dependencies={"a"})

        # execution_order breaks on cycle — returns empty because neither can start
        waves = graph.execution_order
        # All nodes remain in "remaining" set since neither has deps satisfied
        assigned_nodes = {nid for wave in waves for nid in wave}
        assert "a" not in assigned_nodes
        assert "b" not in assigned_nodes

    def test_self_dependency_handled(self):
        """A → A self-dependency: node never becomes ready."""
        graph = ExecutionGraph(intent_id="test")
        task_a = SubTask(id="a", description="Task A", dependencies=["a"])
        graph.add_node(task_a, dependencies={"a"})

        waves = graph.execution_order
        assigned_nodes = {nid for wave in waves for nid in wave}
        assert "a" not in assigned_nodes

        # get_ready_nodes should return nothing since dep on self not satisfied
        ready = graph.get_ready_nodes()
        assert len(ready) == 0


# ─── P2: Unbounded Decomposition ─────────────────────────

@pytest.mark.adversarial
class TestUnboundedDecomposition:
    """P2: Decomposition depth is bounded by IntentV2 model validation."""

    def test_max_depth_enforced(self):
        """IntentV2.max_decomposition_depth has upper bound of 20."""
        with pytest.raises(ValidationError):
            IntentV2(
                description="Infinite decomposition attempt",
                max_decomposition_depth=100,
            )

    def test_max_depth_boundary(self):
        """max_decomposition_depth=20 is the maximum allowed value."""
        intent = IntentV2(
            description="Maximum depth",
            max_decomposition_depth=20,
        )
        assert intent.max_decomposition_depth == 20

    def test_min_depth_boundary(self):
        """max_decomposition_depth=0 is below minimum (1)."""
        with pytest.raises(ValidationError):
            IntentV2(
                description="Zero depth",
                max_decomposition_depth=0,
            )


# ─── P2: Subscriber Crash ────────────────────────────────

@pytest.mark.adversarial
class TestSubscriberCrash:
    """P2: Crashing subscriber does not corrupt trace log."""

    @pytest.mark.asyncio
    async def test_subscriber_crash_preserves_chain(self):
        """A subscriber that raises exceptions must not break hash chain integrity."""
        log = ImmutableTraceLog()

        crash_count = 0

        async def crashing_subscriber(event: HashedTrace):
            nonlocal crash_count
            crash_count += 1
            raise RuntimeError("Subscriber crash!")

        log.subscribe(crashing_subscriber)

        # Append events through async path (which notifies subscribers)
        for i in range(5):
            await log.append_async(Trace(
                intent_id="intent-1",
                task_id=f"t{i}",
                event_type="TEST",
                description=f"Event {i}",
            ))

        # Subscriber was called but crashed
        assert crash_count == 5

        # Hash chain must still be intact
        valid, msg = log.verify_integrity()
        assert valid
        assert len(log) == 5


# ─── P2: DCT Signature Forgery ───────────────────────────

@pytest.mark.adversarial
class TestDCTForgery:
    """P2: Forged token signatures are rejected."""

    def test_forged_signature_rejected(self):
        """A token with a manually crafted signature is rejected by validate()."""
        authority = TokenAuthority(secret_key="real-secret")
        token = authority.issue("agent-1")

        # Forge the signature
        token.signature = "0" * 64

        valid, reason = authority.validate(token)
        assert not valid
        assert "signature" in reason.lower()

    def test_reuse_revoked_token_fails(self):
        """Attempting to validate a revoked token fails even with correct signature."""
        authority = TokenAuthority(secret_key="real-secret")
        token = authority.issue("agent-1")

        # Revoke
        authority.revoke(token.id)

        valid, reason = authority.validate(token)
        assert not valid
        assert "revoked" in reason.lower()

    def test_different_authority_rejects(self):
        """Token signed by one authority is invalid on another authority."""
        authority_a = TokenAuthority(secret_key="secret-a")
        authority_b = TokenAuthority(secret_key="secret-b")

        token = authority_a.issue("agent-1")

        valid, reason = authority_b.validate(token)
        assert not valid
        assert "signature" in reason.lower()


# ─── P2: DCT Scope Escalation ────────────────────────────

@pytest.mark.adversarial
class TestDCTScopeEscalation:
    """P2: Child tokens cannot escalate beyond parent scope."""

    def test_child_wider_risk_rejected(self):
        """Child requesting wider risk levels than parent is rejected."""
        authority = TokenAuthority(secret_key="test-key")
        parent_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
            max_tasks=10,
        )
        parent = authority.issue("agent-parent", parent_scope)

        child_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.HIGH],
            max_tasks=5,
        )
        with pytest.raises(ScopeViolationError, match="risk"):
            authority.issue("agent-child", child_scope, parent_token_id=parent.id)

    def test_child_wider_actions_rejected(self):
        """Child requesting wider actions than parent is rejected."""
        authority = TokenAuthority(secret_key="test-key")
        parent_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
            allowed_actions=[RoutingAction.AUTO_EXECUTE],
            max_tasks=10,
        )
        parent = authority.issue("agent-parent", parent_scope)

        child_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
            allowed_actions=[RoutingAction.AUTO_EXECUTE, RoutingAction.HUMAN_APPROVAL],
            max_tasks=5,
        )
        with pytest.raises(ScopeViolationError, match="actions"):
            authority.issue("agent-child", child_scope, parent_token_id=parent.id)
