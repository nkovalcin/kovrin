"""Tests for LATTICE Phase 6 — Delegation Capability Tokens."""

import time
from datetime import datetime, timedelta, timezone

import pytest

from kovrin.core.models import (
    DelegationScope,
    DelegationToken,
    RiskLevel,
    RoutingAction,
    SubTask,
)
from kovrin.engine.tokens import ScopeViolationError, TokenAuthority


# ─── Model Tests ──────────────────────────────────────────

class TestTokenModels:
    def test_delegation_scope_defaults(self):
        scope = DelegationScope()
        assert scope.allowed_risk_levels == [RiskLevel.LOW]
        assert scope.allowed_actions == [RoutingAction.AUTO_EXECUTE]
        assert scope.max_tasks == 10
        assert scope.max_depth == 1

    def test_delegation_token_defaults(self):
        token = DelegationToken(agent_id="agent-1")
        assert token.agent_id == "agent-1"
        assert token.id.startswith("dct-")
        assert token.revoked is False
        assert token.tasks_executed == 0
        assert token.signature == ""

    def test_delegation_scope_custom(self):
        scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.MEDIUM],
            allowed_actions=[RoutingAction.AUTO_EXECUTE, RoutingAction.SANDBOX_REVIEW],
            max_tasks=5,
            max_depth=2,
        )
        assert len(scope.allowed_risk_levels) == 2
        assert scope.max_tasks == 5


# ─── Token Authority Tests ────────────────────────────────

class TestTokenAuthority:
    def test_issue_basic(self):
        auth = TokenAuthority(secret_key="test-secret")
        token = auth.issue("agent-1")
        assert token.agent_id == "agent-1"
        assert token.signature != ""
        assert not token.revoked
        assert token.tasks_executed == 0

    def test_issue_with_scope(self):
        auth = TokenAuthority()
        scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.MEDIUM],
            max_tasks=3,
        )
        token = auth.issue("agent-1", scope=scope)
        assert token.scope.max_tasks == 3
        assert RiskLevel.MEDIUM in token.scope.allowed_risk_levels

    def test_issue_with_ttl(self):
        auth = TokenAuthority()
        token = auth.issue("agent-1", ttl_seconds=60)
        assert token.expires_at > token.issued_at
        delta = (token.expires_at - token.issued_at).total_seconds()
        assert 59 <= delta <= 61

    def test_validate_valid_token(self):
        auth = TokenAuthority(secret_key="secret")
        token = auth.issue("agent-1", ttl_seconds=300)
        valid, reason = auth.validate(token)
        assert valid is True
        assert reason == "Valid"

    def test_validate_revoked_token(self):
        auth = TokenAuthority()
        token = auth.issue("agent-1")
        auth.revoke(token.id)
        valid, reason = auth.validate(token)
        assert valid is False
        assert "revoked" in reason.lower()

    def test_validate_expired_token(self):
        auth = TokenAuthority()
        token = auth.issue("agent-1", ttl_seconds=0)
        # Token expires immediately (at issued_at + 0s = now)
        time.sleep(0.01)
        valid, reason = auth.validate(token)
        assert valid is False
        assert "expired" in reason.lower()

    def test_validate_invalid_signature(self):
        auth = TokenAuthority(secret_key="secret")
        token = auth.issue("agent-1")
        token.signature = "invalid-sig"
        valid, reason = auth.validate(token)
        assert valid is False
        assert "signature" in reason.lower()

    def test_active_tokens(self):
        auth = TokenAuthority()
        auth.issue("agent-1", ttl_seconds=300)
        auth.issue("agent-2", ttl_seconds=300)
        t3 = auth.issue("agent-3", ttl_seconds=300)
        auth.revoke(t3.id)
        assert len(auth.active_tokens) == 2

    def test_deterministic_signing(self):
        auth = TokenAuthority(secret_key="fixed")
        t1 = auth.issue("agent-1")
        sig1 = auth._sign(t1)
        sig2 = auth._sign(t1)
        assert sig1 == sig2


# ─── Scope Check Tests ───────────────────────────────────

class TestScopeCheck:
    def test_scope_allows_task(self):
        auth = TokenAuthority()
        scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.MEDIUM],
            max_tasks=5,
        )
        token = auth.issue("agent-1", scope=scope)
        task = SubTask(description="Test", risk_level=RiskLevel.LOW)
        ok, reason = auth.check_scope(token, task)
        assert ok is True

    def test_scope_denies_risk_level(self):
        auth = TokenAuthority()
        scope = DelegationScope(allowed_risk_levels=[RiskLevel.LOW])
        token = auth.issue("agent-1", scope=scope)
        task = SubTask(description="Test", risk_level=RiskLevel.HIGH)
        ok, reason = auth.check_scope(token, task)
        assert ok is False
        assert "risk level" in reason.lower()

    def test_scope_denies_max_tasks(self):
        auth = TokenAuthority()
        scope = DelegationScope(max_tasks=1)
        token = auth.issue("agent-1", scope=scope)
        token.tasks_executed = 1
        task = SubTask(description="Test", risk_level=RiskLevel.LOW)
        ok, reason = auth.check_scope(token, task)
        assert ok is False
        assert "max tasks" in reason.lower()

    def test_record_execution(self):
        auth = TokenAuthority()
        token = auth.issue("agent-1")
        assert token.tasks_executed == 0
        auth.record_execution(token)
        assert token.tasks_executed == 1
        auth.record_execution(token)
        assert token.tasks_executed == 2


# ─── Revocation Tests ────────────────────────────────────

class TestRevocation:
    def test_revoke_single(self):
        auth = TokenAuthority()
        token = auth.issue("agent-1")
        count = auth.revoke(token.id)
        assert count == 1
        assert token.revoked is True

    def test_revoke_cascades_to_children(self):
        auth = TokenAuthority()
        parent = auth.issue("agent-1", scope=DelegationScope(max_tasks=5))
        child1 = auth.issue("agent-2", scope=DelegationScope(max_tasks=3), parent_token_id=parent.id)
        child2 = auth.issue("agent-3", scope=DelegationScope(max_tasks=2), parent_token_id=parent.id)

        count = auth.revoke(parent.id)
        assert count == 3
        assert parent.revoked is True
        assert child1.revoked is True
        assert child2.revoked is True

    def test_revoke_idempotent(self):
        auth = TokenAuthority()
        token = auth.issue("agent-1")
        auth.revoke(token.id)
        count = auth.revoke(token.id)
        assert count == 0  # Already revoked

    def test_revoke_nonexistent(self):
        auth = TokenAuthority()
        count = auth.revoke("nonexistent-id")
        assert count == 0


# ─── Scope Narrowing Tests ────────────────────────────────

class TestScopeNarrowing:
    def test_equal_scope_allowed(self):
        auth = TokenAuthority()
        parent_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.MEDIUM],
            max_tasks=5,
        )
        parent = auth.issue("agent-1", scope=parent_scope)
        child = auth.issue("agent-2", scope=parent_scope, parent_token_id=parent.id)
        assert child.parent_token_id == parent.id

    def test_narrower_scope_allowed(self):
        auth = TokenAuthority()
        parent_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.MEDIUM],
            max_tasks=5,
        )
        child_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
            max_tasks=2,
        )
        parent = auth.issue("agent-1", scope=parent_scope)
        child = auth.issue("agent-2", scope=child_scope, parent_token_id=parent.id)
        assert child is not None

    def test_wider_risk_levels_rejected(self):
        auth = TokenAuthority()
        parent_scope = DelegationScope(allowed_risk_levels=[RiskLevel.LOW])
        child_scope = DelegationScope(allowed_risk_levels=[RiskLevel.LOW, RiskLevel.HIGH])
        parent = auth.issue("agent-1", scope=parent_scope)
        with pytest.raises(ScopeViolationError, match="risk levels"):
            auth.issue("agent-2", scope=child_scope, parent_token_id=parent.id)

    def test_wider_max_tasks_rejected(self):
        auth = TokenAuthority()
        parent_scope = DelegationScope(max_tasks=3)
        child_scope = DelegationScope(max_tasks=10)
        parent = auth.issue("agent-1", scope=parent_scope)
        with pytest.raises(ScopeViolationError, match="max_tasks"):
            auth.issue("agent-2", scope=child_scope, parent_token_id=parent.id)

    def test_wider_actions_rejected(self):
        auth = TokenAuthority()
        parent_scope = DelegationScope(allowed_actions=[RoutingAction.AUTO_EXECUTE])
        child_scope = DelegationScope(
            allowed_actions=[RoutingAction.AUTO_EXECUTE, RoutingAction.SANDBOX_REVIEW]
        )
        parent = auth.issue("agent-1", scope=parent_scope)
        with pytest.raises(ScopeViolationError, match="actions"):
            auth.issue("agent-2", scope=child_scope, parent_token_id=parent.id)

    def test_wider_max_depth_rejected(self):
        auth = TokenAuthority()
        parent_scope = DelegationScope(max_depth=1)
        child_scope = DelegationScope(max_depth=3)
        parent = auth.issue("agent-1", scope=parent_scope)
        with pytest.raises(ScopeViolationError, match="max_depth"):
            auth.issue("agent-2", scope=child_scope, parent_token_id=parent.id)


# ─── Trace Tests ──────────────────────────────────────────

class TestTokenTrace:
    def test_create_trace(self):
        token = DelegationToken(agent_id="agent-1")
        trace = TokenAuthority.create_trace(token, "ISSUED", "intent-1")
        assert trace.event_type == "TOKEN_ISSUED"
        assert "agent-1" in trace.description
        assert trace.details["token_id"] == token.id
        assert trace.details["agent_id"] == "agent-1"
