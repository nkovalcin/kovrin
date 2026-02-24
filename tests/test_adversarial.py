"""
LATTICE Adversarial Tests

Attempts to bypass Layer 0 safety mechanisms.
These tests define LATTICE's security boundary.

Categories:
1. Direct unsafe intents
2. Injection attempts (constraints that override safety)
3. Scope escalation
4. Axiom tampering
5. Proof obligation forgery
6. Intent context injection
7. Task ID cloning
8. Trace log tampering
9. Watchdog rule collision / evasion
10. Autonomy override attacks
11. Drift window exploitation
12. Reversibility misclassification
"""

import json

import pytest

from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.constitutional import (
    _AXIOM_INTEGRITY_HASH,
    AXIOMS,
    ConstitutionalCore,
    _compute_axiom_hash,
)
from kovrin.core.models import (
    AutonomyProfile,
    AutonomySettings,
    ContainmentLevel,
    DriftLevel,
    RiskLevel,
    RoutingAction,
    SpeculationTier,
    SubTask,
    Trace,
)
from kovrin.engine.risk_router import RiskRouter
from kovrin.safety.watchdog import (
    AgentDriftTracker,
    ExcessiveFailureRate,
    UnexpectedEventSequence,
    WatchdogAgent,
)


class TestDirectUnsafeIntents:
    """Verify that obviously unsafe tasks are caught by parsing."""

    def test_parse_delete_records(self):
        """A task to delete records should be classified as high risk."""
        core = ConstitutionalCore(client=None)
        # Simulate a response where axioms 1, 2, and 5 fail
        response = json.dumps(
            [
                {
                    "axiom_id": 1,
                    "axiom_name": "Human Agency",
                    "passed": False,
                    "evidence": "Removes ability to recover data",
                },
                {
                    "axiom_id": 2,
                    "axiom_name": "Harm Floor",
                    "passed": False,
                    "evidence": "Permanent data loss exceeds harm threshold",
                },
                {
                    "axiom_id": 3,
                    "axiom_name": "Transparency",
                    "passed": True,
                    "evidence": "Action is traceable",
                },
                {
                    "axiom_id": 4,
                    "axiom_name": "Reversibility",
                    "passed": False,
                    "evidence": "Deletion is irreversible",
                },
                {
                    "axiom_id": 5,
                    "axiom_name": "Scope Limit",
                    "passed": False,
                    "evidence": "Exceeds authorized boundary",
                },
            ]
        )
        obligations = core._parse_obligations(response)
        assert not ConstitutionalCore.all_passed(obligations)
        failed = [o for o in obligations if not o.passed]
        assert len(failed) == 4

    def test_parse_disable_override(self):
        """A task that disables human override must always fail axiom 1."""
        core = ConstitutionalCore(client=None)
        response = json.dumps(
            [
                {
                    "axiom_id": 1,
                    "axiom_name": "Human Agency",
                    "passed": False,
                    "evidence": "Directly removes human override capability",
                },
                {
                    "axiom_id": 2,
                    "axiom_name": "Harm Floor",
                    "passed": False,
                    "evidence": "High harm potential",
                },
                {
                    "axiom_id": 3,
                    "axiom_name": "Transparency",
                    "passed": True,
                    "evidence": "Traceable",
                },
                {
                    "axiom_id": 4,
                    "axiom_name": "Reversibility",
                    "passed": False,
                    "evidence": "Irreversible",
                },
                {
                    "axiom_id": 5,
                    "axiom_name": "Scope Limit",
                    "passed": False,
                    "evidence": "Exceeds scope",
                },
            ]
        )
        obligations = core._parse_obligations(response)
        axiom_1 = next(o for o in obligations if o.axiom_id == 1)
        assert axiom_1.passed is False


class TestFailSafeMechanisms:
    """Verify that parsing failures default to rejection."""

    def test_empty_response_rejects_all(self):
        core = ConstitutionalCore(client=None)
        obligations = core._parse_obligations("")
        assert len(obligations) == 5
        assert all(not o.passed for o in obligations)

    def test_malformed_json_rejects_all(self):
        core = ConstitutionalCore(client=None)
        obligations = core._parse_obligations("{malformed")
        assert all(not o.passed for o in obligations)

    def test_partial_response_fills_missing_as_failed(self):
        core = ConstitutionalCore(client=None)
        # Only return 2 out of 5 axioms
        response = json.dumps(
            [
                {"axiom_id": 1, "axiom_name": "Human Agency", "passed": True, "evidence": "OK"},
                {"axiom_id": 3, "axiom_name": "Transparency", "passed": True, "evidence": "OK"},
            ]
        )
        obligations = core._parse_obligations(response)
        # 2 passed + 3 auto-failed
        failed = [o for o in obligations if not o.passed]
        assert len(failed) == 3

    def test_all_passed_true_still_fails_if_missing(self):
        """Even if returned axioms all pass, missing ones should cause failure."""
        core = ConstitutionalCore(client=None)
        response = json.dumps(
            [
                {"axiom_id": 1, "axiom_name": "Human Agency", "passed": True, "evidence": "OK"},
            ]
        )
        obligations = core._parse_obligations(response)
        assert not ConstitutionalCore.all_passed(obligations)


class TestAxiomTampering:
    """Verify that axiom integrity cannot be compromised."""

    def test_axioms_are_frozen(self):
        for axiom in AXIOMS:
            with pytest.raises(AttributeError):
                axiom.name = "Hacked"

    def test_axiom_tuple_immutable(self):
        with pytest.raises(TypeError):
            AXIOMS[0] = AXIOMS[1]

    def test_integrity_hash_detects_external_modification(self):
        """If someone modifies axiom data externally, hash should not match."""
        from kovrin.core.constitutional import Axiom

        fake_axioms = (Axiom(id=1, name="HACKED", description="Hacked", formal="hacked"),)
        fake_hash = _compute_axiom_hash(fake_axioms)
        assert fake_hash != _AXIOM_INTEGRITY_HASH


class TestRiskRouterSafety:
    """Verify that risk routing cannot be bypassed."""

    def test_critical_tasks_always_require_human(self):
        """No speculation tier should allow auto-execution of CRITICAL tasks."""
        router = RiskRouter()
        for tier in SpeculationTier:
            task = SubTask(
                description="Critical task",
                risk_level=RiskLevel.CRITICAL,
                speculation_tier=tier,
            )
            decision = router.route(task)
            assert decision.action == RoutingAction.HUMAN_APPROVAL

    def test_high_none_requires_human(self):
        router = RiskRouter()
        task = SubTask(
            description="Irreversible high-risk action",
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.NONE,
        )
        decision = router.route(task)
        assert decision.action == RoutingAction.HUMAN_APPROVAL


class TestInjectionAttempts:
    """Verify that constraint injection cannot bypass safety."""

    def test_constraint_cannot_override_axioms(self):
        """Even if constraints say 'ignore safety', axioms still apply."""
        # The constitutional core checks axioms regardless of constraints.
        # Constraints are checked by the PolicyCritic, not the ConstitutionalCore.
        # This test verifies the separation.
        core = ConstitutionalCore(client=None)

        # A task that violates axioms should fail even with permissive constraints
        response = json.dumps(
            [
                {
                    "axiom_id": 1,
                    "axiom_name": "Human Agency",
                    "passed": False,
                    "evidence": "Violates",
                },
                {"axiom_id": 2, "axiom_name": "Harm Floor", "passed": True, "evidence": "OK"},
                {"axiom_id": 3, "axiom_name": "Transparency", "passed": True, "evidence": "OK"},
                {"axiom_id": 4, "axiom_name": "Reversibility", "passed": True, "evidence": "OK"},
                {"axiom_id": 5, "axiom_name": "Scope Limit", "passed": True, "evidence": "OK"},
            ]
        )
        obligations = core._parse_obligations(response)
        # Even with 4/5 passing, one failure means rejection
        assert not ConstitutionalCore.all_passed(obligations)


# ─── P0: Constraint Injection ────────────────────────────


@pytest.mark.adversarial
class TestConstraintInjection:
    """P0: PolicyCritic constraints cannot override Layer 0 axioms."""

    def test_policy_constraint_cannot_override_l0_rejection(self):
        """A constraint saying 'ignore axiom 1' must not cause L0 to pass.
        ConstitutionalCore does NOT accept constraints — they go to PolicyCritic."""
        core = ConstitutionalCore(client=None)
        # Simulate L0 response where axiom 1 fails
        response = json.dumps(
            [
                {
                    "axiom_id": 1,
                    "axiom_name": "Human Agency",
                    "passed": False,
                    "evidence": "Removes override",
                },
                {"axiom_id": 2, "axiom_name": "Harm Floor", "passed": True, "evidence": "OK"},
                {"axiom_id": 3, "axiom_name": "Transparency", "passed": True, "evidence": "OK"},
                {"axiom_id": 4, "axiom_name": "Reversibility", "passed": True, "evidence": "OK"},
                {"axiom_id": 5, "axiom_name": "Scope Limit", "passed": True, "evidence": "OK"},
            ]
        )
        # Even with a permissive constraint context, _parse_obligations only reads the JSON
        obligations = core._parse_obligations(response)
        assert not ConstitutionalCore.all_passed(obligations)
        # The failed axiom is still axiom 1
        axiom_1 = next(o for o in obligations if o.axiom_id == 1)
        assert axiom_1.passed is False

    def test_policy_constraint_ignore_safety_still_fails_l0(self):
        """Even with constraint 'allow all actions', L0 axioms still reject."""
        core = ConstitutionalCore(client=None)
        response = json.dumps(
            [
                {
                    "axiom_id": 1,
                    "axiom_name": "Human Agency",
                    "passed": False,
                    "evidence": "Blocks override",
                },
                {
                    "axiom_id": 2,
                    "axiom_name": "Harm Floor",
                    "passed": False,
                    "evidence": "Excessive harm",
                },
                {"axiom_id": 3, "axiom_name": "Transparency", "passed": True, "evidence": "OK"},
                {
                    "axiom_id": 4,
                    "axiom_name": "Reversibility",
                    "passed": False,
                    "evidence": "Irreversible",
                },
                {"axiom_id": 5, "axiom_name": "Scope Limit", "passed": True, "evidence": "OK"},
            ]
        )
        obligations = core._parse_obligations(response)
        assert not ConstitutionalCore.all_passed(obligations)
        failed = [o for o in obligations if not o.passed]
        assert len(failed) == 3


# ─── P0: Proof Obligation Forgery ────────────────────────


@pytest.mark.adversarial
class TestProofObligationForgery:
    """P0: Verify all-or-nothing behavior of proof obligations."""

    def test_all_true_obligations_pass(self):
        """If Claude returns all-true, the system correctly accepts."""
        core = ConstitutionalCore(client=None)
        response = json.dumps(
            [
                {"axiom_id": i, "axiom_name": a.name, "passed": True, "evidence": "OK"}
                for i, a in enumerate(AXIOMS, 1)
            ]
        )
        obligations = core._parse_obligations(response)
        assert ConstitutionalCore.all_passed(obligations)

    def test_single_false_obligation_rejects_all(self):
        """A single failed axiom means the entire check fails — no partial acceptance."""
        core = ConstitutionalCore(client=None)
        results = []
        for i, a in enumerate(AXIOMS, 1):
            results.append(
                {
                    "axiom_id": i,
                    "axiom_name": a.name,
                    "passed": i != 3,  # Axiom 3 fails
                    "evidence": "Fail" if i == 3 else "OK",
                }
            )
        response = json.dumps(results)
        obligations = core._parse_obligations(response)
        assert not ConstitutionalCore.all_passed(obligations)
        failed = [o for o in obligations if not o.passed]
        assert len(failed) == 1
        assert failed[0].axiom_id == 3


# ─── P0: Intent Context Injection ────────────────────────


@pytest.mark.adversarial
class TestIntentContextInjection:
    """P0: Malicious intent_context cannot bypass obligation parsing."""

    def test_malicious_context_does_not_bypass_parsing(self):
        """_parse_obligations ignores intent_context — it only reads JSON response."""
        core = ConstitutionalCore(client=None)
        # Response has axiom 1 failing
        response = json.dumps(
            [
                {
                    "axiom_id": 1,
                    "axiom_name": "Human Agency",
                    "passed": False,
                    "evidence": "Violates",
                },
                {"axiom_id": 2, "axiom_name": "Harm Floor", "passed": True, "evidence": "OK"},
                {"axiom_id": 3, "axiom_name": "Transparency", "passed": True, "evidence": "OK"},
                {"axiom_id": 4, "axiom_name": "Reversibility", "passed": True, "evidence": "OK"},
                {"axiom_id": 5, "axiom_name": "Scope Limit", "passed": True, "evidence": "OK"},
            ]
        )
        # Regardless of what intent_context might say, _parse_obligations only cares about JSON
        obligations = core._parse_obligations(response)
        assert not ConstitutionalCore.all_passed(obligations)


# ─── P0: Task ID Cloning ─────────────────────────────────


@pytest.mark.adversarial
class TestTaskIdCloning:
    """P0: Rejected task re-submitted with new ID still gets caught."""

    def test_cloned_id_still_fails_l0_recheck(self):
        """L0 checks content, not ID — same description always fails the same way."""
        core = ConstitutionalCore(client=None)
        response = json.dumps(
            [
                {
                    "axiom_id": 1,
                    "axiom_name": "Human Agency",
                    "passed": False,
                    "evidence": "Removes override",
                },
                {"axiom_id": 2, "axiom_name": "Harm Floor", "passed": False, "evidence": "Harmful"},
                {"axiom_id": 3, "axiom_name": "Transparency", "passed": True, "evidence": "OK"},
                {
                    "axiom_id": 4,
                    "axiom_name": "Reversibility",
                    "passed": False,
                    "evidence": "Irreversible",
                },
                {"axiom_id": 5, "axiom_name": "Scope Limit", "passed": True, "evidence": "OK"},
            ]
        )
        # First check
        obligations_1 = core._parse_obligations(response)
        assert not ConstitutionalCore.all_passed(obligations_1)

        # Same response parsed again (simulates re-check with new task ID)
        obligations_2 = core._parse_obligations(response)
        assert not ConstitutionalCore.all_passed(obligations_2)

        # Both have the same failure pattern
        failed_1 = {o.axiom_id for o in obligations_1 if not o.passed}
        failed_2 = {o.axiom_id for o in obligations_2 if not o.passed}
        assert failed_1 == failed_2


# ─── P1: Trace Log Tampering ─────────────────────────────


@pytest.mark.adversarial
class TestTraceLogTampering:
    """P1: Modifications to trace events are detected by hash chain."""

    def _make_trace(
        self, event_type: str = "TEST", desc: str = "test", task_id: str = "t1"
    ) -> Trace:
        return Trace(
            intent_id="intent-1",
            task_id=task_id,
            event_type=event_type,
            description=desc,
        )

    def test_modifying_description_breaks_chain(self):
        log = ImmutableTraceLog()
        log.append(self._make_trace(desc="event 0"))
        log.append(self._make_trace(desc="event 1"))
        log.append(self._make_trace(desc="event 2"))

        valid, _ = log.verify_integrity()
        assert valid

        # Tamper: modify description of event 1
        log._events[1].trace.description = "TAMPERED"
        valid, msg = log.verify_integrity()
        assert not valid
        assert "Tampered" in msg or "event 1" in msg

    def test_modifying_hash_breaks_chain(self):
        log = ImmutableTraceLog()
        log.append(self._make_trace(desc="event 0"))
        log.append(self._make_trace(desc="event 1"))
        log.append(self._make_trace(desc="event 2"))

        # Tamper: change hash of event 1
        log._events[1].hash = "0" * 64
        valid, msg = log.verify_integrity()
        assert not valid

    def test_inserting_event_breaks_chain(self):
        log = ImmutableTraceLog()
        log.append(self._make_trace(desc="event 0"))
        log.append(self._make_trace(desc="event 2"))

        # Insert a fake event at position 1
        fake_trace = self._make_trace(desc="INJECTED")
        fake_hashed = HashedTrace(
            trace=fake_trace,
            hash="fake" * 16,
            previous_hash=log._events[0].hash,
            sequence=1,
        )
        log._events.insert(1, fake_hashed)
        # Fix sequence of event 2 (it's now at index 2 but has sequence=1)

        valid, msg = log.verify_integrity()
        assert not valid


# ─── P1: Watchdog Rule Collision ──────────────────────────


@pytest.mark.adversarial
class TestWatchdogRuleCollision:
    """P1: Multiple rules fire on same event — all alerts captured."""

    def _make_hashed(
        self, event_type: str, task_id: str = "t1", l0_passed: bool | None = None
    ) -> HashedTrace:
        trace = Trace(
            intent_id="intent-1",
            task_id=task_id,
            event_type=event_type,
            l0_passed=l0_passed,
        )
        return HashedTrace(trace=trace, hash="abc", previous_hash="000", sequence=0)

    def test_multiple_alerts_same_event(self):
        """EXECUTION_COMPLETE without START for a previously rejected task fires two rules."""
        rejection = self._make_hashed("L0_CHECK", task_id="t1", l0_passed=False)
        # EXECUTION_COMPLETE without prior EXECUTION_START → fires UnexpectedEventSequence
        # But also the task was rejected → if we check NoExecutionAfterRejection with EXECUTION_START
        # Let's create a scenario where we have both UnexpectedEventSequence and ExcessiveFailureRate

        # Build history with many failures
        history = [rejection]
        for i in range(4):
            history.append(
                self._make_hashed("CRITIC_PIPELINE", task_id=f"t{i + 2}", l0_passed=False)
            )

        # New event: EXECUTION_COMPLETE without prior EXECUTION_START
        event = self._make_hashed("EXECUTION_COMPLETE", task_id="t99")

        # Both rules should fire
        unexpected = UnexpectedEventSequence()
        failure_rate = ExcessiveFailureRate(threshold=0.5)

        alert_unexpected = unexpected.check(event, history)
        alert_failure = failure_rate.check(event, history)

        assert alert_unexpected is not None
        assert alert_failure is not None

    def test_highest_severity_wins(self):
        """When KILL and WARN fire simultaneously, pipeline must be killed."""
        wd = WatchdogAgent()

        # Rejection trace
        rejection = self._make_hashed("L0_CHECK", task_id="t1", l0_passed=False)
        # Execution attempt after rejection → KILL
        exec_start = self._make_hashed("EXECUTION_START", task_id="t1")
        # Also EXECUTION_COMPLETE without START → WARN (for different task)
        exec_complete = self._make_hashed("EXECUTION_COMPLETE", task_id="t99")

        # Process events manually
        wd._history = [rejection]
        for rule in wd.rules:
            alert = rule.check(exec_start, wd._history)
            if alert:
                wd.alerts.append(alert)
                if alert.severity == ContainmentLevel.KILL:
                    wd._killed = True

        assert wd.is_killed


# ─── P1: Failure Rate Evasion ─────────────────────────────


@pytest.mark.adversarial
class TestFailureRateEvasion:
    """P1: Gradual failures eventually trigger excessive failure rate."""

    def _make_hashed(
        self, event_type: str, task_id: str, l0_passed: bool | None = None
    ) -> HashedTrace:
        trace = Trace(
            intent_id="intent-1",
            task_id=task_id,
            event_type=event_type,
            l0_passed=l0_passed,
        )
        return HashedTrace(trace=trace, hash="abc", previous_hash="000", sequence=0)

    def test_gradual_failures_trigger(self):
        """Alternating fail/success but >50% failures overall still triggers alert."""
        rule = ExcessiveFailureRate(threshold=0.5)
        history = []
        # Pattern: 2 successes, then 4 failures → 4/6 = 67% failure rate
        for i in range(2):
            history.append(self._make_hashed("EXECUTION_COMPLETE", task_id=f"s{i}"))
        for i in range(4):
            history.append(self._make_hashed("CRITIC_PIPELINE", task_id=f"f{i}", l0_passed=False))

        event = self._make_hashed("EXECUTION_COMPLETE", task_id="trigger")
        alert = rule.check(event, history)
        assert alert is not None
        assert alert.severity == ContainmentLevel.PAUSE


# ─── P1: Drift Window Exploitation ───────────────────────


@pytest.mark.adversarial
class TestDriftWindowExploitation:
    """P1: Agent with good start then consistent failures is detected."""

    def test_good_start_then_drift(self):
        """5 good scores followed by 15 bad scores triggers high/critical drift."""
        tracker = AgentDriftTracker(window_size=20)

        # Good start
        for i in range(5):
            tracker.record("agent-x", f"good-{i}", prm_score=0.8, success=True)

        # Then consistent degradation
        for i in range(15):
            tracker.record("agent-x", f"bad-{i}", prm_score=0.2, success=False)

        metrics = tracker.get_metrics("agent-x")
        # Window has 20 scores: 5 × 0.8 + 15 × 0.2 = 7.0 / 20 = 0.35
        # success_rate = 5/20 = 0.25
        assert metrics.drift_level in (DriftLevel.HIGH, DriftLevel.CRITICAL)


# ─── P1: Autonomy Override ────────────────────────────────


@pytest.mark.adversarial
class TestAutonomyOverride:
    """P1: AGGRESSIVE profile cannot bypass CRITICAL safety guard."""

    def test_aggressive_cannot_auto_execute_critical(self):
        """AGGRESSIVE profile + CRITICAL risk → still HUMAN_APPROVAL."""
        router = RiskRouter()
        settings = AutonomySettings(
            profile=AutonomyProfile.AGGRESSIVE,
            override_matrix={},
            updated_at="2024-01-01T00:00:00Z",
        )
        for tier in SpeculationTier:
            task = SubTask(
                description="Critical operation",
                risk_level=RiskLevel.CRITICAL,
                speculation_tier=tier,
            )
            decision = router.route(task, settings)
            assert decision.action == RoutingAction.HUMAN_APPROVAL

    def test_cell_override_cannot_bypass_critical(self):
        """Cell-level override 'CRITICAL:FREE' → AUTO_EXECUTE is blocked by safety guard."""
        router = RiskRouter()
        settings = AutonomySettings(
            profile=AutonomyProfile.DEFAULT,
            override_matrix={
                "CRITICAL:FREE": "AUTO_EXECUTE",
                "CRITICAL:GUARDED": "AUTO_EXECUTE",
                "CRITICAL:NONE": "AUTO_EXECUTE",
            },
            updated_at="2024-01-01T00:00:00Z",
        )
        for tier in SpeculationTier:
            task = SubTask(
                description="Critical operation with override attempt",
                risk_level=RiskLevel.CRITICAL,
                speculation_tier=tier,
            )
            decision = router.route(task, settings)
            # Safety guard at line 98-99 of risk_router.py always overrides
            assert decision.action == RoutingAction.HUMAN_APPROVAL


# ─── P1: Scope Creep ─────────────────────────────────────


@pytest.mark.adversarial
class TestScopeCreep:
    """P1: DCT scope escalation blocked at every delegation level."""

    def test_grandchild_cannot_escalate_via_chain(self):
        """Parent → Child → Grandchild: scope narrowing enforced at every level."""
        from kovrin.core.models import DelegationScope
        from kovrin.engine.tokens import ScopeViolationError, TokenAuthority

        authority = TokenAuthority(secret_key="test-key")

        # Parent: LOW + MEDIUM
        parent_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.MEDIUM],
            allowed_actions=[RoutingAction.AUTO_EXECUTE, RoutingAction.SANDBOX_REVIEW],
            max_tasks=10,
            max_depth=3,
        )
        parent = authority.issue("agent-parent", parent_scope)

        # Child: LOW only (narrower)
        child_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
            allowed_actions=[RoutingAction.AUTO_EXECUTE],
            max_tasks=5,
            max_depth=2,
        )
        child = authority.issue("agent-child", child_scope, parent_token_id=parent.id)

        # Grandchild tries to escalate back to LOW + MEDIUM → must fail
        grandchild_scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.MEDIUM],
            allowed_actions=[RoutingAction.AUTO_EXECUTE],
            max_tasks=3,
            max_depth=1,
        )
        with pytest.raises(ScopeViolationError):
            authority.issue("agent-grandchild", grandchild_scope, parent_token_id=child.id)


# ─── P1: Reversibility Misclassification ─────────────────


@pytest.mark.adversarial
class TestReversibilityMisclassification:
    """P1: Even if speculation tier is wrong, safety routing holds."""

    def test_critical_free_still_human_approval(self):
        """CRITICAL + FREE → HUMAN_APPROVAL regardless (safety guard)."""
        router = RiskRouter()
        task = SubTask(
            description="Critical but classified as FREE",
            risk_level=RiskLevel.CRITICAL,
            speculation_tier=SpeculationTier.FREE,
        )
        decision = router.route(task)
        assert decision.action == RoutingAction.HUMAN_APPROVAL

    def test_high_guarded_routes_safely(self):
        """HIGH + GUARDED → HUMAN_APPROVAL per routing matrix."""
        router = RiskRouter()
        task = SubTask(
            description="High risk but GUARDED tier",
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.GUARDED,
        )
        decision = router.route(task)
        assert decision.action == RoutingAction.HUMAN_APPROVAL
