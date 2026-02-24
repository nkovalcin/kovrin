"""Tests for LATTICE Risk Router."""

from kovrin.core.models import (
    RiskLevel,
    RoutingAction,
    SpeculationTier,
    SubTask,
)
from kovrin.engine.risk_router import RiskRouter


class TestRiskRouter:
    def setup_method(self):
        self.router = RiskRouter()

    def _make_task(self, risk: RiskLevel, tier: SpeculationTier) -> SubTask:
        return SubTask(
            description=f"Task with {risk.value}/{tier.value}",
            risk_level=risk,
            speculation_tier=tier,
        )

    # AUTO_EXECUTE cases
    def test_low_free_auto_executes(self):
        decision = self.router.route(self._make_task(RiskLevel.LOW, SpeculationTier.FREE))
        assert decision.action == RoutingAction.AUTO_EXECUTE

    def test_low_guarded_auto_executes(self):
        decision = self.router.route(self._make_task(RiskLevel.LOW, SpeculationTier.GUARDED))
        assert decision.action == RoutingAction.AUTO_EXECUTE

    def test_medium_free_auto_executes(self):
        decision = self.router.route(self._make_task(RiskLevel.MEDIUM, SpeculationTier.FREE))
        assert decision.action == RoutingAction.AUTO_EXECUTE

    # SANDBOX_REVIEW cases
    def test_low_none_sandbox_review(self):
        decision = self.router.route(self._make_task(RiskLevel.LOW, SpeculationTier.NONE))
        assert decision.action == RoutingAction.SANDBOX_REVIEW

    def test_medium_guarded_sandbox_review(self):
        decision = self.router.route(self._make_task(RiskLevel.MEDIUM, SpeculationTier.GUARDED))
        assert decision.action == RoutingAction.SANDBOX_REVIEW

    def test_high_free_sandbox_review(self):
        decision = self.router.route(self._make_task(RiskLevel.HIGH, SpeculationTier.FREE))
        assert decision.action == RoutingAction.SANDBOX_REVIEW

    # HUMAN_APPROVAL cases
    def test_medium_none_human_approval(self):
        decision = self.router.route(self._make_task(RiskLevel.MEDIUM, SpeculationTier.NONE))
        assert decision.action == RoutingAction.HUMAN_APPROVAL

    def test_high_guarded_human_approval(self):
        decision = self.router.route(self._make_task(RiskLevel.HIGH, SpeculationTier.GUARDED))
        assert decision.action == RoutingAction.HUMAN_APPROVAL

    def test_high_none_human_approval(self):
        decision = self.router.route(self._make_task(RiskLevel.HIGH, SpeculationTier.NONE))
        assert decision.action == RoutingAction.HUMAN_APPROVAL

    def test_critical_always_human_approval(self):
        for tier in SpeculationTier:
            decision = self.router.route(self._make_task(RiskLevel.CRITICAL, tier))
            assert decision.action == RoutingAction.HUMAN_APPROVAL

    # Decision metadata
    def test_decision_includes_reason(self):
        decision = self.router.route(self._make_task(RiskLevel.LOW, SpeculationTier.FREE))
        assert decision.reason != ""
        assert "LOW" in decision.reason

    def test_decision_includes_task_id(self):
        task = self._make_task(RiskLevel.LOW, SpeculationTier.FREE)
        decision = self.router.route(task)
        assert decision.task_id == task.id

    # Trace creation
    def test_create_trace(self):
        task = self._make_task(RiskLevel.MEDIUM, SpeculationTier.GUARDED)
        decision = self.router.route(task)
        trace = RiskRouter.create_trace(task, decision, "intent-1")
        assert trace.event_type == "RISK_ROUTING"
        assert "SANDBOX_REVIEW" in trace.description

    # Full matrix coverage
    def test_all_combinations_covered(self):
        """Every risk/tier combination should produce a valid decision."""
        for risk in RiskLevel:
            for tier in SpeculationTier:
                decision = self.router.route(self._make_task(risk, tier))
                assert decision.action in RoutingAction
