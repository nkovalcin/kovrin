"""Tests for LATTICE Phase 5 — Decision Replay and Counterfactual."""

import pytest

from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import (
    AutonomyProfile,
    AutonomySettings,
    CounterfactualRequest,
    CounterfactualResult,
    ReplayFrame,
    ReplaySession,
    RiskLevel,
    RoutingAction,
    SpeculationTier,
    SubTask,
    Trace,
)
from kovrin.engine.risk_router import RiskRouter


# ─── Replay Model Tests ───────────────────────────────────

class TestReplayModels:
    def test_replay_frame_defaults(self):
        frame = ReplayFrame()
        assert frame.sequence == 0
        assert frame.hash == ""
        assert frame.previous_hash == ""
        assert frame.counterfactual_action is None

    def test_replay_session_defaults(self):
        session = ReplaySession(intent_id="test-123")
        assert session.intent_id == "test-123"
        assert session.total_frames == 0
        assert session.chain_valid is True
        assert session.chain_message == ""

    def test_counterfactual_request(self):
        req = CounterfactualRequest(
            intent_id="test-123",
            autonomy_settings=AutonomySettings(profile=AutonomyProfile.CAUTIOUS),
        )
        assert req.intent_id == "test-123"
        assert req.autonomy_settings.profile == AutonomyProfile.CAUTIOUS

    def test_counterfactual_result(self):
        result = CounterfactualResult(
            task_id="task-1",
            task_description="Test task",
            actual_action=RoutingAction.AUTO_EXECUTE,
            counterfactual_action=RoutingAction.HUMAN_APPROVAL,
            changed=True,
            risk_level=RiskLevel.MEDIUM,
            speculation_tier=SpeculationTier.GUARDED,
        )
        assert result.changed is True
        assert result.actual_action != result.counterfactual_action


# ─── Trace Logger Extension Tests ─────────────────────────

class TestTraceLoggerExtensions:
    def test_get_events_since(self):
        log = ImmutableTraceLog()
        for i in range(5):
            log.append(Trace(event_type=f"EVENT_{i}"))

        events = log.get_events_since(3)
        assert len(events) == 2
        assert events[0].sequence == 3
        assert events[1].sequence == 4

    def test_get_events_since_zero(self):
        log = ImmutableTraceLog()
        for i in range(3):
            log.append(Trace(event_type=f"EVENT_{i}"))

        events = log.get_events_since(0)
        assert len(events) == 3

    def test_get_events_since_beyond_end(self):
        log = ImmutableTraceLog()
        log.append(Trace(event_type="ONLY"))
        events = log.get_events_since(10)
        assert len(events) == 0

    def test_get_frame_at(self):
        log = ImmutableTraceLog()
        log.append(Trace(event_type="FIRST"))
        log.append(Trace(event_type="SECOND"))
        log.append(Trace(event_type="THIRD"))

        frame = log.get_frame_at(1)
        assert frame is not None
        assert frame.trace.event_type == "SECOND"
        assert frame.sequence == 1

    def test_get_frame_at_invalid(self):
        log = ImmutableTraceLog()
        log.append(Trace(event_type="ONLY"))
        assert log.get_frame_at(5) is None

    def test_get_frame_at_empty_log(self):
        log = ImmutableTraceLog()
        assert log.get_frame_at(0) is None


# ─── Counterfactual Routing Tests ─────────────────────────

class TestCounterfactualRouting:
    def test_counterfactual_detects_changes(self):
        """Compare actual routing vs hypothetical CAUTIOUS profile."""
        router = RiskRouter()
        task = SubTask(
            description="Medium risk task",
            risk_level=RiskLevel.MEDIUM,
            speculation_tier=SpeculationTier.GUARDED,
        )

        actual = router.route(task)
        hypothetical = router.route(task, AutonomySettings(profile=AutonomyProfile.CAUTIOUS))

        assert actual.action == RoutingAction.SANDBOX_REVIEW
        assert hypothetical.action == RoutingAction.HUMAN_APPROVAL
        assert actual.action != hypothetical.action

    def test_counterfactual_no_change_for_low_free(self):
        """LOW/FREE should remain AUTO_EXECUTE under CAUTIOUS."""
        router = RiskRouter()
        task = SubTask(
            description="Low risk task",
            risk_level=RiskLevel.LOW,
            speculation_tier=SpeculationTier.FREE,
        )

        actual = router.route(task)
        hypothetical = router.route(task, AutonomySettings(profile=AutonomyProfile.CAUTIOUS))

        assert actual.action == hypothetical.action == RoutingAction.AUTO_EXECUTE

    def test_counterfactual_aggressive_relaxes_routing(self):
        """AGGRESSIVE should relax HIGH/FREE from SANDBOX to AUTO."""
        router = RiskRouter()
        task = SubTask(
            description="High risk task",
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.FREE,
        )

        actual = router.route(task)
        hypothetical = router.route(task, AutonomySettings(profile=AutonomyProfile.AGGRESSIVE))

        assert actual.action == RoutingAction.SANDBOX_REVIEW
        assert hypothetical.action == RoutingAction.AUTO_EXECUTE

    def test_counterfactual_locked_escalates_everything(self):
        """LOCKED should escalate everything to HUMAN_APPROVAL."""
        router = RiskRouter()
        task = SubTask(
            description="Low task",
            risk_level=RiskLevel.LOW,
            speculation_tier=SpeculationTier.FREE,
        )

        actual = router.route(task)
        hypothetical = router.route(task, AutonomySettings(profile=AutonomyProfile.LOCKED))

        assert actual.action == RoutingAction.AUTO_EXECUTE
        assert hypothetical.action == RoutingAction.HUMAN_APPROVAL
