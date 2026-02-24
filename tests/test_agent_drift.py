"""Tests for LATTICE Phase 6 — Multi-agent Drift Detection."""

import pytest

from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.models import (
    AgentDriftMetrics,
    ContainmentLevel,
    DriftLevel,
    RiskLevel,
    Trace,
)
from kovrin.safety.watchdog import (
    AgentCompetencyDrift,
    AgentDriftTracker,
    CrossAgentConsistency,
    WatchdogAgent,
    make_agent_drift_rules,
)


# ─── Drift Tracker Tests ─────────────────────────────────

class TestAgentDriftTracker:
    def test_empty_tracker(self):
        tracker = AgentDriftTracker()
        metrics = tracker.get_metrics("unknown")
        assert metrics.agent_name == "unknown"
        assert metrics.total_executions == 0
        assert metrics.drift_level == DriftLevel.NONE

    def test_record_and_get(self):
        tracker = AgentDriftTracker()
        tracker.record("agent-1", "t1", prm_score=0.8, success=True)
        tracker.record("agent-1", "t2", prm_score=0.7, success=True)
        metrics = tracker.get_metrics("agent-1")
        assert metrics.total_executions == 2
        assert 0.74 <= metrics.average_prm_score <= 0.76
        assert metrics.success_rate == 1.0
        assert metrics.drift_level == DriftLevel.NONE

    def test_drift_level_moderate(self):
        tracker = AgentDriftTracker()
        for i in range(5):
            tracker.record("agent-1", f"t{i}", prm_score=0.45, success=True)
        metrics = tracker.get_metrics("agent-1")
        assert metrics.drift_level == DriftLevel.MODERATE

    def test_drift_level_high_low_score(self):
        tracker = AgentDriftTracker()
        for i in range(5):
            tracker.record("agent-1", f"t{i}", prm_score=0.3, success=True)
        metrics = tracker.get_metrics("agent-1")
        assert metrics.drift_level == DriftLevel.HIGH

    def test_drift_level_high_low_success(self):
        tracker = AgentDriftTracker()
        for i in range(6):
            tracker.record("agent-1", f"t{i}", prm_score=0.6, success=i < 2)
        metrics = tracker.get_metrics("agent-1")
        # success_rate = 2/6 ≈ 33% < 50%
        assert metrics.drift_level == DriftLevel.HIGH

    def test_drift_level_critical(self):
        tracker = AgentDriftTracker()
        for i in range(5):
            tracker.record("agent-1", f"t{i}", prm_score=0.15, success=i == 0)
        metrics = tracker.get_metrics("agent-1")
        # avg 0.15 < 0.2 and success 20% < 30%
        assert metrics.drift_level == DriftLevel.CRITICAL

    def test_drift_level_none_insufficient_data(self):
        tracker = AgentDriftTracker()
        tracker.record("agent-1", "t1", prm_score=0.1, success=False)
        tracker.record("agent-1", "t2", prm_score=0.1, success=False)
        metrics = tracker.get_metrics("agent-1")
        # Only 2 samples < 3 minimum
        assert metrics.drift_level == DriftLevel.NONE

    def test_sliding_window(self):
        tracker = AgentDriftTracker(window_size=5)
        for i in range(10):
            tracker.record("agent-1", f"t{i}", prm_score=0.9 if i >= 5 else 0.1)
        metrics = tracker.get_metrics("agent-1")
        # Only last 5 scores (all 0.9)
        assert metrics.average_prm_score >= 0.85

    def test_get_all_metrics(self):
        tracker = AgentDriftTracker()
        tracker.record("agent-1", "t1", prm_score=0.8)
        tracker.record("agent-2", "t2", prm_score=0.5)
        all_metrics = tracker.get_all_metrics()
        assert len(all_metrics) == 2
        names = {m.agent_name for m in all_metrics}
        assert names == {"agent-1", "agent-2"}

    def test_no_prm_score(self):
        tracker = AgentDriftTracker()
        tracker.record("agent-1", "t1", success=True)
        metrics = tracker.get_metrics("agent-1")
        assert metrics.total_executions == 1
        assert metrics.average_prm_score == 0.0
        assert metrics.recent_prm_scores == []


# ─── AgentCompetencyDrift Rule Tests ──────────────────────

class TestAgentCompetencyDriftRule:
    def _make_hashed(self, event_type: str, details: dict | None = None, task_id: str = "t1", intent_id: str = "i1") -> HashedTrace:
        trace = Trace(
            event_type=event_type,
            task_id=task_id,
            intent_id=intent_id,
            details=details or {},
        )
        return HashedTrace(trace=trace, hash="abc", previous_hash="000", sequence=0)

    def test_ignores_non_prm_events(self):
        tracker = AgentDriftTracker()
        rule = AgentCompetencyDrift(tracker)
        event = self._make_hashed("EXECUTION_COMPLETE")
        assert rule.check(event, []) is None

    def test_no_alert_without_agent_name(self):
        tracker = AgentDriftTracker()
        rule = AgentCompetencyDrift(tracker)
        event = self._make_hashed("PRM_EVALUATION", {"aggregate_score": 0.3})
        assert rule.check(event, []) is None

    def test_warn_on_moderate_drift(self):
        tracker = AgentDriftTracker()
        # Pre-seed with moderate scores
        for i in range(4):
            tracker.record("agent-1", f"t{i}", prm_score=0.45)

        rule = AgentCompetencyDrift(tracker)
        event = self._make_hashed("PRM_EVALUATION", {
            "agent_name": "agent-1",
            "aggregate_score": 0.45,
        })
        alert = rule.check(event, [])
        assert alert is not None
        assert alert.severity == ContainmentLevel.WARN

    def test_pause_on_high_drift(self):
        tracker = AgentDriftTracker()
        for i in range(4):
            tracker.record("agent-1", f"t{i}", prm_score=0.3)

        rule = AgentCompetencyDrift(tracker)
        event = self._make_hashed("PRM_EVALUATION", {
            "agent_name": "agent-1",
            "aggregate_score": 0.3,
        })
        alert = rule.check(event, [])
        assert alert is not None
        assert alert.severity == ContainmentLevel.PAUSE

    def test_kill_on_critical_drift(self):
        tracker = AgentDriftTracker()
        for i in range(4):
            tracker.record("agent-1", f"t{i}", prm_score=0.15, success=False)

        rule = AgentCompetencyDrift(tracker)
        event = self._make_hashed("PRM_EVALUATION", {
            "agent_name": "agent-1",
            "aggregate_score": 0.15,
        })
        alert = rule.check(event, [])
        assert alert is not None
        assert alert.severity == ContainmentLevel.KILL


# ─── CrossAgentConsistency Rule Tests ─────────────────────

class TestCrossAgentConsistencyRule:
    def _make_hashed(self, event_type: str, desc: str, task_id: str, intent_id: str = "i1") -> HashedTrace:
        trace = Trace(
            event_type=event_type,
            description=desc,
            task_id=task_id,
            intent_id=intent_id,
        )
        return HashedTrace(trace=trace, hash="abc", previous_hash="000", sequence=0)

    def test_ignores_non_completion(self):
        rule = CrossAgentConsistency()
        event = self._make_hashed("EXECUTION_START", "starting task", "t1")
        assert rule.check(event, []) is None

    def test_no_alert_no_contradiction(self):
        rule = CrossAgentConsistency()
        past = self._make_hashed("EXECUTION_COMPLETE", "Task success approved", "t1")
        event = self._make_hashed("EXECUTION_COMPLETE", "Task success valid", "t2")
        assert rule.check(event, [past]) is None

    def test_alert_on_contradiction(self):
        rule = CrossAgentConsistency()
        past = self._make_hashed("EXECUTION_COMPLETE", "Task approved success valid", "t1")
        event = self._make_hashed("EXECUTION_COMPLETE", "Task rejected failure invalid", "t2")
        alert = rule.check(event, [past])
        assert alert is not None
        assert alert.severity == ContainmentLevel.WARN
        assert "Contradictory" in alert.reason

    def test_no_alert_different_intents(self):
        rule = CrossAgentConsistency()
        past = self._make_hashed("EXECUTION_COMPLETE", "approved success", "t1", "intent-A")
        event = self._make_hashed("EXECUTION_COMPLETE", "rejected failure", "t2", "intent-B")
        assert rule.check(event, [past]) is None

    def test_no_alert_same_task(self):
        rule = CrossAgentConsistency()
        past = self._make_hashed("EXECUTION_COMPLETE", "approved success", "t1")
        event = self._make_hashed("EXECUTION_COMPLETE", "rejected failure", "t1")
        assert rule.check(event, [past]) is None


# ─── Make Agent Drift Rules Tests ─────────────────────────

class TestMakeAgentDriftRules:
    def test_creates_two_rules(self):
        rules = make_agent_drift_rules()
        assert len(rules) == 2
        assert isinstance(rules[0], AgentCompetencyDrift)
        assert isinstance(rules[1], CrossAgentConsistency)

    def test_shared_tracker(self):
        tracker = AgentDriftTracker()
        rules = make_agent_drift_rules(tracker)
        assert rules[0]._tracker is tracker


# ─── Watchdog Integration Tests ───────────────────────────

class TestWatchdogAgentDrift:
    def test_watchdog_without_drift(self):
        wd = WatchdogAgent()
        assert wd.drift_tracker is None
        assert len(wd.rules) == 6  # DEFAULT_RULES (3 original + 3 tool rules)

    def test_watchdog_with_drift(self):
        wd = WatchdogAgent(enable_agent_drift=True)
        assert wd.drift_tracker is not None
        assert len(wd.rules) == 8  # 6 default + 2 drift

    def test_drift_tracker_accessible(self):
        wd = WatchdogAgent(enable_agent_drift=True)
        tracker = wd.drift_tracker
        tracker.record("agent-1", "t1", prm_score=0.7)
        metrics = tracker.get_metrics("agent-1")
        assert metrics.total_executions == 1
