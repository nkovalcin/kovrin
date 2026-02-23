"""
Kovrin Watchdog Agent

Independent runtime monitor that observes execution in real-time
and can intervene when agents deviate from the original intent.

Features:
- Temporal rule engine: detects forbidden event sequences
- Drift detection: compares execution against original intent via Claude API
- Graduated containment: WARN -> PAUSE -> KILL
- Runs as independent asyncio task alongside execution

The watchdog subscribes to the trace log and evaluates every new
event against its rule set. It operates independently of the
executor — it cannot be disabled by agents.
"""

import asyncio
import time
from collections import defaultdict

import anthropic

from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.models import AgentDriftMetrics, ContainmentLevel, DriftLevel, Trace, WatchdogAlert


class TemporalRule:
    """A rule that checks sequences of trace events."""

    def __init__(self, name: str, description: str, severity: ContainmentLevel):
        self.name = name
        self.description = description
        self.severity = severity

    def check(self, event: HashedTrace, history: list[HashedTrace]) -> WatchdogAlert | None:
        """Check if this rule is violated. Override in subclasses."""
        raise NotImplementedError


class NoExecutionAfterRejection(TemporalRule):
    """After a task is REJECTED_BY_L0, no EXECUTION may follow for the same task_id."""

    def __init__(self):
        super().__init__(
            name="no_exec_after_rejection",
            description="Execution must not follow L0 rejection for the same task",
            severity=ContainmentLevel.KILL,
        )

    def check(self, event: HashedTrace, history: list[HashedTrace]) -> WatchdogAlert | None:
        if event.trace.event_type != "EXECUTION_START":
            return None

        # Check if this task_id was previously rejected
        for past in history:
            if (
                past.trace.task_id == event.trace.task_id
                and past.trace.event_type == "L0_CHECK"
                and past.trace.l0_passed is False
            ):
                return WatchdogAlert(
                    severity=self.severity,
                    reason=f"Task {event.trace.task_id} was rejected by L0 but execution was attempted",
                    task_id=event.trace.task_id,
                    intent_id=event.trace.intent_id,
                    rule=self.name,
                )
        return None


class ExcessiveFailureRate(TemporalRule):
    """If more than 50% of tasks fail, something is wrong."""

    def __init__(self, threshold: float = 0.5):
        super().__init__(
            name="excessive_failure_rate",
            description=f"Failure rate exceeds {threshold*100}%",
            severity=ContainmentLevel.PAUSE,
        )
        self.threshold = threshold

    def check(self, event: HashedTrace, history: list[HashedTrace]) -> WatchdogAlert | None:
        if event.trace.event_type not in ("EXECUTION_COMPLETE", "EXECUTION_START"):
            return None

        completed = sum(1 for h in history if h.trace.event_type == "EXECUTION_COMPLETE")
        failed = sum(
            1 for h in history
            if h.trace.event_type in ("HUMAN_REJECTED",)
            or (h.trace.event_type == "CRITIC_PIPELINE" and h.trace.l0_passed is False)
        )

        total = completed + failed
        if total >= 3 and failed / total > self.threshold:
            return WatchdogAlert(
                severity=self.severity,
                reason=f"Failure rate {failed}/{total} ({failed/total:.0%}) exceeds threshold {self.threshold:.0%}",
                intent_id=event.trace.intent_id,
                rule=self.name,
            )
        return None


class UnexpectedEventSequence(TemporalRule):
    """Detects suspicious event patterns."""

    def __init__(self):
        super().__init__(
            name="unexpected_sequence",
            description="Unexpected event sequence detected",
            severity=ContainmentLevel.WARN,
        )

    def check(self, event: HashedTrace, history: list[HashedTrace]) -> WatchdogAlert | None:
        if not history:
            return None

        # Rule: EXECUTION_COMPLETE without prior EXECUTION_START for same task
        if event.trace.event_type == "EXECUTION_COMPLETE":
            has_start = any(
                h.trace.task_id == event.trace.task_id
                and h.trace.event_type == "EXECUTION_START"
                for h in history
            )
            if not has_start:
                return WatchdogAlert(
                    severity=self.severity,
                    reason=f"EXECUTION_COMPLETE without prior EXECUTION_START for task {event.trace.task_id}",
                    task_id=event.trace.task_id,
                    intent_id=event.trace.intent_id,
                    rule=self.name,
                )
        return None


# Default rule set
DEFAULT_RULES: list[TemporalRule] = [
    NoExecutionAfterRejection(),
    ExcessiveFailureRate(),
    UnexpectedEventSequence(),
]


# ─── Phase 6: Agent Drift Detection ──────────────────────


class AgentDriftTracker:
    """Tracks per-agent execution history for drift detection.

    Maintains a sliding window of PRM scores and success/failure
    counts per agent. Used by the drift rules to determine if an
    agent's performance is degrading.
    """

    def __init__(self, window_size: int = 20):
        self._window_size = window_size
        self._data: dict[str, dict] = {}  # agent_name -> tracking data

    def record(
        self,
        agent_name: str,
        task_id: str,
        prm_score: float | None = None,
        success: bool = True,
    ) -> None:
        """Record an execution result for an agent."""
        if agent_name not in self._data:
            self._data[agent_name] = {
                "total": 0,
                "successes": 0,
                "prm_scores": [],
            }

        data = self._data[agent_name]
        data["total"] += 1
        if success:
            data["successes"] += 1
        if prm_score is not None:
            data["prm_scores"].append(prm_score)
            # Sliding window
            if len(data["prm_scores"]) > self._window_size:
                data["prm_scores"] = data["prm_scores"][-self._window_size:]

    def get_metrics(self, agent_name: str) -> AgentDriftMetrics:
        """Get drift metrics for a specific agent."""
        data = self._data.get(agent_name)
        if not data:
            return AgentDriftMetrics(agent_name=agent_name)

        total = data["total"]
        successes = data["successes"]
        scores = data["prm_scores"]
        avg_score = sum(scores) / len(scores) if scores else 0.0
        success_rate = successes / total if total > 0 else 1.0

        drift_level = self._compute_drift_level(avg_score, success_rate, len(scores))

        return AgentDriftMetrics(
            agent_name=agent_name,
            total_executions=total,
            recent_prm_scores=list(scores),
            average_prm_score=round(avg_score, 4),
            success_rate=round(success_rate, 4),
            drift_level=drift_level,
        )

    def get_all_metrics(self) -> list[AgentDriftMetrics]:
        """Get drift metrics for all tracked agents."""
        return [self.get_metrics(name) for name in self._data]

    @staticmethod
    def _compute_drift_level(avg_score: float, success_rate: float, sample_size: int) -> DriftLevel:
        """Determine drift level from metrics."""
        if sample_size < 3:
            return DriftLevel.NONE
        if avg_score < 0.2 and success_rate < 0.3:
            return DriftLevel.CRITICAL
        if avg_score < 0.35 or success_rate < 0.5:
            return DriftLevel.HIGH
        if avg_score < 0.5:
            return DriftLevel.MODERATE
        if avg_score < 0.65:
            return DriftLevel.LOW
        return DriftLevel.NONE


class AgentCompetencyDrift(TemporalRule):
    """Monitors per-agent PRM scores and triggers graduated containment.

    Checks PRM_EVALUATION events and uses the AgentDriftTracker to
    determine if an agent is drifting:
    - WARN: average PRM < 0.5
    - PAUSE: average PRM < 0.35 or success rate < 50%
    - KILL: average PRM < 0.2 and success rate < 30%
    """

    def __init__(self, tracker: AgentDriftTracker):
        super().__init__(
            name="agent_competency_drift",
            description="Agent performance degradation detected via PRM scores",
            severity=ContainmentLevel.WARN,  # Base severity, overridden per-check
        )
        self._tracker = tracker

    def check(self, event: HashedTrace, history: list[HashedTrace]) -> WatchdogAlert | None:
        if event.trace.event_type != "PRM_EVALUATION":
            return None

        details = event.trace.details or {}
        agent_name = details.get("agent_name", "")
        score = details.get("aggregate_score", 0.5)

        if not agent_name:
            return None

        # Record in tracker
        self._tracker.record(agent_name, event.trace.task_id, prm_score=score)

        # Evaluate metrics
        metrics = self._tracker.get_metrics(agent_name)

        if metrics.drift_level == DriftLevel.CRITICAL:
            return WatchdogAlert(
                severity=ContainmentLevel.KILL,
                reason=f"Agent '{agent_name}' critically drifted: avg_prm={metrics.average_prm_score:.2f}, success_rate={metrics.success_rate:.0%}",
                task_id=event.trace.task_id,
                intent_id=event.trace.intent_id,
                rule=self.name,
            )
        elif metrics.drift_level == DriftLevel.HIGH:
            return WatchdogAlert(
                severity=ContainmentLevel.PAUSE,
                reason=f"Agent '{agent_name}' high drift: avg_prm={metrics.average_prm_score:.2f}, success_rate={metrics.success_rate:.0%}",
                task_id=event.trace.task_id,
                intent_id=event.trace.intent_id,
                rule=self.name,
            )
        elif metrics.drift_level == DriftLevel.MODERATE:
            return WatchdogAlert(
                severity=ContainmentLevel.WARN,
                reason=f"Agent '{agent_name}' moderate drift: avg_prm={metrics.average_prm_score:.2f}",
                task_id=event.trace.task_id,
                intent_id=event.trace.intent_id,
                rule=self.name,
            )
        return None


class CrossAgentConsistency(TemporalRule):
    """Detects contradictory outputs from different agents in the same intent.

    Lightweight heuristic: checks for opposing sentiment keywords
    in EXECUTION_COMPLETE events from the same intent.
    """

    _POSITIVE = {"success", "approved", "valid", "correct", "feasible", "recommended", "agree"}
    _NEGATIVE = {"failure", "rejected", "invalid", "incorrect", "infeasible", "not recommended", "disagree"}

    def __init__(self):
        super().__init__(
            name="cross_agent_consistency",
            description="Contradictory outputs detected between agents in the same intent",
            severity=ContainmentLevel.WARN,
        )

    def check(self, event: HashedTrace, history: list[HashedTrace]) -> WatchdogAlert | None:
        if event.trace.event_type != "EXECUTION_COMPLETE":
            return None

        current_desc = (event.trace.description or "").lower()
        current_sentiment = self._sentiment(current_desc)
        if current_sentiment == 0:
            return None

        # Check against other completed tasks in the same intent
        for past in history:
            if (
                past.trace.event_type == "EXECUTION_COMPLETE"
                and past.trace.intent_id == event.trace.intent_id
                and past.trace.task_id != event.trace.task_id
            ):
                past_desc = (past.trace.description or "").lower()
                past_sentiment = self._sentiment(past_desc)
                # Opposite sentiments on the same topic
                if past_sentiment != 0 and past_sentiment != current_sentiment:
                    return WatchdogAlert(
                        severity=self.severity,
                        reason=f"Contradictory outputs: task {event.trace.task_id} vs {past.trace.task_id}",
                        task_id=event.trace.task_id,
                        intent_id=event.trace.intent_id,
                        rule=self.name,
                    )
        return None

    def _sentiment(self, text: str) -> int:
        """Simple keyword-based sentiment: +1 positive, -1 negative, 0 neutral."""
        pos = sum(1 for w in self._POSITIVE if w in text)
        neg = sum(1 for w in self._NEGATIVE if w in text)
        if pos > neg:
            return 1
        if neg > pos:
            return -1
        return 0


# Agent drift rules (opt-in, not included in DEFAULT_RULES)
def make_agent_drift_rules(tracker: AgentDriftTracker | None = None) -> list[TemporalRule]:
    """Create agent drift detection rules with a shared tracker."""
    tracker = tracker or AgentDriftTracker()
    return [
        AgentCompetencyDrift(tracker),
        CrossAgentConsistency(),
    ]


class WatchdogAgent:
    """Independent runtime monitor for Kovrin execution.

    Subscribes to the trace log and evaluates every event against
    temporal rules and drift detection. Can WARN, PAUSE, or KILL
    the pipeline.
    """

    def __init__(
        self,
        rules: list[TemporalRule] | None = None,
        enable_drift_detection: bool = False,
        client: anthropic.AsyncAnthropic | None = None,
        enable_agent_drift: bool = False,
    ):
        base_rules = rules or list(DEFAULT_RULES)
        if enable_agent_drift:
            self._drift_tracker = AgentDriftTracker()
            base_rules = base_rules + make_agent_drift_rules(self._drift_tracker)
        else:
            self._drift_tracker = None
        self.rules = base_rules
        self.enable_drift_detection = enable_drift_detection
        self._client = client
        self.alerts: list[WatchdogAlert] = []
        self._pause_event = asyncio.Event()
        self._pause_event.set()  # Not paused initially
        self._killed = False
        self._intent_context: str = ""
        self._trace_log: ImmutableTraceLog | None = None
        self._history: list[HashedTrace] = []
        self._callback = self._on_event  # Stable reference for subscribe/unsubscribe
        self._last_drift_check: float = 0.0  # Rate limiting
        self._drift_check_interval: float = 5.0  # Min seconds between drift checks

    @property
    def drift_tracker(self) -> AgentDriftTracker | None:
        return self._drift_tracker

    @property
    def is_paused(self) -> bool:
        return not self._pause_event.is_set()

    @property
    def is_killed(self) -> bool:
        return self._killed

    async def wait_if_paused(self) -> None:
        """Block until unpaused. Call this in the executor before each task."""
        await self._pause_event.wait()

    def resume(self) -> None:
        """Resume execution after a PAUSE."""
        self._pause_event.set()

    async def start(self, trace_log: ImmutableTraceLog, intent_context: str = "") -> None:
        """Start monitoring the trace log."""
        self._trace_log = trace_log
        self._intent_context = intent_context
        trace_log.subscribe(self._callback)

    async def stop(self) -> None:
        """Stop monitoring."""
        if self._trace_log is not None:
            self._trace_log.unsubscribe(self._callback)

    async def _on_event(self, hashed: HashedTrace) -> None:
        """Process a new trace event."""
        if self._killed:
            return

        # Check all temporal rules
        for rule in self.rules:
            alert = rule.check(hashed, self._history)
            if alert:
                self.alerts.append(alert)
                await self._handle_alert(alert)

        # Check drift detection on EXECUTION_COMPLETE events
        if (
            self.enable_drift_detection
            and self._client
            and hashed.trace.event_type == "EXECUTION_COMPLETE"
        ):
            now = time.monotonic()
            if now - self._last_drift_check >= self._drift_check_interval:
                self._last_drift_check = now
                drift_alert = await self._check_drift(hashed)
                if drift_alert:
                    self.alerts.append(drift_alert)
                    await self._handle_alert(drift_alert)

        self._history.append(hashed)

    async def _check_drift(self, event: HashedTrace) -> WatchdogAlert | None:
        """Check if a completed task's result aligns with the original intent.

        Uses Claude API to assess alignment. Returns a WatchdogAlert if drift
        is detected, None otherwise.

        Verdicts:
        - ALIGNED: Task result matches the intent. No alert.
        - DRIFTED: Task result diverges from intent. PAUSE alert.
        - UNCERTAIN: Cannot determine alignment. WARN alert.
        """
        task_desc = event.trace.description
        details = event.trace.details or {}
        output_length = details.get("output_length", "unknown")

        prompt = f"""You are a drift detection system for an AI orchestration framework.

ORIGINAL INTENT: {self._intent_context}

COMPLETED TASK: {task_desc}
OUTPUT LENGTH: {output_length} characters

Based on the original intent, does this completed task align with what was requested?

Answer with exactly one word on the first line: ALIGNED, DRIFTED, or UNCERTAIN
Then provide a brief reason on the second line."""

        try:
            response = await self._client.messages.create(
                model="claude-sonnet-4-20250514",
                max_tokens=100,
                messages=[{"role": "user", "content": prompt}],
            )
            answer = response.content[0].text.strip()
            lines = answer.split("\n", 1)
            verdict = lines[0].strip().upper()
            reason = lines[1].strip() if len(lines) > 1 else ""

            if verdict == "DRIFTED":
                return WatchdogAlert(
                    severity=ContainmentLevel.PAUSE,
                    reason=f"Drift detected: {reason or 'Task diverged from intent'}",
                    task_id=event.trace.task_id,
                    intent_id=event.trace.intent_id,
                    rule="drift_detection",
                )
            elif verdict == "UNCERTAIN":
                return WatchdogAlert(
                    severity=ContainmentLevel.WARN,
                    reason=f"Drift uncertain: {reason or 'Cannot determine alignment'}",
                    task_id=event.trace.task_id,
                    intent_id=event.trace.intent_id,
                    rule="drift_detection",
                )
            # ALIGNED -> no alert
            return None
        except Exception:
            # API errors should not break execution
            return None

    async def _handle_alert(self, alert: WatchdogAlert) -> None:
        """Execute containment action based on alert severity."""
        if alert.severity == ContainmentLevel.WARN:
            # Log warning, continue execution
            pass
        elif alert.severity == ContainmentLevel.PAUSE:
            self._pause_event.clear()  # Block executor
        elif alert.severity == ContainmentLevel.KILL:
            self._killed = True
            self._pause_event.clear()

        # Log the alert as a trace event
        if self._trace_log:
            self._trace_log.append(Trace(
                intent_id=alert.intent_id,
                task_id=alert.task_id,
                event_type=f"WATCHDOG_{alert.severity.value}",
                description=f"Watchdog {alert.severity.value}: {alert.reason}",
                details={
                    "rule": alert.rule,
                    "severity": alert.severity.value,
                    "alert_id": alert.id,
                },
            ))
