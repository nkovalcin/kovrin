"""Tests for the LATTICE Watchdog Agent.

Covers temporal rules, graduated containment, subscribe/unsubscribe,
and watchdog lifecycle (start/stop).
"""

import asyncio

import pytest

from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.models import ContainmentLevel, RiskLevel, Trace, WatchdogAlert
from kovrin.safety.watchdog import (
    DEFAULT_RULES,
    ExcessiveFailureRate,
    NoExecutionAfterRejection,
    UnexpectedEventSequence,
    WatchdogAgent,
)


# ─── Helper ──────────────────────────────────────────────────

def make_hashed(trace: Trace, seq: int = 0) -> HashedTrace:
    """Create a HashedTrace for testing (hash values don't matter here)."""
    return HashedTrace(
        trace=trace,
        hash=f"fakehash_{seq}",
        previous_hash=f"fakehash_{seq - 1}" if seq > 0 else "GENESIS",
        sequence=seq,
    )


# ─── NoExecutionAfterRejection ──────────────────────────────

class TestNoExecutionAfterRejection:
    def test_triggers_on_exec_after_l0_rejection(self):
        rule = NoExecutionAfterRejection()

        rejection = make_hashed(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="L0_CHECK",
            l0_passed=False,
        ), seq=0)

        exec_event = make_hashed(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="EXECUTION_START",
        ), seq=1)

        alert = rule.check(exec_event, [rejection])
        assert alert is not None
        assert alert.severity == ContainmentLevel.KILL
        assert "task-1" in alert.reason

    def test_no_trigger_for_different_task(self):
        rule = NoExecutionAfterRejection()

        rejection = make_hashed(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="L0_CHECK",
            l0_passed=False,
        ), seq=0)

        exec_event = make_hashed(Trace(
            task_id="task-2",
            intent_id="intent-1",
            event_type="EXECUTION_START",
        ), seq=1)

        alert = rule.check(exec_event, [rejection])
        assert alert is None

    def test_no_trigger_for_passed_l0(self):
        rule = NoExecutionAfterRejection()

        passed = make_hashed(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="L0_CHECK",
            l0_passed=True,
        ), seq=0)

        exec_event = make_hashed(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="EXECUTION_START",
        ), seq=1)

        alert = rule.check(exec_event, [passed])
        assert alert is None

    def test_ignores_non_execution_events(self):
        rule = NoExecutionAfterRejection()

        rejection = make_hashed(Trace(
            task_id="task-1",
            event_type="L0_CHECK",
            l0_passed=False,
        ), seq=0)

        other = make_hashed(Trace(
            task_id="task-1",
            event_type="DECOMPOSITION",
        ), seq=1)

        assert rule.check(other, [rejection]) is None


# ─── ExcessiveFailureRate ────────────────────────────────────

class TestExcessiveFailureRate:
    def test_triggers_when_failure_rate_exceeds_threshold(self):
        rule = ExcessiveFailureRate(threshold=0.5)

        history = [
            make_hashed(Trace(event_type="CRITIC_PIPELINE", l0_passed=False), seq=0),
            make_hashed(Trace(event_type="CRITIC_PIPELINE", l0_passed=False), seq=1),
            make_hashed(Trace(event_type="EXECUTION_COMPLETE"), seq=2),
        ]

        trigger = make_hashed(Trace(
            event_type="EXECUTION_COMPLETE",
            intent_id="intent-1",
        ), seq=3)

        alert = rule.check(trigger, history)
        assert alert is not None
        assert alert.severity == ContainmentLevel.PAUSE
        assert "exceeds threshold" in alert.reason

    def test_no_trigger_below_threshold(self):
        rule = ExcessiveFailureRate(threshold=0.5)

        history = [
            make_hashed(Trace(event_type="EXECUTION_COMPLETE"), seq=0),
            make_hashed(Trace(event_type="EXECUTION_COMPLETE"), seq=1),
            make_hashed(Trace(event_type="EXECUTION_COMPLETE"), seq=2),
        ]

        trigger = make_hashed(Trace(event_type="EXECUTION_COMPLETE"), seq=3)
        assert rule.check(trigger, history) is None

    def test_no_trigger_with_too_few_events(self):
        rule = ExcessiveFailureRate(threshold=0.5)

        history = [
            make_hashed(Trace(event_type="CRITIC_PIPELINE", l0_passed=False), seq=0),
        ]

        trigger = make_hashed(Trace(event_type="EXECUTION_COMPLETE"), seq=1)
        assert rule.check(trigger, history) is None


# ─── UnexpectedEventSequence ────────────────────────────────

class TestUnexpectedEventSequence:
    def test_triggers_complete_without_start(self):
        rule = UnexpectedEventSequence()

        history = [
            make_hashed(Trace(task_id="task-other", event_type="EXECUTION_START"), seq=0),
        ]

        event = make_hashed(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="EXECUTION_COMPLETE",
        ), seq=1)

        alert = rule.check(event, history)
        assert alert is not None
        assert alert.severity == ContainmentLevel.WARN
        assert "task-1" in alert.reason

    def test_no_trigger_when_start_exists(self):
        rule = UnexpectedEventSequence()

        history = [
            make_hashed(Trace(task_id="task-1", event_type="EXECUTION_START"), seq=0),
        ]

        event = make_hashed(Trace(
            task_id="task-1",
            event_type="EXECUTION_COMPLETE",
        ), seq=1)

        assert rule.check(event, history) is None

    def test_no_trigger_for_non_complete_events(self):
        rule = UnexpectedEventSequence()
        history = [make_hashed(Trace(event_type="SOMETHING"), seq=0)]
        event = make_hashed(Trace(event_type="EXECUTION_START"), seq=1)
        assert rule.check(event, history) is None


# ─── WatchdogAgent ───────────────────────────────────────────

class TestWatchdogAgent:
    def test_initial_state(self):
        wd = WatchdogAgent()
        assert not wd.is_paused
        assert not wd.is_killed
        assert len(wd.alerts) == 0

    async def test_start_subscribes_to_trace_log(self):
        trace_log = ImmutableTraceLog()
        wd = WatchdogAgent()
        await wd.start(trace_log, "test intent")
        assert len(trace_log._subscribers) == 1
        await wd.stop()
        assert len(trace_log._subscribers) == 0

    async def test_kill_on_exec_after_rejection(self):
        trace_log = ImmutableTraceLog()
        wd = WatchdogAgent()
        await wd.start(trace_log, "test")

        # L0 rejection
        await trace_log.append_async(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="L0_CHECK",
            l0_passed=False,
        ))

        # Attempt execution of rejected task → should trigger KILL
        await trace_log.append_async(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="EXECUTION_START",
        ))

        assert wd.is_killed
        assert len(wd.alerts) >= 1
        assert any(a.severity == ContainmentLevel.KILL for a in wd.alerts)

        await wd.stop()

    async def test_pause_on_excessive_failures(self):
        trace_log = ImmutableTraceLog()
        wd = WatchdogAgent()
        await wd.start(trace_log, "test")

        # Generate failures (L0 rejections via CRITIC_PIPELINE)
        for i in range(3):
            await trace_log.append_async(Trace(
                task_id=f"task-{i}",
                intent_id="intent-1",
                event_type="CRITIC_PIPELINE",
                l0_passed=False,
            ))

        # One success
        await trace_log.append_async(Trace(
            task_id="task-ok",
            intent_id="intent-1",
            event_type="EXECUTION_COMPLETE",
        ))

        assert wd.is_paused
        assert any(a.severity == ContainmentLevel.PAUSE for a in wd.alerts)

        # Resume
        wd.resume()
        assert not wd.is_paused

        await wd.stop()

    async def test_warn_on_unexpected_sequence(self):
        trace_log = ImmutableTraceLog()
        wd = WatchdogAgent()
        await wd.start(trace_log, "test")

        # Something to make history non-empty
        await trace_log.append_async(Trace(
            task_id="task-other",
            event_type="DECOMPOSITION",
        ))

        # Complete without start
        await trace_log.append_async(Trace(
            task_id="task-1",
            intent_id="intent-1",
            event_type="EXECUTION_COMPLETE",
        ))

        assert not wd.is_paused
        assert not wd.is_killed
        assert any(a.severity == ContainmentLevel.WARN for a in wd.alerts)

        await wd.stop()

    async def test_clean_execution_no_alerts(self):
        trace_log = ImmutableTraceLog()
        wd = WatchdogAgent()
        await wd.start(trace_log, "test")

        await trace_log.append_async(Trace(event_type="INTENT_RECEIVED"))
        await trace_log.append_async(Trace(event_type="DECOMPOSITION"))
        await trace_log.append_async(Trace(task_id="t1", event_type="EXECUTION_START"))
        await trace_log.append_async(Trace(task_id="t1", event_type="EXECUTION_COMPLETE"))

        assert not wd.is_paused
        assert not wd.is_killed
        assert len(wd.alerts) == 0

        await wd.stop()

    async def test_wait_if_paused_blocks(self):
        wd = WatchdogAgent()
        wd._pause_event.clear()  # Simulate pause

        # Should not complete quickly
        done = False

        async def waiter():
            nonlocal done
            await wd.wait_if_paused()
            done = True

        task = asyncio.create_task(waiter())
        await asyncio.sleep(0.05)
        assert not done

        # Resume
        wd.resume()
        await asyncio.sleep(0.05)
        assert done

        task.cancel()

    async def test_killed_watchdog_stops_processing(self):
        trace_log = ImmutableTraceLog()
        wd = WatchdogAgent()
        await wd.start(trace_log, "test")
        wd._killed = True

        # No alerts should be generated
        await trace_log.append_async(Trace(
            task_id="task-1",
            event_type="EXECUTION_COMPLETE",
        ))

        assert len(wd.alerts) == 0
        await wd.stop()


# ─── Trace Log Subscribe ─────────────────────────────────────

class TestTraceLogSubscribe:
    async def test_subscribe_receives_events(self):
        log = ImmutableTraceLog()
        received = []

        async def cb(hashed: HashedTrace):
            received.append(hashed)

        log.subscribe(cb)
        await log.append_async(Trace(event_type="TEST"))
        assert len(received) == 1
        assert received[0].trace.event_type == "TEST"

    async def test_unsubscribe_stops_events(self):
        log = ImmutableTraceLog()
        received = []

        async def cb(hashed: HashedTrace):
            received.append(hashed)

        log.subscribe(cb)
        await log.append_async(Trace(event_type="TEST1"))
        log.unsubscribe(cb)
        await log.append_async(Trace(event_type="TEST2"))
        assert len(received) == 1

    async def test_sync_append_does_not_notify(self):
        log = ImmutableTraceLog()
        received = []

        async def cb(hashed: HashedTrace):
            received.append(hashed)

        log.subscribe(cb)
        log.append(Trace(event_type="TEST"))
        assert len(received) == 0

    async def test_subscriber_error_does_not_break_log(self):
        log = ImmutableTraceLog()

        async def bad_cb(hashed: HashedTrace):
            raise RuntimeError("subscriber crash")

        log.subscribe(bad_cb)
        # Should not raise
        await log.append_async(Trace(event_type="TEST"))
        assert len(log) == 1


# ─── Default Rules ────────────────────────────────────────────

class TestDefaultRules:
    def test_default_rules_exist(self):
        assert len(DEFAULT_RULES) == 3

    def test_default_rule_types(self):
        types = {type(r) for r in DEFAULT_RULES}
        assert NoExecutionAfterRejection in types
        assert ExcessiveFailureRate in types
        assert UnexpectedEventSequence in types
