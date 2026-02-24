"""Tests for LATTICE Speculative Execution Engine."""

import pytest

from kovrin.core.models import (
    SpeculationTier,
    SubTask,
    TaskStatus,
)
from kovrin.engine.speculation import (
    Checkpoint,
    SpeculativeContext,
    SpeculativeExecutor,
)


class TestCheckpoint:
    def test_default_values(self):
        cp = Checkpoint(task_id="t-1")
        assert cp.task_id == "t-1"
        assert cp.task_snapshot == {}
        assert cp.result is None
        assert cp.committed is False
        assert cp.rolled_back is False


class TestSpeculativeContext:
    def test_checkpoint_creates_snapshot(self):
        ctx = SpeculativeContext()
        task = SubTask(id="t-1", description="Test task")
        cp = ctx.checkpoint(task)
        assert cp.task_id == "t-1"
        assert cp.task_snapshot["description"] == "Test task"
        assert cp.task_snapshot["status"] == "PENDING"

    def test_checkpoint_emits_trace(self):
        ctx = SpeculativeContext()
        task = SubTask(id="t-1", description="Test task", parent_intent_id="i-1")
        ctx.checkpoint(task)
        assert len(ctx.traces) == 1
        assert ctx.traces[0].event_type == "SPECULATION_CHECKPOINT"
        assert ctx.traces[0].intent_id == "i-1"

    def test_commit(self):
        ctx = SpeculativeContext()
        task = SubTask(id="t-1", description="Test task")
        cp = ctx.checkpoint(task)
        cp.result = "some result"
        ctx.commit(cp)
        assert cp.committed is True
        assert len(ctx.traces) == 2
        assert ctx.traces[1].event_type == "SPECULATION_COMMIT"

    def test_rollback_restores_state(self):
        ctx = SpeculativeContext()
        task = SubTask(id="t-1", description="Test task")
        cp = ctx.checkpoint(task)

        # Modify task state
        task.status = TaskStatus.EXECUTING
        task.output = "partial result"

        ctx.rollback(cp, task)
        assert cp.rolled_back is True
        assert task.status == TaskStatus.PENDING
        assert task.output is None
        assert len(ctx.traces) == 2
        assert ctx.traces[1].event_type == "SPECULATION_ROLLBACK"

    def test_get_checkpoint(self):
        ctx = SpeculativeContext()
        task = SubTask(id="t-1", description="Test task")
        ctx.checkpoint(task)
        assert ctx.get_checkpoint("t-1") is not None
        assert ctx.get_checkpoint("nonexistent") is None

    def test_multiple_checkpoints(self):
        ctx = SpeculativeContext()
        t1 = SubTask(id="t-1", description="Task 1")
        t2 = SubTask(id="t-2", description="Task 2")
        cp1 = ctx.checkpoint(t1)
        cp2 = ctx.checkpoint(t2)
        ctx.commit(cp1)
        ctx.rollback(cp2, t2)
        assert cp1.committed is True
        assert cp2.rolled_back is True
        # 2 checkpoint + 1 commit + 1 rollback = 4
        assert len(ctx.traces) == 4


class TestSpeculativeExecutor:
    @pytest.mark.asyncio
    async def test_free_passthrough(self):
        executor = SpeculativeExecutor()
        task = SubTask(id="t-1", description="Free task", speculation_tier=SpeculationTier.FREE)

        async def execute_fn(t, deps):
            return "result"

        result = await executor.execute(task, execute_fn, {})
        assert result == "result"
        # No traces for FREE tier
        assert len(executor.context.traces) == 0

    @pytest.mark.asyncio
    async def test_guarded_checkpoint_and_commit(self):
        executor = SpeculativeExecutor()
        task = SubTask(
            id="t-1", description="Guarded task", speculation_tier=SpeculationTier.GUARDED
        )

        async def execute_fn(t, deps):
            return "guarded result"

        result = await executor.execute(task, execute_fn, {})
        assert result == "guarded result"
        # checkpoint + commit = 2 traces
        assert len(executor.context.traces) == 2
        assert executor.context.traces[0].event_type == "SPECULATION_CHECKPOINT"
        assert executor.context.traces[1].event_type == "SPECULATION_COMMIT"

    @pytest.mark.asyncio
    async def test_guarded_rollback_on_validation_failure(self):
        executor = SpeculativeExecutor()
        task = SubTask(
            id="t-1", description="Guarded task", speculation_tier=SpeculationTier.GUARDED
        )

        async def execute_fn(t, deps):
            return "bad result"

        async def validate_fn(result):
            return False  # Reject

        with pytest.raises(RuntimeError, match="rejected by validator"):
            await executor.execute(task, execute_fn, {}, validate_fn=validate_fn)

        # checkpoint + rollback
        assert len(executor.context.traces) == 2
        assert executor.context.traces[1].event_type == "SPECULATION_ROLLBACK"

    @pytest.mark.asyncio
    async def test_guarded_rollback_on_exception(self):
        executor = SpeculativeExecutor()
        task = SubTask(
            id="t-1", description="Guarded task", speculation_tier=SpeculationTier.GUARDED
        )

        async def execute_fn(t, deps):
            raise ValueError("Something went wrong")

        with pytest.raises(ValueError, match="Something went wrong"):
            await executor.execute(task, execute_fn, {})

        assert len(executor.context.traces) == 2
        assert executor.context.traces[1].event_type == "SPECULATION_ROLLBACK"

    @pytest.mark.asyncio
    async def test_none_tier_passthrough(self):
        executor = SpeculativeExecutor()
        task = SubTask(id="t-1", description="None task", speculation_tier=SpeculationTier.NONE)

        async def execute_fn(t, deps):
            return "approved result"

        result = await executor.execute(task, execute_fn, {})
        assert result == "approved result"
        assert len(executor.context.traces) == 0
