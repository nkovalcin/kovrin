"""
Kovrin Speculative Execution Engine

Manages checkpoint/rollback for GUARDED speculation tier tasks.
Provides a SpeculativeContext that wraps task execution with
state snapshots.

Tiers:
- FREE: Execute immediately, results are final
- GUARDED: Execute with checkpoint, can rollback
- NONE: Block until human approval (handled by RiskRouter upstream)
"""

from dataclasses import dataclass, field

from kovrin.core.models import (
    SpeculationTier,
    SubTask,
    TaskStatus,
    Trace,
)


@dataclass
class Checkpoint:
    """A snapshot of task state before speculative execution."""
    task_id: str
    task_snapshot: dict = field(default_factory=dict)
    result: str | None = None
    committed: bool = False
    rolled_back: bool = False


class SpeculativeContext:
    """Manages speculative execution with checkpoint/rollback.

    Usage:
        ctx = SpeculativeContext()
        cp = ctx.checkpoint(subtask)
        try:
            result = await execute(subtask)
            cp.result = result
            if validate(result):
                ctx.commit(cp)
            else:
                ctx.rollback(cp, subtask)
        except Exception:
            ctx.rollback(cp, subtask)
    """

    def __init__(self):
        self._checkpoints: dict[str, Checkpoint] = {}
        self._traces: list[Trace] = []

    def checkpoint(self, subtask: SubTask) -> Checkpoint:
        """Create a checkpoint before speculative execution."""
        cp = Checkpoint(
            task_id=subtask.id,
            task_snapshot=subtask.model_dump(),
        )
        self._checkpoints[subtask.id] = cp
        self._traces.append(Trace(
            intent_id=subtask.parent_intent_id or "",
            task_id=subtask.id,
            event_type="SPECULATION_CHECKPOINT",
            description=f"Checkpoint created for GUARDED task: {subtask.description[:60]}",
        ))
        return cp

    def commit(self, checkpoint: Checkpoint) -> None:
        """Commit a speculative execution (result is accepted)."""
        checkpoint.committed = True
        self._traces.append(Trace(
            intent_id="",
            task_id=checkpoint.task_id,
            event_type="SPECULATION_COMMIT",
            description=f"Speculative result committed for task {checkpoint.task_id}",
        ))

    def rollback(self, checkpoint: Checkpoint, subtask: SubTask) -> None:
        """Rollback a speculative execution (restore task state)."""
        checkpoint.rolled_back = True
        snapshot = checkpoint.task_snapshot
        subtask.status = TaskStatus(snapshot.get("status", "PENDING"))
        subtask.output = snapshot.get("output")
        self._traces.append(Trace(
            intent_id=subtask.parent_intent_id or "",
            task_id=checkpoint.task_id,
            event_type="SPECULATION_ROLLBACK",
            description=f"Speculative result rolled back for task {checkpoint.task_id}",
        ))

    @property
    def traces(self) -> list[Trace]:
        return list(self._traces)

    def get_checkpoint(self, task_id: str) -> Checkpoint | None:
        return self._checkpoints.get(task_id)


class SpeculativeExecutor:
    """Wraps task execution with speculation-tier-aware behavior.

    - FREE: Pass through directly
    - GUARDED: Checkpoint, execute, validate, commit or rollback
    - NONE: Pass through (pre-approved by RiskRouter upstream)
    """

    def __init__(self, context: SpeculativeContext | None = None):
        self.context = context or SpeculativeContext()

    async def execute(
        self,
        subtask: SubTask,
        execute_fn,
        dep_results: dict[str, str],
        validate_fn=None,
    ) -> str:
        """Execute with speculation-tier-appropriate behavior.

        Args:
            subtask: Task to execute.
            execute_fn: async (SubTask, dict[str, str]) -> str
            dep_results: Results from dependency tasks.
            validate_fn: Optional async (str) -> bool validator.

        Returns:
            Task result string.
        """
        if subtask.speculation_tier == SpeculationTier.FREE:
            return await execute_fn(subtask, dep_results)

        elif subtask.speculation_tier == SpeculationTier.GUARDED:
            cp = self.context.checkpoint(subtask)
            try:
                result = await execute_fn(subtask, dep_results)
                cp.result = result

                if validate_fn:
                    valid = await validate_fn(result)
                    if not valid:
                        self.context.rollback(cp, subtask)
                        raise RuntimeError(
                            f"Speculative execution rejected by validator: {subtask.id}"
                        )

                self.context.commit(cp)
                return result
            except RuntimeError:
                raise
            except Exception:
                self.context.rollback(cp, subtask)
                raise

        else:  # NONE — pre-approved by RiskRouter
            return await execute_fn(subtask, dep_results)
