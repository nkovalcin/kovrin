"""
Session Chain — Sequential Pipeline Orchestration

Executes a series of Kovrin pipeline runs where each step's output
feeds into the next step's context.  Supports template variables
(``{step_N.output}``), configurable error handling, and chain-level
metrics aggregation.

Safety: every step runs through the full Kovrin pipeline (critic
pipeline, risk router, watchdog) — no safety bypass.
"""

from __future__ import annotations

import logging
import re
import time
import uuid
from typing import TYPE_CHECKING

from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import (
    ChainErrorStrategy,
    ChainResult,
    ChainStep,
    ChainStepResult,
    ChainStepStatus,
    Trace,
)
from kovrin.exceptions import ChainError

if TYPE_CHECKING:
    from kovrin import Kovrin

logger = logging.getLogger(__name__)

# Regex for {step_N.output} template variables
_TEMPLATE_RE = re.compile(r"\{step_(\d+)\.output\}")


class SessionChain:
    """Orchestrates sequential pipeline runs where each run's output feeds the next.

    Example::

        chain = SessionChain(
            engine=kovrin,
            steps=[
                ChainStep(intent="Research AI safety frameworks"),
                ChainStep(intent="Summarize findings from {step_0.output}"),
            ],
        )
        result = await chain.run()
        print(result.final_output)

    Every step runs through the full ``Kovrin.run()`` pipeline, so all
    safety invariants (constitutional check, risk routing, watchdog) are
    enforced per step.
    """

    def __init__(
        self,
        engine: Kovrin,
        steps: list[ChainStep],
        error_strategy: ChainErrorStrategy = ChainErrorStrategy.STOP_ON_FIRST,
        max_retries: int = 2,
        chain_id: str | None = None,
    ) -> None:
        self._engine = engine
        self._steps = steps
        self._error_strategy = error_strategy
        self._max_retries = max_retries
        self._chain_id = chain_id or f"chain-{uuid.uuid4().hex[:8]}"
        self._results: dict[int, ChainStepResult] = {}

    @property
    def chain_id(self) -> str:
        return self._chain_id

    async def run(self) -> ChainResult:
        """Execute the chain sequentially, feeding each step's output forward."""
        from kovrin.observability.tracing import get_tracer

        tracer = get_tracer()
        trace_log = ImmutableTraceLog()

        step_results: list[ChainStepResult] = []
        chain_success = True
        start_time = time.monotonic()

        with tracer.start_as_current_span("kovrin.chain") as chain_span:
            chain_span.set_attribute("kovrin.chain_id", self._chain_id)
            chain_span.set_attribute("kovrin.chain_steps", len(self._steps))
            chain_span.set_attribute(
                "kovrin.chain_error_strategy", self._error_strategy.value
            )

            await trace_log.append_async(
                Trace(
                    intent_id=self._chain_id,
                    event_type="CHAIN_START",
                    description=f"Starting chain with {len(self._steps)} steps",
                    details={
                        "chain_id": self._chain_id,
                        "error_strategy": self._error_strategy.value,
                        "step_count": len(self._steps),
                    },
                )
            )

            for i, step in enumerate(self._steps):
                with tracer.start_as_current_span("kovrin.chain.step") as step_span:
                    step_span.set_attribute("kovrin.step_index", i)
                    step_span.set_attribute("kovrin.step_id", step.id)

                    step_result = await self._execute_step(
                        step, i, trace_log, step_span
                    )
                    step_results.append(step_result)
                    self._results[i] = step_result

                    if step_result.status == ChainStepStatus.FAILED:
                        chain_success = False
                        if self._error_strategy == ChainErrorStrategy.STOP_ON_FIRST:
                            logger.warning(
                                "Chain %s stopping at step %d: %s",
                                self._chain_id,
                                i,
                                step_result.error,
                            )
                            break

            total_duration = (time.monotonic() - start_time) * 1000

            # Compute final output from the last successful step
            final_output = ""
            for sr in reversed(step_results):
                if (
                    sr.status == ChainStepStatus.COMPLETED
                    and sr.execution_result
                ):
                    final_output = sr.execution_result.output
                    break

            await trace_log.append_async(
                Trace(
                    intent_id=self._chain_id,
                    event_type="CHAIN_COMPLETE",
                    description=(
                        f"Chain complete: {sum(1 for s in step_results if s.status == ChainStepStatus.COMPLETED)}"
                        f"/{len(self._steps)} steps succeeded"
                    ),
                    details={
                        "chain_id": self._chain_id,
                        "success": chain_success,
                        "duration_ms": total_duration,
                    },
                )
            )

            chain_span.set_attribute("kovrin.chain_success", chain_success)

        return ChainResult(
            chain_id=self._chain_id,
            steps=step_results,
            success=chain_success,
            total_duration_ms=total_duration,
            total_cost_usd=sum(s.cost_usd for s in step_results),
            total_input_tokens=sum(s.input_tokens for s in step_results),
            total_output_tokens=sum(s.output_tokens for s in step_results),
            final_output=final_output,
        )

    # ── Private helpers ──────────────────────────────────────

    async def _execute_step(
        self,
        step: ChainStep,
        index: int,
        trace_log: ImmutableTraceLog,
        span,
    ) -> ChainStepResult:
        """Execute a single step with optional retries."""
        attempts = 1 if self._error_strategy != ChainErrorStrategy.RETRY else (
            self._max_retries + 1
        )

        last_error: str | None = None
        for attempt in range(attempts):
            start = time.monotonic()
            try:
                # Resolve intent template variables
                resolved_intent = self._resolve_templates(step.intent, index)
                context = self._build_step_context(step, index)

                span.set_attribute("kovrin.step_intent", resolved_intent[:200])
                if attempt > 0:
                    span.set_attribute("kovrin.step_retry", attempt)

                result = await self._engine.run(
                    intent=resolved_intent,
                    constraints=step.constraints or None,
                    context=context or None,
                    trace_log=trace_log,
                )
                duration = (time.monotonic() - start) * 1000

                if result.success:
                    return ChainStepResult(
                        step_id=step.id,
                        step_index=index,
                        status=ChainStepStatus.COMPLETED,
                        execution_result=result,
                        duration_ms=duration,
                    )
                else:
                    last_error = f"Pipeline returned success=False: {result.output[:200]}"
                    logger.warning(
                        "Chain %s step %d attempt %d failed: %s",
                        self._chain_id,
                        index,
                        attempt + 1,
                        last_error,
                    )

            except Exception as exc:
                duration = (time.monotonic() - start) * 1000
                last_error = str(exc)
                logger.warning(
                    "Chain %s step %d attempt %d exception: %s",
                    self._chain_id,
                    index,
                    attempt + 1,
                    last_error,
                )

        # All attempts exhausted
        return ChainStepResult(
            step_id=step.id,
            step_index=index,
            status=ChainStepStatus.FAILED,
            error=last_error,
            duration_ms=(time.monotonic() - start) * 1000 if 'start' in dir() else 0.0,
        )

    def _resolve_templates(self, intent: str, step_index: int) -> str:
        """Replace ``{step_N.output}`` placeholders with actual results."""

        def _replace(match: re.Match) -> str:
            ref_idx = int(match.group(1))
            if ref_idx >= step_index:
                return match.group(0)  # Forward reference — leave as-is
            result = self._results.get(ref_idx)
            if result and result.execution_result:
                return result.execution_result.output
            return f"[step {ref_idx} output unavailable]"

        return _TEMPLATE_RE.sub(_replace, intent)

    def _build_step_context(self, step: ChainStep, step_index: int) -> dict:
        """Build context dict for a step, injecting previous results."""
        ctx = dict(step.context) if step.context else {}

        if step.inject_previous and step_index > 0:
            prev = self._results.get(step_index - 1)
            if prev and prev.execution_result:
                ctx["previous_step_output"] = prev.execution_result.output
                ctx["previous_step_id"] = prev.step_id

        # Inject chain metadata
        ctx["chain_id"] = self._chain_id
        ctx["step_index"] = step_index
        ctx["total_steps"] = len(self._steps)

        return ctx
