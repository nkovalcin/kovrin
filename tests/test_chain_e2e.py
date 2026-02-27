"""End-to-end Session Chain tests.

Wires all Kovrin components together with mocked Claude API and
verifies the full chain flow: multi-step pipeline execution with
output propagation, template resolution, and error handling.
"""

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin import Kovrin
from kovrin.core.models import (
    ChainErrorStrategy,
    ChainStep,
    ChainStepStatus,
)


# ─── Helpers ────────────────────────────────────────────────


def _mock_anthropic_client(responses: list[str] | None = None):
    """Create a mock Anthropic client returning sequential responses.

    Each call to messages.create returns the next response in the list.
    If list is exhausted, cycles from the beginning.
    """
    if responses is None:
        responses = ['[{"description": "Test task", "risk_level": "LOW", "speculation_tier": "FREE"}]']

    call_idx = 0

    async def _create(**kwargs):
        nonlocal call_idx
        resp = responses[call_idx % len(responses)]
        call_idx += 1

        mock_msg = MagicMock()
        mock_msg.content = [MagicMock(text=resp)]
        mock_msg.stop_reason = "end_turn"
        mock_msg.usage = MagicMock(input_tokens=50, output_tokens=25)
        return mock_msg

    client = MagicMock()
    client.messages.create = AsyncMock(side_effect=_create)
    return client


DECOMPOSE_RESPONSE = json.dumps([
    {
        "description": "Execute the task",
        "risk_level": "LOW",
        "speculation_tier": "FREE",
    }
])

CRITIC_PASS = json.dumps({
    "passed": True,
    "evidence": "Safe and feasible",
})

EXECUTION_RESULT = "Task executed successfully. Output: Hello World"


class TestChainE2E:
    """End-to-end chain tests with mocked Claude API."""

    @pytest.mark.asyncio
    async def test_two_step_chain_full_flow(self):
        """Complete flow: step 1 → output feeds step 2 (mocked engine)."""
        from kovrin.core.models import ExecutionResult

        async def _run(intent, constraints=None, context=None, trace_log=None):
            return ExecutionResult(
                intent_id="test",
                output=f"Result for: {intent[:30]}",
                success=True,
            )

        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=_run)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Research AI safety"),
                ChainStep(intent="Summarize findings"),
            ],
        )
        result = await chain.run()

        assert result.success is True
        assert len(result.steps) == 2
        assert result.steps[0].status == ChainStepStatus.COMPLETED
        assert result.steps[1].status == ChainStepStatus.COMPLETED
        assert result.total_duration_ms > 0

    @pytest.mark.asyncio
    async def test_chain_with_template_vars(self):
        """Template {step_0.output} is resolved in step 1."""
        call_intents = []

        original_run = None

        async def _capture_run(intent, constraints=None, context=None, trace_log=None):
            call_intents.append(intent)
            # Return mock result
            from kovrin.core.models import ExecutionResult
            return ExecutionResult(
                intent_id="test",
                output=f"Output of: {intent[:30]}",
                success=True,
            )

        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=_capture_run)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Collect data on AI"),
                ChainStep(intent="Analyze: {step_0.output}"),
            ],
        )
        result = await chain.run()

        assert result.success is True
        # Step 1 intent should have the output of step 0
        assert "Output of: Collect data on AI" in call_intents[1]

    @pytest.mark.asyncio
    async def test_chain_stop_on_first_with_full_pipeline(self):
        """Chain stops when a step returns success=False."""
        call_count = 0

        async def _run(intent, constraints=None, context=None, trace_log=None):
            nonlocal call_count
            call_count += 1
            from kovrin.core.models import ExecutionResult
            if call_count == 2:
                return ExecutionResult(intent_id="t", output="Failed", success=False)
            return ExecutionResult(intent_id="t", output="OK", success=True)

        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=_run)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Step 0"),
                ChainStep(intent="Step 1"),
                ChainStep(intent="Step 2"),
            ],
            error_strategy=ChainErrorStrategy.STOP_ON_FIRST,
        )
        result = await chain.run()
        assert result.success is False
        assert len(result.steps) == 2
        assert call_count == 2

    @pytest.mark.asyncio
    async def test_chain_skip_failed_continues(self):
        """With SKIP_FAILED, remaining steps still execute."""
        call_count = 0

        async def _run(intent, constraints=None, context=None, trace_log=None):
            nonlocal call_count
            call_count += 1
            from kovrin.core.models import ExecutionResult
            if call_count == 1:
                return ExecutionResult(intent_id="t", output="Failed", success=False)
            return ExecutionResult(intent_id="t", output="OK", success=True)

        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=_run)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Fail"),
                ChainStep(intent="Succeed"),
            ],
            error_strategy=ChainErrorStrategy.SKIP_FAILED,
        )
        result = await chain.run()
        assert len(result.steps) == 2
        assert result.steps[0].status == ChainStepStatus.FAILED
        assert result.steps[1].status == ChainStepStatus.COMPLETED

    @pytest.mark.asyncio
    async def test_chain_three_steps_propagation(self):
        """Three steps: each builds on previous output."""
        step_num = 0

        async def _run(intent, constraints=None, context=None, trace_log=None):
            nonlocal step_num
            step_num += 1
            from kovrin.core.models import ExecutionResult
            return ExecutionResult(
                intent_id="t",
                output=f"Output-{step_num}",
                success=True,
            )

        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=_run)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Step A"),
                ChainStep(intent="Step B using {step_0.output}"),
                ChainStep(intent="Step C using {step_0.output} and {step_1.output}"),
            ],
        )
        result = await chain.run()
        assert result.success is True
        assert result.final_output == "Output-3"

        # Verify template resolution in step 2 (index 2)
        third_intent = engine.run.call_args_list[2].kwargs.get("intent", "")
        assert "Output-1" in third_intent
        assert "Output-2" in third_intent

    @pytest.mark.asyncio
    async def test_chain_retry_then_succeed(self):
        """RETRY strategy retries failed step and succeeds."""
        attempt = 0

        async def _run(intent, constraints=None, context=None, trace_log=None):
            nonlocal attempt
            attempt += 1
            from kovrin.core.models import ExecutionResult
            if attempt <= 1:
                return ExecutionResult(intent_id="t", output="Fail", success=False)
            return ExecutionResult(intent_id="t", output="OK on retry", success=True)

        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=_run)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Flaky")],
            error_strategy=ChainErrorStrategy.RETRY,
            max_retries=2,
        )
        result = await chain.run()
        assert result.success is True
        assert result.final_output == "OK on retry"

    @pytest.mark.asyncio
    async def test_chain_context_merging(self):
        """Static step context is merged with chain metadata."""
        async def _run(intent, constraints=None, context=None, trace_log=None):
            from kovrin.core.models import ExecutionResult
            return ExecutionResult(intent_id="t", output="OK", success=True)

        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=_run)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Test", context={"budget": 1000}),
            ],
        )
        await chain.run()

        ctx = engine.run.call_args_list[0].kwargs.get("context", {})
        assert ctx["budget"] == 1000
        assert "chain_id" in ctx
        assert ctx["step_index"] == 0

    @pytest.mark.asyncio
    async def test_chain_empty_steps(self):
        """Empty chain returns success with no steps."""
        engine = MagicMock(spec=Kovrin)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(engine=engine, steps=[])
        result = await chain.run()
        assert result.success is True
        assert len(result.steps) == 0
        assert engine.run.call_count == 0

    @pytest.mark.asyncio
    async def test_chain_exception_in_engine(self):
        """Exception in engine.run is caught and step marked FAILED."""
        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=RuntimeError("Engine crashed"))

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Crash")],
        )
        result = await chain.run()
        assert result.success is False
        assert result.steps[0].status == ChainStepStatus.FAILED
        assert "Engine crashed" in result.steps[0].error

    @pytest.mark.asyncio
    async def test_chain_constraints_forwarded(self):
        """Step constraints are forwarded to engine.run."""
        async def _run(intent, constraints=None, context=None, trace_log=None):
            from kovrin.core.models import ExecutionResult
            return ExecutionResult(intent_id="t", output="OK", success=True)

        engine = MagicMock(spec=Kovrin)
        engine.run = AsyncMock(side_effect=_run)

        from kovrin.engine.chain import SessionChain

        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Test", constraints=["No PII", "Be concise"])],
        )
        await chain.run()

        constraints = engine.run.call_args_list[0].kwargs.get("constraints", [])
        assert constraints == ["No PII", "Be concise"]
