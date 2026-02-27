"""Session Chain unit tests.

Tests for the SessionChain class which orchestrates sequential pipeline
runs where each step's output feeds into the next step's context.
"""

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin.core.models import (
    ChainErrorStrategy,
    ChainResult,
    ChainStep,
    ChainStepResult,
    ChainStepStatus,
    ExecutionResult,
    Trace,
)
from kovrin.engine.chain import SessionChain, _TEMPLATE_RE
from kovrin.exceptions import ChainError


# ─── Helpers ────────────────────────────────────────────────


def _make_engine_mock(results: list[ExecutionResult | Exception]) -> MagicMock:
    """Create a mock Kovrin engine that returns pre-defined results."""
    engine = MagicMock()
    call_count = 0

    async def _run(intent, constraints=None, context=None, trace_log=None):
        nonlocal call_count
        idx = min(call_count, len(results) - 1)
        call_count += 1
        r = results[idx]
        if isinstance(r, Exception):
            raise r
        return r

    engine.run = AsyncMock(side_effect=_run)
    return engine


def _ok_result(output: str = "Step output", intent_id: str = "test-intent") -> ExecutionResult:
    return ExecutionResult(intent_id=intent_id, output=output, success=True)


def _fail_result(output: str = "Failed", intent_id: str = "test-intent") -> ExecutionResult:
    return ExecutionResult(intent_id=intent_id, output=output, success=False)


# ─── Model Tests ────────────────────────────────────────────


class TestChainModels:
    """Test chain-related Pydantic models."""

    def test_chain_step_defaults(self):
        step = ChainStep(intent="Do something")
        assert step.intent == "Do something"
        assert step.inject_previous is True
        assert step.constraints == []
        assert step.context == {}
        assert step.id.startswith("step-")

    def test_chain_step_frozen(self):
        step = ChainStep(intent="Test")
        with pytest.raises(Exception):
            step.intent = "Changed"

    def test_chain_step_with_context(self):
        step = ChainStep(
            intent="Analyze {step_0.output}",
            constraints=["Be concise"],
            context={"key": "value"},
            inject_previous=False,
        )
        assert step.inject_previous is False
        assert step.context == {"key": "value"}

    def test_chain_step_result_defaults(self):
        result = ChainStepResult(step_id="s1", step_index=0)
        assert result.status == ChainStepStatus.PENDING
        assert result.execution_result is None
        assert result.error is None
        assert result.cost_usd == 0.0

    def test_chain_result_defaults(self):
        result = ChainResult(chain_id="c1")
        assert result.success is True
        assert result.steps == []
        assert result.total_cost_usd == 0.0

    def test_chain_error_strategy_values(self):
        assert ChainErrorStrategy.STOP_ON_FIRST.value == "STOP_ON_FIRST"
        assert ChainErrorStrategy.SKIP_FAILED.value == "SKIP_FAILED"
        assert ChainErrorStrategy.RETRY.value == "RETRY"

    def test_chain_step_status_values(self):
        assert ChainStepStatus.PENDING.value == "PENDING"
        assert ChainStepStatus.RUNNING.value == "RUNNING"
        assert ChainStepStatus.COMPLETED.value == "COMPLETED"
        assert ChainStepStatus.FAILED.value == "FAILED"
        assert ChainStepStatus.SKIPPED.value == "SKIPPED"


class TestChainError:
    """Test ChainError exception."""

    def test_chain_error_attributes(self):
        err = ChainError(chain_id="c1", step_index=2, message="boom")
        assert err.chain_id == "c1"
        assert err.step_index == 2
        assert "Step 2" in str(err)
        assert "boom" in str(err)

    def test_chain_error_details(self):
        err = ChainError(
            chain_id="c1", step_index=0, message="fail",
            details={"extra": True},
        )
        assert err.details["chain_id"] == "c1"
        assert err.details["step_index"] == 0
        assert err.details["extra"] is True


# ─── Template Resolution Tests ──────────────────────────────


class TestTemplateResolution:
    """Test {step_N.output} template variable resolution."""

    def test_template_regex_matches(self):
        matches = _TEMPLATE_RE.findall("Use {step_0.output} and {step_2.output}")
        assert matches == ["0", "2"]

    def test_template_regex_no_match(self):
        matches = _TEMPLATE_RE.findall("No templates here")
        assert matches == []

    @pytest.mark.asyncio
    async def test_resolve_templates_basic(self):
        engine = _make_engine_mock([
            _ok_result("Research findings"),
            _ok_result("Summary"),
        ])
        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Research AI"),
                ChainStep(intent="Summarize {step_0.output}"),
            ],
        )
        result = await chain.run()
        assert result.success is True

        # Verify second call used resolved template
        second_call = engine.run.call_args_list[1]
        assert "Research findings" in second_call.kwargs.get("intent", second_call.args[0] if second_call.args else "")

    @pytest.mark.asyncio
    async def test_resolve_forward_reference_preserved(self):
        """Forward references like {step_1.output} in step 0 are left as-is."""
        engine = _make_engine_mock([_ok_result("Out")])
        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Do {step_1.output}")],
        )
        result = await chain.run()
        call_intent = engine.run.call_args_list[0].kwargs.get(
            "intent", engine.run.call_args_list[0].args[0] if engine.run.call_args_list[0].args else ""
        )
        assert "{step_1.output}" in call_intent

    @pytest.mark.asyncio
    async def test_resolve_unavailable_step(self):
        """Reference to a failed step produces [unavailable] placeholder."""
        engine = _make_engine_mock([
            _fail_result("Failed step"),
            _ok_result("OK"),
        ])
        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Step 0"),
                ChainStep(intent="Use {step_0.output}"),
            ],
            error_strategy=ChainErrorStrategy.SKIP_FAILED,
        )
        result = await chain.run()
        # Step 0 failed → step 1 should get placeholder
        second_call = engine.run.call_args_list[1]
        intent_arg = second_call.kwargs.get("intent", "")
        assert "unavailable" in intent_arg or "Failed step" in intent_arg


# ─── Execution Flow Tests ───────────────────────────────────


class TestSessionChainExecution:
    """Test chain execution flow."""

    @pytest.mark.asyncio
    async def test_single_step_chain(self):
        engine = _make_engine_mock([_ok_result("Done")])
        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Do something")],
        )
        result = await chain.run()
        assert result.success is True
        assert len(result.steps) == 1
        assert result.steps[0].status == ChainStepStatus.COMPLETED
        assert result.final_output == "Done"

    @pytest.mark.asyncio
    async def test_two_step_chain(self):
        engine = _make_engine_mock([
            _ok_result("Step 1 output"),
            _ok_result("Step 2 output"),
        ])
        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Step 1"),
                ChainStep(intent="Step 2"),
            ],
        )
        result = await chain.run()
        assert result.success is True
        assert len(result.steps) == 2
        assert result.final_output == "Step 2 output"
        assert engine.run.call_count == 2

    @pytest.mark.asyncio
    async def test_previous_output_injected_into_context(self):
        engine = _make_engine_mock([
            _ok_result("Research data"),
            _ok_result("Summary"),
        ])
        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Research"),
                ChainStep(intent="Summarize", inject_previous=True),
            ],
        )
        await chain.run()

        second_call = engine.run.call_args_list[1]
        ctx = second_call.kwargs.get("context", {})
        assert ctx.get("previous_step_output") == "Research data"

    @pytest.mark.asyncio
    async def test_inject_previous_false(self):
        engine = _make_engine_mock([
            _ok_result("Step 1"),
            _ok_result("Step 2"),
        ])
        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="First"),
                ChainStep(intent="Second", inject_previous=False),
            ],
        )
        await chain.run()

        second_call = engine.run.call_args_list[1]
        ctx = second_call.kwargs.get("context", {})
        assert "previous_step_output" not in ctx

    @pytest.mark.asyncio
    async def test_chain_metadata_in_context(self):
        engine = _make_engine_mock([_ok_result("OK")])
        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Test")],
            chain_id="my-chain",
        )
        await chain.run()

        call = engine.run.call_args_list[0]
        ctx = call.kwargs.get("context", {})
        assert ctx["chain_id"] == "my-chain"
        assert ctx["step_index"] == 0
        assert ctx["total_steps"] == 1

    @pytest.mark.asyncio
    async def test_custom_chain_id(self):
        engine = _make_engine_mock([_ok_result("OK")])
        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Test")],
            chain_id="custom-123",
        )
        result = await chain.run()
        assert result.chain_id == "custom-123"

    @pytest.mark.asyncio
    async def test_chain_id_auto_generated(self):
        engine = _make_engine_mock([_ok_result("OK")])
        chain = SessionChain(engine=engine, steps=[ChainStep(intent="Test")])
        assert chain.chain_id.startswith("chain-")


# ─── Error Strategy Tests ───────────────────────────────────


class TestChainErrorStrategies:
    """Test different error handling strategies."""

    @pytest.mark.asyncio
    async def test_stop_on_first_failure(self):
        engine = _make_engine_mock([
            _ok_result("OK"),
            _fail_result("Error"),
            _ok_result("Should not run"),
        ])
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
        assert len(result.steps) == 2  # Only 2 steps ran
        assert result.steps[0].status == ChainStepStatus.COMPLETED
        assert result.steps[1].status == ChainStepStatus.FAILED

    @pytest.mark.asyncio
    async def test_skip_failed_continues(self):
        engine = _make_engine_mock([
            _fail_result("Error"),
            _ok_result("Step 2 OK"),
        ])
        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Step 0"),
                ChainStep(intent="Step 1"),
            ],
            error_strategy=ChainErrorStrategy.SKIP_FAILED,
        )
        result = await chain.run()
        assert result.success is False  # Overall failed because step 0 failed
        assert len(result.steps) == 2
        assert result.steps[0].status == ChainStepStatus.FAILED
        assert result.steps[1].status == ChainStepStatus.COMPLETED
        assert result.final_output == "Step 2 OK"

    @pytest.mark.asyncio
    async def test_retry_strategy_succeeds_on_retry(self):
        call_count = 0

        async def _flaky_run(intent, constraints=None, context=None, trace_log=None):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                return _fail_result("First attempt failed")
            return _ok_result("Retry succeeded")

        engine = MagicMock()
        engine.run = AsyncMock(side_effect=_flaky_run)

        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Flaky step")],
            error_strategy=ChainErrorStrategy.RETRY,
            max_retries=2,
        )
        result = await chain.run()
        assert result.success is True
        assert result.steps[0].status == ChainStepStatus.COMPLETED

    @pytest.mark.asyncio
    async def test_retry_exhausted(self):
        engine = _make_engine_mock([_fail_result("Always fails")])
        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Bad step")],
            error_strategy=ChainErrorStrategy.RETRY,
            max_retries=2,
        )
        result = await chain.run()
        assert result.success is False
        assert result.steps[0].status == ChainStepStatus.FAILED

    @pytest.mark.asyncio
    async def test_exception_in_step(self):
        engine = _make_engine_mock([ConnectionError("timeout")])
        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Will crash")],
        )
        result = await chain.run()
        assert result.success is False
        assert result.steps[0].status == ChainStepStatus.FAILED
        assert "timeout" in result.steps[0].error


# ─── Metrics Aggregation Tests ──────────────────────────────


class TestChainMetrics:
    """Test chain-level metrics aggregation."""

    @pytest.mark.asyncio
    async def test_duration_tracked(self):
        engine = _make_engine_mock([_ok_result("OK")])
        chain = SessionChain(engine=engine, steps=[ChainStep(intent="Test")])
        result = await chain.run()
        assert result.total_duration_ms > 0

    @pytest.mark.asyncio
    async def test_step_duration_tracked(self):
        engine = _make_engine_mock([_ok_result("OK")])
        chain = SessionChain(engine=engine, steps=[ChainStep(intent="Test")])
        result = await chain.run()
        assert result.steps[0].duration_ms > 0


# ─── Edge Cases ──────────────────────────────────────────────


class TestChainEdgeCases:
    """Test edge cases and boundary conditions."""

    @pytest.mark.asyncio
    async def test_empty_steps_list(self):
        engine = _make_engine_mock([])
        chain = SessionChain(engine=engine, steps=[])
        result = await chain.run()
        assert result.success is True
        assert len(result.steps) == 0
        assert result.final_output == ""

    @pytest.mark.asyncio
    async def test_step_with_static_context(self):
        engine = _make_engine_mock([_ok_result("OK")])
        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Test", context={"budget": "1000"})],
        )
        await chain.run()
        call = engine.run.call_args_list[0]
        ctx = call.kwargs.get("context", {})
        assert ctx["budget"] == "1000"

    @pytest.mark.asyncio
    async def test_step_constraints_passed(self):
        engine = _make_engine_mock([_ok_result("OK")])
        chain = SessionChain(
            engine=engine,
            steps=[ChainStep(intent="Test", constraints=["Be safe"])],
        )
        await chain.run()
        call = engine.run.call_args_list[0]
        constraints = call.kwargs.get("constraints", [])
        assert constraints == ["Be safe"]

    @pytest.mark.asyncio
    async def test_three_step_chain_output_propagation(self):
        engine = _make_engine_mock([
            _ok_result("Data collected"),
            _ok_result("Data analyzed"),
            _ok_result("Report generated"),
        ])
        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Collect data"),
                ChainStep(intent="Analyze {step_0.output}"),
                ChainStep(intent="Generate report from {step_1.output}"),
            ],
        )
        result = await chain.run()
        assert result.success is True
        assert len(result.steps) == 3
        assert result.final_output == "Report generated"

        # Verify template resolution in step 2
        third_call = engine.run.call_args_list[2]
        intent_arg = third_call.kwargs.get("intent", "")
        assert "Data analyzed" in intent_arg

    @pytest.mark.asyncio
    async def test_all_steps_fail(self):
        engine = _make_engine_mock([_fail_result("Fail")])
        chain = SessionChain(
            engine=engine,
            steps=[
                ChainStep(intent="Fail 1"),
                ChainStep(intent="Fail 2"),
            ],
            error_strategy=ChainErrorStrategy.STOP_ON_FIRST,
        )
        result = await chain.run()
        assert result.success is False
        assert result.final_output == ""
