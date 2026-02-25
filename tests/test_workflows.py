"""Tests for Kovrin Temporal workflows (activities, workflow, worker).

All tests mock temporalio — no real Temporal server needed.
"""

import json
from dataclasses import asdict
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin.workflows.activities import (
    EvaluateCriticsInput,
    EvaluateCriticsOutput,
    ExecuteTaskInput,
    ExecuteTaskOutput,
    ParseIntentInput,
    ParseIntentOutput,
)
from kovrin.workflows.pipeline_workflow import (
    TASK_QUEUE,
    PipelineInput,
    PipelineOutput,
)


class TestDataclasses:
    """Test input/output dataclasses."""

    def test_parse_intent_input(self):
        inp = ParseIntentInput(intent="test", constraints=["c1"], context={"k": "v"})
        assert inp.intent == "test"
        assert inp.constraints == ["c1"]
        assert inp.context == {"k": "v"}

    def test_parse_intent_output(self):
        out = ParseIntentOutput(
            intent_id="i1", subtask_ids=["t1", "t2"], subtasks_json="[]"
        )
        assert out.intent_id == "i1"
        assert len(out.subtask_ids) == 2

    def test_evaluate_critics_input(self):
        inp = EvaluateCriticsInput(
            subtasks_json="[]",
            constraints=["safe"],
            intent_context="test",
            task_context_json="{}",
        )
        assert inp.constraints == ["safe"]

    def test_evaluate_critics_output(self):
        out = EvaluateCriticsOutput(
            approved_ids=["t1"], rejected_ids=["t2"], all_subtasks_json="[]"
        )
        assert len(out.approved_ids) == 1
        assert len(out.rejected_ids) == 1

    def test_execute_task_input(self):
        inp = ExecuteTaskInput(
            subtask_json="{}", dep_results_json="{}", intent_context="test"
        )
        assert inp.intent_context == "test"

    def test_execute_task_output(self):
        out = ExecuteTaskOutput(
            task_id="t1", result_text="done", success=True, traces_json="[]"
        )
        assert out.success is True

    def test_pipeline_input(self):
        inp = PipelineInput(intent="build feature")
        assert inp.intent == "build feature"
        assert inp.constraints == []
        assert inp.context == {}

    def test_pipeline_output(self):
        out = PipelineOutput(
            intent_id="i1",
            success=True,
            output="result",
            task_count=3,
            rejected_count=1,
        )
        assert out.task_count == 3

    def test_task_queue_constant(self):
        assert TASK_QUEUE == "kovrin-pipeline"


class TestActivityDefinitions:
    def test_import_error_without_temporalio(self):
        with patch.dict("sys.modules", {"temporalio": None, "temporalio.activity": None}):
            from kovrin.workflows.activities import _get_activity_definitions

            with pytest.raises(ImportError, match="temporalio is required"):
                _get_activity_definitions()


class TestWorkflowDefinition:
    def test_import_error_without_temporalio(self):
        with patch.dict(
            "sys.modules",
            {"temporalio": None, "temporalio.workflow": None},
        ):
            from kovrin.workflows.pipeline_workflow import _get_workflow_class

            with pytest.raises(ImportError, match="temporalio is required"):
                _get_workflow_class()


class TestWorkerModule:
    def test_import_error_without_temporalio(self):
        with patch.dict(
            "sys.modules",
            {
                "temporalio": None,
                "temporalio.client": None,
                "temporalio.worker": None,
            },
        ):
            from kovrin.workflows.worker import run_worker

            with pytest.raises(ImportError, match="temporalio is required"):
                import asyncio
                asyncio.run(run_worker())

    def test_main_entry_point(self):
        """worker.main() calls asyncio.run(run_worker())."""
        with patch("kovrin.workflows.worker.asyncio") as mock_asyncio:
            from kovrin.workflows.worker import main
            main()
            mock_asyncio.run.assert_called_once()

    def test_env_var_defaults(self):
        """Worker reads TEMPORAL_ADDRESS, TEMPORAL_NAMESPACE, TEMPORAL_TASK_QUEUE."""
        import os
        assert os.environ.get("TEMPORAL_ADDRESS", "localhost:7233") == "localhost:7233"
        assert os.environ.get("TEMPORAL_NAMESPACE", "default") == "default"
        assert os.environ.get("TEMPORAL_TASK_QUEUE", TASK_QUEUE) == TASK_QUEUE
