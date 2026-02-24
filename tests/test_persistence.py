"""
Tests for SQLite Persistence.

Verifies:
- Save and load ExecutionResult
- Save and load traces
- List pipelines
- DB integrity after "restart" (close + reopen)
- In-memory database for testing
"""

from kovrin.core.models import (
    ExecutionResult,
    RiskLevel,
    SubTask,
    TaskStatus,
    Trace,
)
from kovrin.storage.repository import PipelineRepository

# ─── Helpers ────────────────────────────────────────────────


def make_result(intent_id: str = "test-intent-1", success: bool = True) -> ExecutionResult:
    traces = [
        Trace(
            intent_id=intent_id,
            event_type="INTENT_RECEIVED",
            description="Test intent received",
        ),
        Trace(
            intent_id=intent_id,
            task_id="task-1",
            event_type="EXECUTION_COMPLETE",
            description="Task completed",
            risk_level=RiskLevel.LOW,
            l0_passed=True,
        ),
    ]
    sub_tasks = [
        SubTask(
            id="task-1",
            description="Analyze data",
            risk_level=RiskLevel.LOW,
            status=TaskStatus.COMPLETED,
        ),
    ]
    return ExecutionResult(
        intent_id=intent_id,
        output="Analysis complete. Results: ...",
        success=success,
        sub_tasks=sub_tasks,
        traces=traces,
        graph_summary={"waves": [["task-1"]]},
    )


# ─── Tests ──────────────────────────────────────────────────


class TestPipelineRepository:
    def setup_method(self):
        self.repo = PipelineRepository(db_url=":memory:")

    def teardown_method(self):
        self.repo.close()

    def test_save_and_get_result(self):
        result = make_result()
        self.repo.save_result(result, intent="Test intent", constraints=["safe"])

        loaded = self.repo.get_result("test-intent-1")
        assert loaded is not None
        assert loaded.intent_id == "test-intent-1"
        assert loaded.success is True
        assert "Analysis complete" in loaded.output

    def test_get_nonexistent_result(self):
        loaded = self.repo.get_result("nonexistent")
        assert loaded is None

    def test_save_and_get_traces(self):
        result = make_result()
        self.repo.save_result(result)

        traces = self.repo.get_traces("test-intent-1")
        assert len(traces) == 2
        assert traces[0].event_type == "INTENT_RECEIVED"
        assert traces[1].event_type == "EXECUTION_COMPLETE"
        assert traces[1].risk_level == RiskLevel.LOW
        assert traces[1].l0_passed is True

    def test_trace_details_preserved(self):
        result = ExecutionResult(
            intent_id="detail-test",
            output="ok",
            traces=[
                Trace(
                    intent_id="detail-test",
                    event_type="TEST",
                    description="Test with details",
                    details={"key": "value", "count": 42},
                ),
            ],
        )
        self.repo.save_result(result)

        traces = self.repo.get_traces("detail-test")
        assert len(traces) == 1
        assert traces[0].details["key"] == "value"
        assert traces[0].details["count"] == 42

    def test_list_pipelines(self):
        self.repo.save_result(make_result("intent-1"), intent="First")
        self.repo.save_result(make_result("intent-2"), intent="Second")
        self.repo.save_result(make_result("intent-3", success=False), intent="Third")

        pipelines = self.repo.list_pipelines()
        assert len(pipelines) == 3
        # Each has expected fields
        for p in pipelines:
            assert "intent_id" in p
            assert "intent" in p
            assert "success" in p

    def test_list_pipelines_limit(self):
        for i in range(10):
            self.repo.save_result(make_result(f"intent-{i}"))

        pipelines = self.repo.list_pipelines(limit=3)
        assert len(pipelines) == 3

    def test_list_pipelines_offset(self):
        for i in range(5):
            self.repo.save_result(make_result(f"intent-{i}"), intent=f"Intent {i}")

        all_pipelines = self.repo.list_pipelines()
        offset_pipelines = self.repo.list_pipelines(offset=2)
        assert len(offset_pipelines) == 3

    def test_pipeline_count(self):
        assert self.repo.pipeline_count == 0
        self.repo.save_result(make_result("a"))
        assert self.repo.pipeline_count == 1
        self.repo.save_result(make_result("b"))
        assert self.repo.pipeline_count == 2

    def test_subtasks_preserved(self):
        result = make_result()
        self.repo.save_result(result)

        loaded = self.repo.get_result("test-intent-1")
        assert len(loaded.sub_tasks) == 1
        assert loaded.sub_tasks[0].description == "Analyze data"
        assert loaded.sub_tasks[0].risk_level == RiskLevel.LOW

    def test_graph_summary_preserved(self):
        result = make_result()
        self.repo.save_result(result)

        loaded = self.repo.get_result("test-intent-1")
        assert loaded.graph_summary == {"waves": [["task-1"]]}

    def test_failed_result(self):
        result = make_result(success=False)
        result.output = "All tasks rejected"
        self.repo.save_result(result)

        loaded = self.repo.get_result("test-intent-1")
        assert loaded.success is False
        assert "All tasks rejected" in loaded.output

    def test_overwrite_result(self):
        """Saving with same intent_id should overwrite."""
        result1 = make_result()
        result1.output = "Version 1"
        self.repo.save_result(result1)

        result2 = make_result()
        result2.output = "Version 2"
        self.repo.save_result(result2)

        loaded = self.repo.get_result("test-intent-1")
        assert loaded.output == "Version 2"


class TestPersistenceAcrossRestart:
    def test_data_survives_close_reopen(self, tmp_path):
        """Data should persist after closing and reopening the DB."""
        db_file = str(tmp_path / "test.db")

        # Save
        repo1 = PipelineRepository(db_url=db_file)
        repo1.save_result(make_result("persist-1"), intent="Persist test")
        repo1.close()

        # Reopen
        repo2 = PipelineRepository(db_url=db_file)
        loaded = repo2.get_result("persist-1")
        assert loaded is not None
        assert loaded.intent_id == "persist-1"
        assert loaded.success is True

        pipelines = repo2.list_pipelines()
        assert len(pipelines) == 1
        assert pipelines[0]["intent"] == "Persist test"

        repo2.close()

    def test_traces_survive_restart(self, tmp_path):
        """Traces should persist after closing and reopening the DB."""
        db_file = str(tmp_path / "traces.db")

        repo1 = PipelineRepository(db_url=db_file)
        repo1.save_result(make_result("trace-persist"))
        repo1.close()

        repo2 = PipelineRepository(db_url=db_file)
        traces = repo2.get_traces("trace-persist")
        assert len(traces) == 2
        repo2.close()
