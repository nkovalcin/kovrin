"""Tests for SuperWork Orchestrator Agent."""

import json
from unittest.mock import AsyncMock, MagicMock

import pytest

from kovrin.superwork.models import (
    MetricsSnapshot,
    ProjectAnalysis,
    TaskCompletionEvent,
)


class TestOrchestratorImport:
    def test_import(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        assert OrchestratorAgent is not None


class TestOrchestratorConstruction:
    def test_defaults(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        mock_context = MagicMock()
        mock_metrics = MagicMock()
        orch = OrchestratorAgent(
            context_injector=mock_context,
            metrics_tracker=mock_metrics,
        )
        assert orch._model == "claude-opus-4-20250514"
        assert orch._task_history == []

    def test_custom_model(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
            model="claude-sonnet-4-20250514",
        )
        assert orch._model == "claude-sonnet-4-20250514"


class TestRecordCompletion:
    def test_history_accumulates(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
        )
        for i in range(5):
            event = TaskCompletionEvent(completed_task=f"Task {i}")
            orch.record_completion(event)
        assert len(orch._task_history) == 5

    def test_history_capped(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
        )
        for i in range(25):
            event = TaskCompletionEvent(completed_task=f"Task {i}")
            orch.record_completion(event)
        assert len(orch._task_history) == 20


class TestResponseParsing:
    """Test JSON parsing from Claude API responses."""

    def test_parse_clean_json(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
        )
        response_text = json.dumps(
            {
                "summary": "Project is on track",
                "focus_area": "Testing",
                "proposals": [
                    {
                        "title": "Add tests",
                        "description": "Write unit tests for auth module",
                        "risk_level": "LOW",
                        "rationale": "Improves reliability",
                        "estimated_tokens": 5000,
                        "auto_execute": False,
                        "priority": 1,
                    }
                ],
            }
        )
        analysis = orch._parse_response(response_text)
        assert isinstance(analysis, ProjectAnalysis)
        assert analysis.summary == "Project is on track"
        assert len(analysis.proposals) == 1
        assert analysis.proposals[0].title == "Add tests"

    def test_parse_markdown_fenced_json(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
        )
        response_text = """Here is my analysis:

```json
{
    "summary": "Needs refactoring",
    "focus_area": "Code quality",
    "proposals": []
}
```"""
        analysis = orch._parse_response(response_text)
        assert analysis.summary == "Needs refactoring"

    def test_parse_invalid_returns_error(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
        )
        analysis = orch._parse_response("This is not JSON at all")
        assert analysis.status == "parse_error"


class TestSafetyEnforcement:
    """Test that HIGH/CRITICAL risk proposals have auto_execute forced to False."""

    def test_critical_force_no_auto_execute(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
        )
        response_text = json.dumps(
            {
                "summary": "Dangerous operation",
                "focus_area": "Deployment",
                "proposals": [
                    {
                        "title": "Delete production DB",
                        "description": "Drop all tables",
                        "risk_level": "CRITICAL",
                        "auto_execute": True,
                        "priority": 1,
                    }
                ],
            }
        )
        analysis = orch._parse_response(response_text)
        assert analysis.proposals[0].auto_execute is False

    def test_high_force_no_auto_execute(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
        )
        response_text = json.dumps(
            {
                "summary": "Risky change",
                "focus_area": "Infrastructure",
                "proposals": [
                    {
                        "title": "Modify firewall rules",
                        "description": "Open port 22",
                        "risk_level": "HIGH",
                        "auto_execute": True,
                        "priority": 1,
                    }
                ],
            }
        )
        analysis = orch._parse_response(response_text)
        assert analysis.proposals[0].auto_execute is False

    def test_low_allows_auto_execute(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        orch = OrchestratorAgent(
            context_injector=MagicMock(),
            metrics_tracker=MagicMock(),
        )
        response_text = json.dumps(
            {
                "summary": "Safe change",
                "focus_area": "Docs",
                "proposals": [
                    {
                        "title": "Update README",
                        "description": "Fix typo",
                        "risk_level": "LOW",
                        "auto_execute": True,
                        "priority": 1,
                    }
                ],
            }
        )
        analysis = orch._parse_response(response_text)
        assert analysis.proposals[0].auto_execute is True


class TestAnalyzeAndPropose:
    """Test the main analyze_and_propose flow with mocked Claude API."""

    @pytest.mark.asyncio
    async def test_api_unavailable_fallback(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        mock_client = MagicMock()
        mock_client.messages.create = AsyncMock(side_effect=Exception("API down"))

        orch = OrchestratorAgent(
            client=mock_client,
            context_injector=MagicMock(get_relevant_context=MagicMock(return_value="context")),
            metrics_tracker=MagicMock(snapshot=MagicMock(return_value=MetricsSnapshot())),
        )
        analysis = await orch.analyze_and_propose()
        assert analysis.status == "api_unavailable"

    @pytest.mark.asyncio
    async def test_successful_analysis(self):
        from kovrin.superwork.orchestrator import OrchestratorAgent

        api_response = json.dumps(
            {
                "summary": "Good progress",
                "focus_area": "Testing",
                "proposals": [
                    {
                        "title": "Add integration tests",
                        "description": "Test API endpoints",
                        "risk_level": "LOW",
                        "priority": 1,
                    }
                ],
            }
        )
        mock_message = MagicMock()
        mock_message.content = [MagicMock(text=api_response)]
        mock_client = MagicMock()
        mock_client.messages.create = AsyncMock(return_value=mock_message)

        orch = OrchestratorAgent(
            client=mock_client,
            context_injector=MagicMock(
                get_relevant_context=MagicMock(return_value="project context")
            ),
            metrics_tracker=MagicMock(
                snapshot=MagicMock(return_value=MetricsSnapshot(tasks_completed=5)),
                tasks_completed=5,
                tasks_failed=0,
                velocity=2.5,
            ),
        )
        analysis = await orch.analyze_and_propose()
        assert analysis.status == "ok"
        assert len(analysis.proposals) == 1
        assert analysis.proposals[0].title == "Add integration tests"
