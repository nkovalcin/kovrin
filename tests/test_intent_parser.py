"""Tests for LATTICE Intent Parser."""

import json

from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.intent.parser import IntentParser


class TestIntentParserParsing:
    """Unit tests for the response parsing logic (no API calls)."""

    def setup_method(self):
        self.parser = IntentParser(client=None)

    def test_parse_valid_response(self):
        response = json.dumps(
            [
                {
                    "id": "task_0",
                    "description": "Analyze expenses",
                    "risk_level": "LOW",
                    "speculation_tier": "FREE",
                    "dependencies": [],
                },
                {
                    "id": "task_1",
                    "description": "Generate report",
                    "risk_level": "MEDIUM",
                    "speculation_tier": "GUARDED",
                    "dependencies": ["task_0"],
                },
            ]
        )

        tasks = self.parser._parse_response(response, "intent-1")
        assert len(tasks) == 2
        assert tasks[0].id == "task_0"
        assert tasks[0].risk_level == RiskLevel.LOW
        assert tasks[1].dependencies == ["task_0"]
        assert tasks[1].speculation_tier == SpeculationTier.GUARDED

    def test_parse_with_surrounding_text(self):
        """Parser should extract JSON even with markdown wrapping."""
        response = """Here is the decomposition:
```json
[{"id": "task_0", "description": "Do something", "risk_level": "LOW", "speculation_tier": "FREE", "dependencies": []}]
```"""
        tasks = self.parser._parse_response(response, "intent-1")
        assert len(tasks) == 1
        assert tasks[0].description == "Do something"

    def test_parse_invalid_json_fallback(self):
        """Invalid JSON should create a single fallback task."""
        tasks = self.parser._parse_response("not json at all", "intent-1")
        assert len(tasks) == 1
        assert (
            "failed" in tasks[0].description.lower()
            or "single task" in tasks[0].description.lower()
        )
        assert tasks[0].risk_level == RiskLevel.MEDIUM

    def test_parse_empty_array(self):
        tasks = self.parser._parse_response("[]", "intent-1")
        assert len(tasks) == 0

    def test_parse_invalid_risk_level_defaults(self):
        response = json.dumps(
            [
                {
                    "id": "task_0",
                    "description": "Task with bad risk",
                    "risk_level": "INVALID",
                    "speculation_tier": "FREE",
                    "dependencies": [],
                }
            ]
        )
        tasks = self.parser._parse_response(response, "intent-1")
        assert tasks[0].risk_level == RiskLevel.LOW  # default

    def test_parse_missing_fields_uses_defaults(self):
        response = json.dumps([{"description": "Minimal task"}])
        tasks = self.parser._parse_response(response, "intent-1")
        assert len(tasks) == 1
        assert tasks[0].risk_level == RiskLevel.LOW
        assert tasks[0].speculation_tier == SpeculationTier.FREE

    def test_parent_intent_id_set(self):
        response = json.dumps(
            [
                {
                    "id": "task_0",
                    "description": "Test task",
                    "risk_level": "LOW",
                    "speculation_tier": "FREE",
                    "dependencies": [],
                }
            ]
        )
        tasks = self.parser._parse_response(response, "my-intent-id")
        assert tasks[0].parent_intent_id == "my-intent-id"
