"""Tests for LATTICE main orchestrator."""

import pytest

from kovrin.intent.schema import IntentV2, Performative, SemanticFrame


class TestIntentV2:
    def test_simple_creation(self):
        intent = IntentV2.simple(
            description="Analyze expenses",
            constraints=["No layoffs"],
            context={"budget": 15000},
        )
        assert intent.description == "Analyze expenses"
        assert len(intent.constraints) == 1
        assert intent.context["budget"] == 15000
        assert intent.performative == Performative.REQUEST

    def test_structured_creation(self):
        intent = IntentV2.structured(
            description="Optimize infrastructure costs",
            performative=Performative.REQUEST,
            frame=SemanticFrame.OPTIMIZATION,
            constraints=["Keep SLA above 99.9%"],
            game="devops",
            expected_state="costs_optimized",
        )
        assert intent.frame == SemanticFrame.OPTIMIZATION
        assert intent.language_game is not None
        assert intent.language_game.game == "devops"
        assert len(intent.expected_effects) == 1
        assert intent.expected_effects[0].state == "costs_optimized"

    def test_intent_has_uuid(self):
        intent = IntentV2.simple(description="Test")
        assert intent.id is not None
        assert len(intent.id) > 0

    def test_intent_has_timestamp(self):
        intent = IntentV2.simple(description="Test")
        assert intent.created_at is not None

    def test_backward_compat_alias(self):
        from kovrin.intent.schema import Intent
        assert Intent is IntentV2

    def test_serialization_roundtrip(self):
        intent = IntentV2.simple(
            description="Test intent",
            constraints=["C1", "C2"],
        )
        data = intent.model_dump()
        restored = IntentV2.model_validate(data)
        assert restored.description == intent.description
        assert restored.constraints == intent.constraints
