"""Tests for Kovrin Model Pricing.

Covers calculate_cost() and detect_provider() for all supported models.
"""

import pytest

from kovrin.engine.pricing import MODEL_PRICING, calculate_cost, detect_provider


class TestCalculateCost:
    """Tests for calculate_cost()."""

    def test_haiku_cost(self):
        """Haiku should use $0.80/$4.00 per 1M tokens."""
        cost = calculate_cost("claude-haiku-4-5", 1_000_000, 1_000_000)
        assert cost == pytest.approx(0.80 + 4.00)

    def test_sonnet_cost(self):
        """Sonnet should use $3.00/$15.00 per 1M tokens."""
        cost = calculate_cost("claude-sonnet-4-6", 1_000_000, 1_000_000)
        assert cost == pytest.approx(3.00 + 15.00)

    def test_opus_cost(self):
        """Opus should use $15.00/$75.00 per 1M tokens."""
        cost = calculate_cost("claude-opus-4-6", 1_000_000, 1_000_000)
        assert cost == pytest.approx(15.00 + 75.00)

    def test_gpt4o_cost(self):
        """GPT-4o should use $2.50/$10.00 per 1M tokens."""
        cost = calculate_cost("gpt-4o", 1_000_000, 1_000_000)
        assert cost == pytest.approx(2.50 + 10.00)

    def test_gpt4o_mini_cost(self):
        """GPT-4o-mini should use $0.15/$0.60 per 1M tokens."""
        cost = calculate_cost("gpt-4o-mini", 1_000_000, 1_000_000)
        assert cost == pytest.approx(0.15 + 0.60)

    def test_o1_cost(self):
        """O1 should use $15.00/$60.00 per 1M tokens."""
        cost = calculate_cost("o1", 1_000_000, 1_000_000)
        assert cost == pytest.approx(15.00 + 60.00)

    def test_zero_tokens(self):
        """Zero tokens should cost nothing."""
        assert calculate_cost("claude-sonnet-4-6", 0, 0) == 0.0

    def test_input_only(self):
        """Output-only cost calculation."""
        cost = calculate_cost("claude-haiku-4-5", 1_000, 0)
        expected = 1_000 * 0.80 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_output_only(self):
        """Output-only cost calculation."""
        cost = calculate_cost("claude-haiku-4-5", 0, 1_000)
        expected = 1_000 * 4.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_unknown_model_uses_default(self):
        """Unknown models should use default pricing ($3/$15)."""
        cost = calculate_cost("some-unknown-model", 1_000_000, 1_000_000)
        assert cost == pytest.approx(3.00 + 15.00)

    def test_large_token_count(self):
        """Large token counts should calculate correctly."""
        cost = calculate_cost("claude-haiku-4-5", 10_000_000, 5_000_000)
        expected = 10_000_000 * 0.80 / 1_000_000 + 5_000_000 * 4.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_small_token_count(self):
        """Single token should give a tiny but non-zero cost."""
        cost = calculate_cost("claude-sonnet-4-6", 1, 1)
        assert cost > 0
        assert cost < 0.001

    def test_legacy_model_ids(self):
        """Legacy Claude model IDs should be recognized."""
        cost1 = calculate_cost("claude-sonnet-4-20250514", 1000, 1000)
        cost2 = calculate_cost("claude-sonnet-4-6", 1000, 1000)
        # Same pricing — both Sonnet
        assert cost1 == pytest.approx(cost2)

    def test_all_models_in_pricing_table(self):
        """All models in MODEL_PRICING should have input and output keys."""
        for model, pricing in MODEL_PRICING.items():
            assert "input" in pricing, f"{model} missing input pricing"
            assert "output" in pricing, f"{model} missing output pricing"
            assert pricing["input"] >= 0
            assert pricing["output"] >= 0


class TestDetectProvider:
    """Tests for detect_provider()."""

    def test_claude_models(self):
        assert detect_provider("claude-sonnet-4-6") == "anthropic"
        assert detect_provider("claude-haiku-4-5") == "anthropic"
        assert detect_provider("claude-opus-4-6") == "anthropic"

    def test_openai_gpt_models(self):
        assert detect_provider("gpt-4o") == "openai"
        assert detect_provider("gpt-4o-mini") == "openai"

    def test_openai_o1_models(self):
        assert detect_provider("o1") == "openai"
        assert detect_provider("o1-mini") == "openai"

    def test_unknown_model(self):
        assert detect_provider("llama-3-70b") == "unknown"
        assert detect_provider("mistral-7b") == "unknown"
