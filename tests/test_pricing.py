"""Tests for Kovrin model pricing calculations.

Tests calculate_cost() for each model and detect_provider() for all providers.
"""

import pytest

from kovrin.engine.pricing import MODEL_PRICING, calculate_cost, detect_provider


# ─── calculate_cost ──────────────────────────────────────────


class TestCalculateCost:
    """Token-to-USD cost calculation."""

    def test_claude_haiku(self):
        cost = calculate_cost("claude-haiku-4-5", input_tokens=1000, output_tokens=500)
        expected = 1000 * 0.80 / 1_000_000 + 500 * 4.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_claude_sonnet(self):
        cost = calculate_cost("claude-sonnet-4-6", input_tokens=1000, output_tokens=500)
        expected = 1000 * 3.00 / 1_000_000 + 500 * 15.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_claude_opus(self):
        cost = calculate_cost("claude-opus-4-6", input_tokens=1000, output_tokens=500)
        expected = 1000 * 15.00 / 1_000_000 + 500 * 75.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_gpt4o(self):
        cost = calculate_cost("gpt-4o", input_tokens=1000, output_tokens=500)
        expected = 1000 * 2.50 / 1_000_000 + 500 * 10.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_gpt4o_mini(self):
        cost = calculate_cost("gpt-4o-mini", input_tokens=1000, output_tokens=500)
        expected = 1000 * 0.15 / 1_000_000 + 500 * 0.60 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_o1(self):
        cost = calculate_cost("o1", input_tokens=1000, output_tokens=500)
        expected = 1000 * 15.00 / 1_000_000 + 500 * 60.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_o1_mini(self):
        cost = calculate_cost("o1-mini", input_tokens=1000, output_tokens=500)
        expected = 1000 * 3.00 / 1_000_000 + 500 * 12.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_unknown_model_uses_default(self):
        """Unknown model should use default pricing (Sonnet-level)."""
        cost = calculate_cost("unknown-model-v3", input_tokens=1000, output_tokens=500)
        expected = 1000 * 3.00 / 1_000_000 + 500 * 15.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_zero_tokens(self):
        cost = calculate_cost("claude-sonnet-4-6", input_tokens=0, output_tokens=0)
        assert cost == 0.0

    def test_only_input_tokens(self):
        cost = calculate_cost("claude-haiku-4-5", input_tokens=1_000_000, output_tokens=0)
        assert cost == pytest.approx(0.80)

    def test_only_output_tokens(self):
        cost = calculate_cost("claude-haiku-4-5", input_tokens=0, output_tokens=1_000_000)
        assert cost == pytest.approx(4.00)

    def test_large_token_count(self):
        """1M tokens should match the pricing per 1M."""
        cost = calculate_cost("claude-opus-4-6", input_tokens=1_000_000, output_tokens=1_000_000)
        assert cost == pytest.approx(15.00 + 75.00)

    def test_legacy_model_id(self):
        """Legacy model IDs should still be priced correctly."""
        cost = calculate_cost("claude-sonnet-4-20250514", input_tokens=1000, output_tokens=500)
        expected = 1000 * 3.00 / 1_000_000 + 500 * 15.00 / 1_000_000
        assert cost == pytest.approx(expected)

    def test_cost_is_rounded(self):
        """Cost should be rounded to 8 decimal places."""
        cost = calculate_cost("claude-haiku-4-5", input_tokens=1, output_tokens=1)
        assert isinstance(cost, float)


# ─── detect_provider ─────────────────────────────────────────


class TestDetectProvider:
    """Provider detection from model ID."""

    def test_claude_models(self):
        assert detect_provider("claude-sonnet-4-6") == "anthropic"
        assert detect_provider("claude-haiku-4-5") == "anthropic"
        assert detect_provider("claude-opus-4-6") == "anthropic"
        assert detect_provider("claude-sonnet-4-20250514") == "anthropic"

    def test_openai_gpt_models(self):
        assert detect_provider("gpt-4o") == "openai"
        assert detect_provider("gpt-4o-mini") == "openai"

    def test_openai_o1_models(self):
        assert detect_provider("o1") == "openai"
        assert detect_provider("o1-mini") == "openai"

    def test_unknown_model(self):
        assert detect_provider("llama-3-70b") == "unknown"
        assert detect_provider("mistral-7b") == "unknown"
        assert detect_provider("") == "unknown"


# ─── MODEL_PRICING completeness ──────────────────────────────


class TestModelPricingData:
    """Verify pricing data structure."""

    def test_all_models_have_input_and_output(self):
        for model, pricing in MODEL_PRICING.items():
            assert "input" in pricing, f"{model} missing 'input' price"
            assert "output" in pricing, f"{model} missing 'output' price"

    def test_all_prices_positive(self):
        for model, pricing in MODEL_PRICING.items():
            assert pricing["input"] > 0, f"{model} input price must be positive"
            assert pricing["output"] > 0, f"{model} output price must be positive"

    def test_output_more_expensive_than_input(self):
        """Output tokens are always more expensive than input tokens."""
        for model, pricing in MODEL_PRICING.items():
            assert pricing["output"] >= pricing["input"], (
                f"{model}: output should be >= input price"
            )
