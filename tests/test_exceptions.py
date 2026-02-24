"""Tests for Kovrin custom exceptions.

Covers the exception hierarchy and structured error information.
"""

import pytest

from kovrin.exceptions import (
    ConstitutionalViolationError,
    KovrinAPIError,
    KovrinError,
    PipelineError,
    ProviderError,
    ProviderTimeoutError,
    ProviderUnavailableError,
    SafetyBlockedError,
    ScopeViolationError,
    ToolExecutionError,
)


class TestKovrinError:
    def test_base_error(self):
        err = KovrinError("something went wrong")
        assert str(err) == "something went wrong"
        assert err.details == {}

    def test_base_error_with_details(self):
        err = KovrinError("failed", details={"key": "value"})
        assert err.details == {"key": "value"}

    def test_is_exception(self):
        assert issubclass(KovrinError, Exception)


class TestConstitutionalViolationError:
    def test_creation(self):
        err = ConstitutionalViolationError("Harm Floor", "Expected harm exceeds threshold")
        assert "Harm Floor" in str(err)
        assert err.axiom_name == "Harm Floor"
        assert err.evidence == "Expected harm exceeds threshold"

    def test_inherits_kovrin_error(self):
        assert issubclass(ConstitutionalViolationError, KovrinError)

    def test_details_include_axiom(self):
        err = ConstitutionalViolationError("Scope Limit", "Exceeded boundaries")
        assert err.details["axiom_name"] == "Scope Limit"
        assert err.details["evidence"] == "Exceeded boundaries"


class TestScopeViolationError:
    def test_creation(self):
        err = ScopeViolationError("Agent exceeded read_only scope")
        assert "read_only" in str(err)

    def test_inherits_kovrin_error(self):
        assert issubclass(ScopeViolationError, KovrinError)


class TestSafetyBlockedError:
    def test_with_failed_critics(self):
        err = SafetyBlockedError(
            "Task blocked by safety pipeline",
            failed_critics=["SafetyCritic", "FeasibilityCritic"],
        )
        assert err.failed_critics == ["SafetyCritic", "FeasibilityCritic"]
        assert "SafetyCritic" in err.details["failed_critics"]

    def test_no_critics(self):
        err = SafetyBlockedError("Blocked")
        assert err.failed_critics == []


class TestToolExecutionError:
    def test_creation(self):
        err = ToolExecutionError("web_search", "API key not set")
        assert "web_search" in str(err)
        assert err.tool_name == "web_search"

    def test_details(self):
        err = ToolExecutionError("code_execution", "Timeout", details={"timeout": 30})
        assert err.details["tool_name"] == "code_execution"
        assert err.details["timeout"] == 30


class TestProviderErrors:
    def test_provider_error(self):
        err = ProviderError("Claude", "Rate limited")
        assert err.provider_name == "Claude"
        assert "Claude" in str(err)

    def test_unavailable_inherits(self):
        err = ProviderUnavailableError("Claude", "Circuit breaker open")
        assert isinstance(err, ProviderError)
        assert isinstance(err, KovrinError)

    def test_timeout_inherits(self):
        err = ProviderTimeoutError("OpenAI", "30s timeout exceeded")
        assert isinstance(err, ProviderError)


class TestKovrinAPIError:
    def test_with_status_code(self):
        err = KovrinAPIError("Not found", status_code=404)
        assert err.status_code == 404
        assert err.details["status_code"] == 404

    def test_default_status_code(self):
        err = KovrinAPIError("Internal error")
        assert err.status_code == 500


class TestPipelineError:
    def test_creation(self):
        err = PipelineError("intent-123", "All tasks rejected")
        assert err.intent_id == "intent-123"
        assert "intent-123" in str(err)


class TestHierarchy:
    """Verify the full exception hierarchy."""

    def test_all_inherit_from_kovrin_error(self):
        errors = [
            ConstitutionalViolationError("a", "b"),
            ScopeViolationError("x"),
            SafetyBlockedError("y"),
            ToolExecutionError("z", "msg"),
            ProviderError("p", "msg"),
            ProviderUnavailableError("p", "msg"),
            ProviderTimeoutError("p", "msg"),
            KovrinAPIError("msg"),
            PipelineError("id", "msg"),
        ]
        for err in errors:
            assert isinstance(err, KovrinError), f"{type(err).__name__} should inherit from KovrinError"
            assert isinstance(err, Exception)

    def test_can_catch_all_with_kovrin_error(self):
        """All Kovrin exceptions should be catchable with KovrinError."""
        with pytest.raises(KovrinError):
            raise ConstitutionalViolationError("test", "test")

        with pytest.raises(KovrinError):
            raise ToolExecutionError("tool", "msg")

        with pytest.raises(KovrinError):
            raise ProviderUnavailableError("p", "msg")
