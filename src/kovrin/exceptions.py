"""
Kovrin Custom Exceptions

Structured exception hierarchy for the Kovrin framework.
All Kovrin-specific exceptions inherit from KovrinError.

Exception hierarchy:
    KovrinError
    +-- ConstitutionalViolationError  (Layer 0 axiom violation — non-recoverable)
    +-- ScopeViolationError           (DCT scope exceeded)
    +-- SafetyBlockedError            (Critic pipeline rejected task)
    +-- ToolExecutionError            (Tool execution failure)
    +-- ProviderError                 (LLM provider failure)
    |   +-- ProviderUnavailableError  (Circuit breaker open)
    |   +-- ProviderTimeoutError      (Request timeout)
    +-- KovrinAPIError                (API layer error)
    +-- PipelineError                 (Pipeline orchestration error)
"""

from __future__ import annotations


class KovrinError(Exception):
    """Base exception for all Kovrin framework errors."""

    def __init__(self, message: str, details: dict | None = None):
        super().__init__(message)
        self.details = details or {}


class ConstitutionalViolationError(KovrinError):
    """Raised when a Layer 0 constitutional axiom is violated.

    This is non-recoverable — the task MUST NOT proceed.
    """

    def __init__(self, axiom_name: str, evidence: str, details: dict | None = None):
        super().__init__(
            f"Constitutional violation: {axiom_name} — {evidence}",
            details={"axiom_name": axiom_name, "evidence": evidence, **(details or {})},
        )
        self.axiom_name = axiom_name
        self.evidence = evidence


class ScopeViolationError(KovrinError):
    """Raised when an operation exceeds its DCT (Delegation Capability Token) scope.

    Scope can only narrow, never widen. This error indicates an attempt
    to exceed authorized boundaries.
    """

    def __init__(self, message: str, scope_details: dict | None = None):
        super().__init__(message, details=scope_details)


class SafetyBlockedError(KovrinError):
    """Raised when the critic pipeline rejects a task or tool call.

    Contains information about which critics failed and why.
    """

    def __init__(
        self, message: str, failed_critics: list[str] | None = None, details: dict | None = None
    ):
        super().__init__(
            message,
            details={"failed_critics": failed_critics or [], **(details or {})},
        )
        self.failed_critics = failed_critics or []


class ToolExecutionError(KovrinError):
    """Raised when a tool execution fails.

    Includes tool name and input for debugging.
    """

    def __init__(self, tool_name: str, message: str, details: dict | None = None):
        super().__init__(
            f"Tool '{tool_name}' execution failed: {message}",
            details={"tool_name": tool_name, **(details or {})},
        )
        self.tool_name = tool_name


class ProviderError(KovrinError):
    """Base exception for LLM provider errors."""

    def __init__(self, provider_name: str, message: str, details: dict | None = None):
        super().__init__(
            f"Provider '{provider_name}' error: {message}",
            details={"provider_name": provider_name, **(details or {})},
        )
        self.provider_name = provider_name


class ProviderUnavailableError(ProviderError):
    """Raised when a provider is unavailable (circuit breaker open)."""

    pass


class ProviderTimeoutError(ProviderError):
    """Raised when a provider request times out."""

    pass


class KovrinAPIError(KovrinError):
    """Raised for API layer errors (FastAPI endpoints)."""

    def __init__(self, message: str, status_code: int = 500, details: dict | None = None):
        super().__init__(
            message,
            details={"status_code": status_code, **(details or {})},
        )
        self.status_code = status_code


class PipelineError(KovrinError):
    """Raised for pipeline orchestration errors."""

    def __init__(self, intent_id: str, message: str, details: dict | None = None):
        super().__init__(
            f"Pipeline '{intent_id}' error: {message}",
            details={"intent_id": intent_id, **(details or {})},
        )
        self.intent_id = intent_id


class ChainError(PipelineError):
    """Raised for session chain orchestration errors.

    Includes chain_id and step_index for debugging which step failed.
    """

    def __init__(
        self,
        chain_id: str,
        step_index: int,
        message: str,
        details: dict | None = None,
    ):
        super().__init__(
            intent_id=chain_id,
            message=f"Step {step_index}: {message}",
            details={"chain_id": chain_id, "step_index": step_index, **(details or {})},
        )
        self.chain_id = chain_id
        self.step_index = step_index
