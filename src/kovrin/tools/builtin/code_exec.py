"""Code execution tool — sandboxed Python execution.

Risk: HIGH — code execution is inherently dangerous.
Tier: GUARDED — can checkpoint/rollback via sandbox isolation.
"""

from __future__ import annotations

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool
from kovrin.tools.sandbox import SandboxConfig, SandboxedExecutor

# Shared sandbox executor for code execution
_sandbox = SandboxedExecutor(
    SandboxConfig(
        timeout_seconds=30.0,
        max_output_bytes=65536,
        network_allowed=False,
    )
)


async def _execute_code(code: str) -> str:
    """Execute Python code in a sandboxed subprocess."""
    return await _sandbox.execute_code(code)


CODE_EXEC_TOOL = RegisteredTool(
    definition=ToolDefinition(
        name="code_execution",
        description=(
            "Execute Python code in a sandboxed environment. "
            "The code runs in an isolated subprocess with no network access. "
            "Use this for data processing, calculations, text manipulation, etc. "
            "Returns stdout output or error messages."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "code": {
                    "type": "string",
                    "description": "Python code to execute",
                },
            },
            "required": ["code"],
        },
    ),
    risk_profile=ToolRiskProfile(
        risk_level=RiskLevel.HIGH,
        speculation_tier=SpeculationTier.GUARDED,
        category=ToolCategory.CODE_EXECUTION,
        scope_tags=["code_execution"],
        max_calls_per_task=5,
    ),
    handler=_execute_code,
)
