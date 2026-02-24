"""File operations tools — sandboxed file read/write.

Two separate tools with different risk profiles:
- file_read: LOW risk, FREE tier (read-only, no side effects)
- file_write: MEDIUM risk, GUARDED tier (creates/modifies files)

Both validate paths against the sandbox to prevent access to
sensitive system directories.
"""

from __future__ import annotations

from pathlib import Path

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool
from kovrin.tools.sandbox import SandboxedExecutor, SandboxConfig

_sandbox = SandboxedExecutor()


def _file_read(path: str, max_lines: int = 200) -> str:
    """Read a file's contents with path validation."""
    valid, reason = _sandbox.validate_path(path)
    if not valid:
        return f"[BLOCKED] {reason}"

    try:
        p = Path(path)
        if not p.exists():
            return f"File not found: {path}"
        if not p.is_file():
            return f"Not a file: {path}"
        if p.stat().st_size > 1_048_576:  # 1MB limit
            return f"File too large ({p.stat().st_size} bytes). Max 1MB."

        lines = p.read_text(encoding="utf-8", errors="replace").splitlines()
        if len(lines) > max_lines:
            content = "\n".join(lines[:max_lines])
            return f"{content}\n[TRUNCATED at {max_lines} lines, total {len(lines)}]"
        return "\n".join(lines)
    except PermissionError:
        return f"Permission denied: {path}"
    except Exception as e:
        return f"Read error: {type(e).__name__}: {e}"


def _file_write(path: str, content: str) -> str:
    """Write content to a file with path validation."""
    valid, reason = _sandbox.validate_path(path)
    if not valid:
        return f"[BLOCKED] {reason}"

    try:
        p = Path(path)
        # Create parent directories if needed
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
        return f"Written {len(content)} bytes to {path}"
    except PermissionError:
        return f"Permission denied: {path}"
    except Exception as e:
        return f"Write error: {type(e).__name__}: {e}"


FILE_READ_TOOL = RegisteredTool(
    definition=ToolDefinition(
        name="file_read",
        description=(
            "Read the contents of a file. Returns the file text content. "
            "Access to system directories (/etc, /var, etc.) is blocked."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "path": {
                    "type": "string",
                    "description": "Absolute or relative path to the file",
                },
                "max_lines": {
                    "type": "integer",
                    "description": "Maximum lines to read (default: 200)",
                    "default": 200,
                },
            },
            "required": ["path"],
        },
    ),
    risk_profile=ToolRiskProfile(
        risk_level=RiskLevel.LOW,
        speculation_tier=SpeculationTier.FREE,
        category=ToolCategory.FILE_SYSTEM,
        scope_tags=["filesystem", "read_only"],
        max_calls_per_task=20,
    ),
    handler=_file_read,
)


FILE_WRITE_TOOL = RegisteredTool(
    definition=ToolDefinition(
        name="file_write",
        description=(
            "Write content to a file. Creates parent directories if needed. "
            "Access to system directories (/etc, /var, etc.) is blocked."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "path": {
                    "type": "string",
                    "description": "Absolute or relative path for the file",
                },
                "content": {
                    "type": "string",
                    "description": "Content to write to the file",
                },
            },
            "required": ["path", "content"],
        },
    ),
    risk_profile=ToolRiskProfile(
        risk_level=RiskLevel.MEDIUM,
        speculation_tier=SpeculationTier.GUARDED,
        category=ToolCategory.FILE_SYSTEM,
        scope_tags=["filesystem"],
        max_calls_per_task=10,
    ),
    handler=_file_write,
)
