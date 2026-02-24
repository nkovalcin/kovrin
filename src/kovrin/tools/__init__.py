"""
Kovrin Safety-Gated Tool Execution System

Every tool call from an AI agent is routed through the Kovrin
safety pipeline before execution:

    Agent → Claude API (tool_use) → SafeToolRouter → RiskRouter → Execute

Components:
- ToolRegistry: Central registry for all tools with safety metadata
- SafeToolRouter: Routes tool calls through Constitutional Core + RiskRouter
- SandboxedExecutor: Isolated execution environment
- RegisteredTool: Tool + safety profile + handler
- Built-in tools: calculator, datetime, json, code_exec, web_search, http, file ops
"""

from kovrin.tools.models import (
    ToolCallDecision,
    ToolCallRequest,
    ToolCallTrace,
    ToolCategory,
    ToolRiskProfile,
)
from kovrin.tools.registry import RegisteredTool, ToolRegistry
from kovrin.tools.router import SafeToolRouter
from kovrin.tools.sandbox import SandboxConfig, SandboxedExecutor

__all__ = [
    "RegisteredTool",
    "SafeToolRouter",
    "SandboxConfig",
    "SandboxedExecutor",
    "ToolCallDecision",
    "ToolCallRequest",
    "ToolCallTrace",
    "ToolCategory",
    "ToolRegistry",
    "ToolRiskProfile",
]
