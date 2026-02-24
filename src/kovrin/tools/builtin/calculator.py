"""Calculator tool — safe math expression evaluation."""

import math

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool


def _calculator(expression: str) -> str:
    """Evaluate a mathematical expression safely."""
    allowed_names = {
        "abs": abs, "round": round, "min": min, "max": max,
        "sum": sum, "pow": pow, "len": len,
        "sqrt": math.sqrt, "log": math.log, "log10": math.log10,
        "sin": math.sin, "cos": math.cos, "tan": math.tan,
        "pi": math.pi, "e": math.e,
        "ceil": math.ceil, "floor": math.floor,
    }
    try:
        result = eval(expression, {"__builtins__": {}}, allowed_names)  # noqa: S307
        return str(result)
    except Exception as e:
        return f"Calculation error: {e}"


CALCULATOR_TOOL = RegisteredTool(
    definition=ToolDefinition(
        name="calculator",
        description="Evaluate a mathematical expression. Supports arithmetic, sqrt, log, trig.",
        input_schema={
            "type": "object",
            "properties": {
                "expression": {
                    "type": "string",
                    "description": "Math expression to evaluate (e.g., 'sqrt(144) + 2 * 3')",
                },
            },
            "required": ["expression"],
        },
    ),
    risk_profile=ToolRiskProfile(
        risk_level=RiskLevel.LOW,
        speculation_tier=SpeculationTier.FREE,
        category=ToolCategory.COMPUTATION,
        scope_tags=["computation", "read_only"],
        max_calls_per_task=50,
    ),
    handler=_calculator,
)
