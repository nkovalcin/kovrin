"""Web search tool — search the web for information.

Risk: LOW — read-only, no side effects.
Tier: FREE — idempotent, safe for parallel execution.

NOTE: This is a stub implementation. In production, integrate with
a search API (Brave, Serper, Tavily, etc.). The safety routing and
audit logging work regardless of the backend implementation.
"""

from __future__ import annotations

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool


async def _web_search(query: str, max_results: int = 5) -> str:
    """Search the web for information.

    Stub: Returns a message indicating search API integration needed.
    Replace this with actual API calls (Brave Search, Serper, Tavily, etc.).
    """
    # TODO: Integrate with a search API provider
    return (
        f"[Web Search] Query: '{query}' (max_results={max_results})\n"
        f"Search API not configured. To enable web search, set KOVRIN_SEARCH_API_KEY "
        f"and configure a search provider (Brave, Serper, or Tavily).\n"
        f"The safety routing and audit trail are active for this tool."
    )


WEB_SEARCH_TOOL = RegisteredTool(
    definition=ToolDefinition(
        name="web_search",
        description=(
            "Search the web for information. Returns search results with "
            "titles, URLs, and snippets. Use this to find current information, "
            "research topics, or verify facts."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "query": {
                    "type": "string",
                    "description": "The search query",
                },
                "max_results": {
                    "type": "integer",
                    "description": "Maximum number of results to return (default: 5)",
                    "default": 5,
                },
            },
            "required": ["query"],
        },
    ),
    risk_profile=ToolRiskProfile(
        risk_level=RiskLevel.LOW,
        speculation_tier=SpeculationTier.FREE,
        category=ToolCategory.NETWORK,
        scope_tags=["network", "read_only"],
        max_calls_per_task=20,
    ),
    handler=_web_search,
)
