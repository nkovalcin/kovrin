"""Web search tool — search the web for information via Brave Search API.

Risk: LOW — read-only, no side effects.
Tier: FREE — idempotent, safe for parallel execution.

Uses Brave Search API (https://api.search.brave.com/).
Requires BRAVE_SEARCH_API_KEY environment variable.
Free tier: 2,000 queries/month. No credit card required.

Graceful degradation: if no API key is set, returns an error message
instead of failing silently. The safety routing and audit logging
work regardless of the backend availability.
"""

from __future__ import annotations

import json
import os
from urllib.error import HTTPError, URLError
from urllib.parse import quote_plus
from urllib.request import Request, urlopen

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool

BRAVE_API_URL = "https://api.search.brave.com/res/v1/web/search"
_REQUEST_TIMEOUT = 10  # seconds


def _get_api_key() -> str | None:
    """Read Brave Search API key from environment."""
    return os.environ.get("BRAVE_SEARCH_API_KEY")


async def _web_search(query: str, max_results: int = 5) -> str:
    """Search the web using Brave Search API.

    Returns formatted search results with titles, URLs, and descriptions.
    If BRAVE_SEARCH_API_KEY is not set, returns an error message.
    """
    import asyncio

    api_key = _get_api_key()
    if not api_key:
        return (
            "[Web Search Error] BRAVE_SEARCH_API_KEY environment variable not set.\n"
            "Get a free API key at https://api.search.brave.com/\n"
            "Free tier: 2,000 queries/month, no credit card required."
        )

    def _do_search() -> str:
        url = f"{BRAVE_API_URL}?q={quote_plus(query)}&count={min(max_results, 20)}"
        headers = {
            "Accept": "application/json",
            "Accept-Encoding": "gzip",
            "X-Subscription-Token": api_key,
        }
        req = Request(url, headers=headers)

        try:
            with urlopen(req, timeout=_REQUEST_TIMEOUT) as resp:  # noqa: S310
                raw = resp.read()
                # Handle gzip encoding
                if resp.headers.get("Content-Encoding") == "gzip":
                    import gzip

                    raw = gzip.decompress(raw)
                data = json.loads(raw.decode("utf-8"))
        except HTTPError as e:
            body = e.read().decode("utf-8", errors="replace")[:500]
            return f"[Web Search Error] HTTP {e.code}: {e.reason}\n{body}"
        except URLError as e:
            return f"[Web Search Error] Connection failed: {e.reason}"
        except Exception as e:
            return f"[Web Search Error] {type(e).__name__}: {e}"

        return _format_results(data, query)

    return await asyncio.get_event_loop().run_in_executor(None, _do_search)


def _format_results(data: dict, query: str) -> str:
    """Format Brave Search API response into readable text."""
    results = data.get("web", {}).get("results", [])

    if not results:
        # Check for special result types
        infobox = data.get("infobox")
        if infobox:
            return (
                f"## {infobox.get('title', 'Info')}\n"
                f"{infobox.get('long_desc', infobox.get('description', 'No description'))}\n"
                f"Source: {infobox.get('url', 'N/A')}"
            )
        return f"No results found for: '{query}'"

    parts = [f"## Web Search Results for: '{query}'\n"]

    for i, result in enumerate(results, 1):
        title = result.get("title", "Untitled")
        url = result.get("url", "")
        description = result.get("description", "No description available.")

        # Clean HTML tags from description
        description = _strip_html(description)

        parts.append(f"### {i}. {title}")
        parts.append(f"URL: {url}")
        parts.append(f"{description}\n")

    # Add knowledge graph / FAQ if available
    faq = data.get("faq", {}).get("results", [])
    if faq:
        parts.append("## Related Questions")
        for item in faq[:3]:
            q = item.get("question", "")
            a = _strip_html(item.get("answer", ""))
            if q and a:
                parts.append(f"**Q: {q}**\n{a}\n")

    # Add news results if available
    news = data.get("news", {}).get("results", [])
    if news:
        parts.append("## Recent News")
        for item in news[:3]:
            title = item.get("title", "")
            url = item.get("url", "")
            age = item.get("age", "")
            parts.append(f"- [{title}]({url}) ({age})")

    return "\n".join(parts)


def _strip_html(text: str) -> str:
    """Remove HTML tags from text."""
    import re

    clean = re.sub(r"<[^>]+>", "", text)
    return clean.strip()


WEB_SEARCH_TOOL = RegisteredTool(
    definition=ToolDefinition(
        name="web_search",
        description=(
            "Search the web for current information using Brave Search API. "
            "Returns search results with titles, URLs, and descriptions. "
            "Use this to find up-to-date information, research topics, "
            "verify facts, or discover recent news and developments."
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
                    "description": "Maximum number of results to return (default: 5, max: 20)",
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
