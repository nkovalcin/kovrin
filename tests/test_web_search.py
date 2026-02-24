"""Tests for the Brave Search web_search tool.

Tests both the stub behavior (no API key) and the formatting logic.
"""

import json
from unittest.mock import patch

import pytest

from kovrin.tools.builtin.web_search import (
    WEB_SEARCH_TOOL,
    _format_results,
    _get_api_key,
    _strip_html,
    _web_search,
)
from kovrin.core.models import RiskLevel, SpeculationTier


class TestWebSearchToolConfig:
    """Verify tool registration and risk profile."""

    def test_tool_name(self):
        assert WEB_SEARCH_TOOL.name == "web_search"

    def test_risk_level(self):
        assert WEB_SEARCH_TOOL.risk_level == RiskLevel.LOW

    def test_speculation_tier(self):
        assert WEB_SEARCH_TOOL.speculation_tier == SpeculationTier.FREE

    def test_max_calls(self):
        assert WEB_SEARCH_TOOL.risk_profile.max_calls_per_task == 20

    def test_scope_tags(self):
        assert "network" in WEB_SEARCH_TOOL.risk_profile.scope_tags
        assert "read_only" in WEB_SEARCH_TOOL.risk_profile.scope_tags

    def test_input_schema_has_query(self):
        schema = WEB_SEARCH_TOOL.definition.input_schema
        assert "query" in schema["properties"]
        assert "query" in schema["required"]


class TestWebSearchNoApiKey:
    """Test graceful degradation when no API key is set."""

    @pytest.mark.asyncio
    async def test_no_api_key_returns_error(self):
        """Without BRAVE_SEARCH_API_KEY, should return helpful error."""
        with patch.dict("os.environ", {}, clear=True):
            # Also clear BRAVE_SEARCH_API_KEY specifically
            import os
            env = os.environ.copy()
            env.pop("BRAVE_SEARCH_API_KEY", None)
            with patch.dict("os.environ", env, clear=True):
                result = await _web_search("test query")
                assert "BRAVE_SEARCH_API_KEY" in result
                assert "api.search.brave.com" in result

    def test_get_api_key_returns_none(self):
        with patch.dict("os.environ", {}, clear=True):
            import os
            env = os.environ.copy()
            env.pop("BRAVE_SEARCH_API_KEY", None)
            with patch.dict("os.environ", env, clear=True):
                assert _get_api_key() is None

    def test_get_api_key_returns_value(self):
        with patch.dict("os.environ", {"BRAVE_SEARCH_API_KEY": "test-key-123"}):
            assert _get_api_key() == "test-key-123"


class TestFormatResults:
    """Test result formatting logic."""

    def test_format_web_results(self):
        data = {
            "web": {
                "results": [
                    {
                        "title": "Python 3.13 Features",
                        "url": "https://python.org/3.13",
                        "description": "New features in <b>Python 3.13</b>",
                    },
                    {
                        "title": "Python Release Notes",
                        "url": "https://docs.python.org/release",
                        "description": "Official release notes",
                    },
                ]
            }
        }
        result = _format_results(data, "Python 3.13")
        assert "Python 3.13 Features" in result
        assert "https://python.org/3.13" in result
        assert "New features in Python 3.13" in result  # HTML stripped
        assert "<b>" not in result  # No HTML tags

    def test_format_no_results(self):
        data = {"web": {"results": []}}
        result = _format_results(data, "nonexistent query")
        assert "No results found" in result

    def test_format_with_faq(self):
        data = {
            "web": {
                "results": [
                    {"title": "Test", "url": "https://test.com", "description": "desc"},
                ]
            },
            "faq": {
                "results": [
                    {
                        "question": "What is Python?",
                        "answer": "Python is a <em>programming language</em>.",
                    }
                ]
            },
        }
        result = _format_results(data, "Python")
        assert "What is Python?" in result
        assert "programming language" in result
        assert "<em>" not in result

    def test_format_with_news(self):
        data = {
            "web": {
                "results": [
                    {"title": "Test", "url": "https://test.com", "description": "desc"},
                ]
            },
            "news": {
                "results": [
                    {
                        "title": "Breaking News",
                        "url": "https://news.com/breaking",
                        "age": "2 hours ago",
                    }
                ]
            },
        }
        result = _format_results(data, "news query")
        assert "Recent News" in result
        assert "Breaking News" in result

    def test_format_infobox_fallback(self):
        data = {
            "web": {"results": []},
            "infobox": {
                "title": "Python (programming language)",
                "description": "A high-level language",
                "long_desc": "Python is a high-level, general-purpose programming language.",
                "url": "https://en.wikipedia.org/wiki/Python",
            },
        }
        result = _format_results(data, "Python")
        assert "Python (programming language)" in result
        assert "high-level" in result


class TestStripHtml:
    def test_strip_basic_tags(self):
        assert _strip_html("<b>bold</b>") == "bold"

    def test_strip_nested_tags(self):
        assert _strip_html("<p><em>hello</em></p>") == "hello"

    def test_no_tags(self):
        assert _strip_html("plain text") == "plain text"

    def test_empty_string(self):
        assert _strip_html("") == ""

    def test_self_closing_tags(self):
        assert _strip_html("line<br/>break") == "linebreak"
