"""Tests for Kovrin structured logging."""

import json
import logging

import pytest

from kovrin.logging import KovrinFormatter, configure_logging, get_logger


class TestKovrinFormatter:
    def test_human_readable_format(self):
        formatter = KovrinFormatter(json_output=False)
        record = logging.LogRecord(
            name="kovrin.engine",
            level=logging.INFO,
            pathname="test.py",
            lineno=1,
            msg="Task executed",
            args=(),
            exc_info=None,
        )
        output = formatter.format(record)
        assert "kovrin.engine" in output
        assert "Task executed" in output
        assert "INFO" in output

    def test_json_format(self):
        formatter = KovrinFormatter(json_output=True)
        record = logging.LogRecord(
            name="kovrin.safety",
            level=logging.WARNING,
            pathname="test.py",
            lineno=1,
            msg="Risk elevated",
            args=(),
            exc_info=None,
        )
        output = formatter.format(record)
        data = json.loads(output)
        assert data["logger"] == "kovrin.safety"
        assert data["message"] == "Risk elevated"
        assert data["level"] == "WARNING"
        assert "timestamp" in data

    def test_extra_fields_in_human_format(self):
        formatter = KovrinFormatter(json_output=False)
        record = logging.LogRecord(
            name="kovrin",
            level=logging.INFO,
            pathname="test.py",
            lineno=1,
            msg="Tool called",
            args=(),
            exc_info=None,
        )
        record.tool_name = "web_search"  # type: ignore[attr-defined]
        record.risk_level = "LOW"  # type: ignore[attr-defined]
        output = formatter.format(record)
        assert "tool_name=web_search" in output
        assert "risk_level=LOW" in output


class TestGetLogger:
    def test_returns_logger(self):
        logger = get_logger("kovrin.test")
        assert isinstance(logger, logging.Logger)
        assert logger.name == "kovrin.test"

    def test_default_name(self):
        logger = get_logger()
        assert logger.name == "kovrin"


class TestConfigureLogging:
    def test_configure_info(self):
        configure_logging(level="INFO")
        logger = get_logger("kovrin")
        assert logger.level == logging.INFO

    def test_configure_debug(self):
        configure_logging(level="DEBUG")
        logger = get_logger("kovrin")
        assert logger.level == logging.DEBUG

    def test_configure_json(self):
        """JSON mode should use KovrinFormatter with json_output=True."""
        configure_logging(json_output=True)
        logger = get_logger("kovrin")
        assert len(logger.handlers) == 1
        formatter = logger.handlers[0].formatter
        assert isinstance(formatter, KovrinFormatter)
        assert formatter._json_output is True

        # Reset to human format
        configure_logging(json_output=False)
