"""
Kovrin Structured Logging

Provides a configured logger for the Kovrin framework using stdlib logging
with structured context. No external dependencies required.

Usage:
    from kovrin.logging import get_logger

    logger = get_logger("kovrin.engine")
    logger.info("Task executed", extra={"task_id": "t-123", "risk": "HIGH"})

For production, configure with JSON output:
    from kovrin.logging import configure_logging
    configure_logging(json_output=True, level="INFO")
"""

from __future__ import annotations

import json
import logging
import sys
from datetime import datetime, timezone
from typing import Any


class KovrinFormatter(logging.Formatter):
    """Structured log formatter for Kovrin.

    Outputs either human-readable or JSON format depending on configuration.
    """

    def __init__(self, json_output: bool = False):
        super().__init__()
        self._json_output = json_output

    def format(self, record: logging.LogRecord) -> str:
        # Base log data
        log_data: dict[str, Any] = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "level": record.levelname,
            "logger": record.name,
            "message": record.getMessage(),
        }

        # Add extra fields (task_id, intent_id, risk_level, etc.)
        for key in ("task_id", "intent_id", "risk_level", "event_type",
                     "tool_name", "provider", "action", "duration_ms"):
            value = getattr(record, key, None)
            if value is not None:
                log_data[key] = value

        # Include any extra dict passed via extra={}
        extra = getattr(record, "_extra", None)
        if extra and isinstance(extra, dict):
            log_data.update(extra)

        if self._json_output:
            return json.dumps(log_data, default=str)

        # Human-readable format
        extra_str = ""
        extra_keys = {k: v for k, v in log_data.items()
                      if k not in ("timestamp", "level", "logger", "message")}
        if extra_keys:
            extra_str = " | " + " ".join(f"{k}={v}" for k, v in extra_keys.items())

        return f"[{log_data['timestamp']}] {record.levelname:8s} {record.name}: {record.getMessage()}{extra_str}"


def configure_logging(
    level: str = "INFO",
    json_output: bool = False,
) -> None:
    """Configure Kovrin logging.

    Args:
        level: Log level (DEBUG, INFO, WARNING, ERROR, CRITICAL).
        json_output: If True, output JSON format (for production/observability).
    """
    root_logger = logging.getLogger("kovrin")
    root_logger.setLevel(getattr(logging, level.upper(), logging.INFO))

    # Remove existing handlers
    root_logger.handlers.clear()

    handler = logging.StreamHandler(sys.stderr)
    handler.setFormatter(KovrinFormatter(json_output=json_output))
    root_logger.addHandler(handler)

    # Prevent propagation to root logger
    root_logger.propagate = False


def get_logger(name: str = "kovrin") -> logging.Logger:
    """Get a Kovrin logger instance.

    Args:
        name: Logger name (usually module path like "kovrin.engine").

    Returns:
        Configured Logger instance.
    """
    return logging.getLogger(name)


# Auto-configure with sensible defaults on import
configure_logging()
