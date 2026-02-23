"""
Session Watcher — Claude Code Session File Monitor

Watches ~/.claude/projects/ for JSONL session file changes using
the watchdog library. Emits TaskCompletionEvent via async callbacks,
following the same subscribe(callback) pattern as ImmutableTraceLog.

Bridges the watchdog thread to the asyncio event loop via
asyncio.run_coroutine_threadsafe.
"""

from __future__ import annotations

import asyncio
import json
import logging
from pathlib import Path
from typing import TYPE_CHECKING

from kovrin.superwork.models import TaskCompletionEvent

if TYPE_CHECKING:
    from collections.abc import Callable

logger = logging.getLogger(__name__)

CLAUDE_SESSIONS_PATH = Path.home() / ".claude" / "projects"


class SessionWatcher:
    """Monitors Claude Code session files for task completions.

    Uses the same subscribe(callback) pattern as ImmutableTraceLog
    and WatchdogAgent for consistency across the framework.
    """

    def __init__(
        self,
        project_path: str | Path,
        sessions_path: Path | None = None,
    ):
        """Initialize Session Watcher.

        Args:
            project_path: Path to the project being monitored.
            sessions_path: Override for Claude sessions directory.
                Defaults to ~/.claude/projects/.
        """
        self._project_path = Path(project_path).resolve()
        self._sessions_path = sessions_path or CLAUDE_SESSIONS_PATH
        self._subscribers: list[Callable] = []
        self._observer = None
        self._file_positions: dict[str, int] = {}
        self._loop: asyncio.AbstractEventLoop | None = None

    def subscribe(self, callback: Callable) -> None:
        """Register an async callback for TaskCompletionEvent.

        Args:
            callback: Async callable with signature (TaskCompletionEvent) -> None.
        """
        self._subscribers.append(callback)

    def unsubscribe(self, callback: Callable) -> None:
        """Remove a previously registered callback."""
        self._subscribers = [s for s in self._subscribers if s is not callback]

    async def start(self) -> None:
        """Start watching for session file changes.

        Requires the ``watchdog`` package (``pip install kovrin[superwork]``).
        """
        from watchdog.observers import Observer

        self._loop = asyncio.get_running_loop()
        self._observer = Observer()

        handler = _SessionFileHandler(self)
        watch_path = self._resolve_watch_path()

        if not watch_path.exists():
            watch_path.mkdir(parents=True, exist_ok=True)

        self._observer.schedule(handler, str(watch_path), recursive=True)
        self._observer.daemon = True
        self._observer.start()
        logger.info("SessionWatcher started on %s", watch_path)

    async def stop(self) -> None:
        """Stop the file watcher."""
        if self._observer:
            self._observer.stop()
            self._observer.join(timeout=5)
            self._observer = None
            logger.info("SessionWatcher stopped")

    @property
    def is_watching(self) -> bool:
        """Whether the watcher is currently active."""
        return self._observer is not None and self._observer.is_alive()

    def _resolve_watch_path(self) -> Path:
        """Find the project hash directory under ~/.claude/projects/.

        Claude Code hashes project paths into directory names like
        ``-Users-user-project``. We search for a matching directory
        or fall back to the root sessions path.
        """
        if not self._sessions_path.exists():
            return self._sessions_path

        # Try to find a directory that matches our project path
        project_slug = str(self._project_path).replace("/", "-")
        for d in self._sessions_path.iterdir():
            if d.is_dir() and project_slug in d.name:
                return d

        # Fallback: watch all sessions
        return self._sessions_path

    def _on_file_modified(self, file_path: str) -> None:
        """Called from watchdog thread when a file is modified.

        Bridges to the asyncio loop via run_coroutine_threadsafe.
        """
        if not file_path.endswith(".jsonl"):
            return

        new_lines = self._read_new_lines(file_path)
        if not new_lines:
            return

        events = self._parse_completions(new_lines, file_path)
        for event in events:
            if self._loop and not self._loop.is_closed():
                asyncio.run_coroutine_threadsafe(self._notify_subscribers(event), self._loop)

    def _read_new_lines(self, file_path: str) -> list[str]:
        """Read only new lines since last check (tail-follow pattern)."""
        pos = self._file_positions.get(file_path, 0)
        try:
            with open(file_path, encoding="utf-8", errors="replace") as f:
                f.seek(pos)
                lines = f.readlines()
                self._file_positions[file_path] = f.tell()
            return lines
        except OSError:
            return []

    def _parse_completions(self, lines: list[str], file_path: str) -> list[TaskCompletionEvent]:
        """Parse JSONL lines for task completion signals.

        Detects completion patterns in Claude Code session output:
        - ``type: "result"`` entries
        - ``stop_reason: "end_turn"`` on assistant messages
        """
        events: list[TaskCompletionEvent] = []
        for line in lines:
            line = line.strip()
            if not line:
                continue
            try:
                data = json.loads(line)
                if self._is_completion_signal(data):
                    events.append(
                        TaskCompletionEvent(
                            session_id=Path(file_path).stem,
                            project_path=str(self._project_path),
                            completed_task=self._extract_task_description(data),
                            output_summary=self._extract_output(data),
                            files_changed=self._extract_files(data),
                            errors=self._extract_errors(data),
                        )
                    )
            except (json.JSONDecodeError, KeyError):
                continue
        return events

    @staticmethod
    def _is_completion_signal(data: dict) -> bool:
        """Detect if a JSONL entry signals task completion."""
        if data.get("type") == "result":
            return True
        return bool(data.get("type") == "assistant" and data.get("stop_reason") == "end_turn")

    @staticmethod
    def _extract_task_description(data: dict) -> str:
        """Extract a human-readable task description from the entry."""
        # Try common fields
        if "summary" in data:
            return str(data["summary"])[:200]
        content = data.get("content", "")
        if isinstance(content, list) and content:
            first = content[0]
            if isinstance(first, dict):
                return str(first.get("text", ""))[:200]
            return str(first)[:200]
        if isinstance(content, str) and content:
            return content[:200]
        return "Task completed"

    @staticmethod
    def _extract_output(data: dict) -> str:
        """Extract output summary from the entry."""
        content = data.get("content", "")
        if isinstance(content, str):
            return content[:500]
        if isinstance(content, list):
            texts = [str(c.get("text", "")) if isinstance(c, dict) else str(c) for c in content]
            return " ".join(texts)[:500]
        return ""

    @staticmethod
    def _extract_files(data: dict) -> list[str]:
        """Extract list of changed files from the entry."""
        files = data.get("files_changed", [])
        if isinstance(files, list):
            return [str(f) for f in files[:50]]
        return []

    @staticmethod
    def _extract_errors(data: dict) -> list[str]:
        """Extract error messages from the entry."""
        errors = data.get("errors", [])
        if isinstance(errors, list) and errors:
            return [str(e) for e in errors[:20]]
        if data.get("error"):
            return [str(data["error"])[:200]]
        return []

    async def _notify_subscribers(self, event: TaskCompletionEvent) -> None:
        """Notify all subscribers. Errors in subscribers are isolated."""
        for callback in self._subscribers:
            try:
                await callback(event)
            except Exception:
                logger.exception("Subscriber error in SessionWatcher")


class _SessionFileHandler:
    """Watchdog FileSystemEventHandler that bridges to SessionWatcher.

    Runs in the watchdog thread — must not do async work directly.
    Delegates to SessionWatcher._on_file_modified which uses
    run_coroutine_threadsafe to bridge to the asyncio loop.
    """

    def __init__(self, watcher: SessionWatcher):
        self._watcher = watcher

    def dispatch(self, event) -> None:
        """Handle all filesystem events."""
        if event.is_directory:
            return
        if event.event_type in ("modified", "created"):
            self._watcher._on_file_modified(event.src_path)
