"""Tests for SuperWork Session Watcher."""

import asyncio
import json
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin.superwork.models import TaskCompletionEvent
from kovrin.superwork.session_watcher import SessionWatcher


class TestConstruction:
    def test_defaults(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        assert watcher._project_path == tmp_path.resolve()
        assert watcher._subscribers == []
        assert watcher._file_positions == {}
        assert watcher._observer is None

    def test_custom_sessions_path(self, tmp_path):
        sessions = tmp_path / "sessions"
        watcher = SessionWatcher(project_path=tmp_path, sessions_path=sessions)
        assert watcher._sessions_path == sessions

    def test_subscribe_and_unsubscribe(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        cb = AsyncMock()
        watcher.subscribe(cb)
        assert len(watcher._subscribers) == 1
        watcher.unsubscribe(cb)
        assert len(watcher._subscribers) == 0

    def test_is_watching_false_initially(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        assert watcher.is_watching is False


class TestCompletionSignal:
    def test_type_result_is_completion(self):
        assert SessionWatcher._is_completion_signal({"type": "result"}) is True

    def test_assistant_end_turn_is_completion(self):
        assert SessionWatcher._is_completion_signal(
            {"type": "assistant", "stop_reason": "end_turn"}
        ) is True

    def test_assistant_without_end_turn_is_not(self):
        assert SessionWatcher._is_completion_signal(
            {"type": "assistant", "stop_reason": "tool_use"}
        ) is False

    def test_human_message_is_not_completion(self):
        assert SessionWatcher._is_completion_signal({"type": "human"}) is False

    def test_empty_data_is_not_completion(self):
        assert SessionWatcher._is_completion_signal({}) is False


class TestExtractTaskDescription:
    def test_from_summary_field(self):
        desc = SessionWatcher._extract_task_description({"summary": "Fixed the bug"})
        assert desc == "Fixed the bug"

    def test_from_content_list_with_dict(self):
        desc = SessionWatcher._extract_task_description(
            {"content": [{"text": "Refactored module"}]}
        )
        assert desc == "Refactored module"

    def test_from_content_list_with_string(self):
        desc = SessionWatcher._extract_task_description({"content": ["Wrote tests"]})
        assert desc == "Wrote tests"

    def test_from_content_string(self):
        desc = SessionWatcher._extract_task_description({"content": "Added feature"})
        assert desc == "Added feature"

    def test_fallback_when_empty(self):
        desc = SessionWatcher._extract_task_description({})
        assert desc == "Task completed"

    def test_truncates_long_summary(self):
        long = "x" * 500
        desc = SessionWatcher._extract_task_description({"summary": long})
        assert len(desc) == 200


class TestExtractOutput:
    def test_string_content(self):
        out = SessionWatcher._extract_output({"content": "Hello world"})
        assert out == "Hello world"

    def test_list_content(self):
        out = SessionWatcher._extract_output({"content": [{"text": "a"}, {"text": "b"}]})
        assert "a" in out and "b" in out

    def test_empty(self):
        out = SessionWatcher._extract_output({})
        assert out == ""


class TestExtractFiles:
    def test_with_files_list(self):
        files = SessionWatcher._extract_files({"files_changed": ["a.py", "b.py"]})
        assert files == ["a.py", "b.py"]

    def test_empty(self):
        assert SessionWatcher._extract_files({}) == []


class TestExtractErrors:
    def test_errors_list(self):
        errors = SessionWatcher._extract_errors({"errors": ["err1", "err2"]})
        assert errors == ["err1", "err2"]

    def test_single_error_field(self):
        errors = SessionWatcher._extract_errors({"error": "something broke"})
        assert errors == ["something broke"]

    def test_empty(self):
        assert SessionWatcher._extract_errors({}) == []


class TestReadNewLines:
    def test_reads_new_content(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        f = tmp_path / "session.jsonl"
        f.write_text('{"type": "result"}\n')

        lines = watcher._read_new_lines(str(f))
        assert len(lines) == 1
        assert "result" in lines[0]

        # Second read returns nothing (position tracked)
        lines2 = watcher._read_new_lines(str(f))
        assert lines2 == []

    def test_reads_only_appended_lines(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        f = tmp_path / "session.jsonl"
        f.write_text('{"line": 1}\n')
        watcher._read_new_lines(str(f))

        # Append new content
        with open(f, "a") as fh:
            fh.write('{"line": 2}\n')

        lines = watcher._read_new_lines(str(f))
        assert len(lines) == 1
        assert "line" in lines[0] and "2" in lines[0]

    def test_missing_file_returns_empty(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        lines = watcher._read_new_lines(str(tmp_path / "nope.jsonl"))
        assert lines == []


class TestParseCompletions:
    def test_valid_completion(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        lines = [json.dumps({"type": "result", "summary": "Done"}) + "\n"]
        events = watcher._parse_completions(lines, str(tmp_path / "sess.jsonl"))
        assert len(events) == 1
        assert events[0].completed_task == "Done"

    def test_skips_non_completion(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        lines = [json.dumps({"type": "human", "content": "hello"}) + "\n"]
        events = watcher._parse_completions(lines, str(tmp_path / "sess.jsonl"))
        assert events == []

    def test_skips_invalid_json(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        lines = ["not json at all\n", "", "\n"]
        events = watcher._parse_completions(lines, str(tmp_path / "sess.jsonl"))
        assert events == []

    def test_mixed_valid_and_invalid(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        lines = [
            "broken\n",
            json.dumps({"type": "result", "summary": "OK"}) + "\n",
            json.dumps({"type": "human"}) + "\n",
        ]
        events = watcher._parse_completions(lines, str(tmp_path / "sess.jsonl"))
        assert len(events) == 1


class TestNotifySubscribers:
    @pytest.mark.asyncio
    async def test_calls_all_callbacks(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        cb1 = AsyncMock()
        cb2 = AsyncMock()
        watcher.subscribe(cb1)
        watcher.subscribe(cb2)

        event = TaskCompletionEvent(completed_task="test")
        await watcher._notify_subscribers(event)

        cb1.assert_called_once_with(event)
        cb2.assert_called_once_with(event)

    @pytest.mark.asyncio
    async def test_isolates_subscriber_errors(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        cb_bad = AsyncMock(side_effect=RuntimeError("boom"))
        cb_good = AsyncMock()
        watcher.subscribe(cb_bad)
        watcher.subscribe(cb_good)

        event = TaskCompletionEvent(completed_task="test")
        await watcher._notify_subscribers(event)

        # Good callback still called despite bad one failing
        cb_good.assert_called_once_with(event)


class TestResolveWatchPath:
    def test_finds_matching_project_dir(self, tmp_path):
        sessions = tmp_path / "sessions"
        project = tmp_path / "myproject"
        project.mkdir()
        sessions.mkdir()
        slug_dir = sessions / f"-{str(project).replace('/', '-')}"
        slug_dir.mkdir()

        watcher = SessionWatcher(project_path=project, sessions_path=sessions)
        result = watcher._resolve_watch_path()
        assert result == slug_dir

    def test_fallback_to_sessions_root(self, tmp_path):
        sessions = tmp_path / "sessions"
        sessions.mkdir()
        watcher = SessionWatcher(project_path=tmp_path / "unknown", sessions_path=sessions)
        result = watcher._resolve_watch_path()
        assert result == sessions


class TestOnFileModified:
    def test_ignores_non_jsonl(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        watcher._read_new_lines = MagicMock()
        watcher._on_file_modified("file.txt")
        watcher._read_new_lines.assert_not_called()

    def test_processes_jsonl_file(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path)
        watcher._loop = MagicMock()
        watcher._loop.is_closed.return_value = False

        f = tmp_path / "session.jsonl"
        f.write_text(json.dumps({"type": "result", "summary": "Done"}) + "\n")

        with patch("asyncio.run_coroutine_threadsafe") as mock_rcs:
            watcher._on_file_modified(str(f))
            assert mock_rcs.called


class TestStartStop:
    @pytest.mark.asyncio
    async def test_start_creates_observer(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path, sessions_path=tmp_path)

        mock_observer = MagicMock()
        mock_observer.is_alive.return_value = True

        with patch("watchdog.observers.Observer", return_value=mock_observer):
            await watcher.start()

        assert watcher._observer is mock_observer
        mock_observer.schedule.assert_called_once()
        mock_observer.start.assert_called_once()

    @pytest.mark.asyncio
    async def test_stop_cleans_up(self, tmp_path):
        watcher = SessionWatcher(project_path=tmp_path, sessions_path=tmp_path)
        mock_observer = MagicMock()

        with patch("watchdog.observers.Observer", return_value=mock_observer):
            await watcher.start()
            await watcher.stop()

        mock_observer.stop.assert_called_once()
        mock_observer.join.assert_called_once()
        assert watcher._observer is None


class TestSessionFileHandler:
    def test_dispatch_ignores_directories(self, tmp_path):
        from kovrin.superwork.session_watcher import _SessionFileHandler

        watcher = MagicMock()
        handler = _SessionFileHandler(watcher)
        event = MagicMock()
        event.is_directory = True
        handler.dispatch(event)
        watcher._on_file_modified.assert_not_called()

    def test_dispatch_handles_modified(self, tmp_path):
        from kovrin.superwork.session_watcher import _SessionFileHandler

        watcher = MagicMock()
        handler = _SessionFileHandler(watcher)
        event = MagicMock()
        event.is_directory = False
        event.event_type = "modified"
        event.src_path = "/tmp/file.jsonl"
        handler.dispatch(event)
        watcher._on_file_modified.assert_called_once_with("/tmp/file.jsonl")
