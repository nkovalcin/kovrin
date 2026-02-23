"""Tests for SuperWork Session Watcher."""

import asyncio
import json
from unittest.mock import AsyncMock

import pytest

from kovrin.superwork.models import TaskCompletionEvent
from kovrin.superwork.session_watcher import SessionWatcher


class TestSessionWatcherImport:
    def test_import(self):
        assert SessionWatcher is not None

    def test_constructor(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        assert watcher._project_path == tmp_path.resolve()

    def test_subscribe(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        callback = AsyncMock()
        watcher.subscribe(callback)
        assert callback in watcher._subscribers

    def test_unsubscribe(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        callback = AsyncMock()
        watcher.subscribe(callback)
        watcher.unsubscribe(callback)
        assert callback not in watcher._subscribers


class TestCompletionSignalDetection:
    """Test _is_completion_signal static method."""

    def test_result_type(self):
        assert SessionWatcher._is_completion_signal({"type": "result"}) is True

    def test_end_turn(self):
        data = {"type": "assistant", "stop_reason": "end_turn"}
        assert SessionWatcher._is_completion_signal(data) is True

    def test_user_message(self):
        assert SessionWatcher._is_completion_signal({"type": "user"}) is False

    def test_assistant_no_stop(self):
        data = {"type": "assistant", "stop_reason": "max_tokens"}
        assert SessionWatcher._is_completion_signal(data) is False

    def test_empty_dict(self):
        assert SessionWatcher._is_completion_signal({}) is False


class TestParseCompletions:
    """Test JSONL line parsing via _parse_completions."""

    def test_parse_result_event(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        line = json.dumps({"type": "result", "summary": "Implemented feature X"})
        events = watcher._parse_completions([line], str(tmp_path / "test.jsonl"))
        assert len(events) == 1
        assert isinstance(events[0], TaskCompletionEvent)
        assert "Implemented feature X" in events[0].completed_task

    def test_parse_end_turn(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        line = json.dumps(
            {
                "type": "assistant",
                "stop_reason": "end_turn",
                "content": [{"text": "Done with the task"}],
            }
        )
        events = watcher._parse_completions([line], str(tmp_path / "test.jsonl"))
        assert len(events) == 1

    def test_parse_irrelevant_line(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        line = json.dumps({"type": "user", "message": "hello"})
        events = watcher._parse_completions([line], str(tmp_path / "test.jsonl"))
        assert len(events) == 0

    def test_parse_invalid_json(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        events = watcher._parse_completions(["not valid json {{{"], str(tmp_path / "test.jsonl"))
        assert len(events) == 0

    def test_parse_empty_lines(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        events = watcher._parse_completions(["", "  \n"], str(tmp_path / "t.jsonl"))
        assert len(events) == 0

    def test_parse_multiple_lines(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        lines = [
            json.dumps({"type": "user", "message": "do stuff"}),
            json.dumps({"type": "result", "summary": "Task A"}),
            json.dumps({"type": "assistant", "stop_reason": "end_turn", "content": ""}),
            json.dumps({"type": "result", "summary": "Task B"}),
        ]
        events = watcher._parse_completions(lines, str(tmp_path / "t.jsonl"))
        assert len(events) == 3


class TestNotification:
    @pytest.mark.asyncio
    async def test_notify_subscribers(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        received = []

        async def callback(event):
            received.append(event)

        watcher.subscribe(callback)
        event = TaskCompletionEvent(completed_task="test")
        watcher._loop = asyncio.get_event_loop()
        await watcher._notify_subscribers(event)
        assert len(received) == 1
        assert received[0].completed_task == "test"

    @pytest.mark.asyncio
    async def test_subscriber_error_isolation(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))

        async def bad_callback(event):
            raise ValueError("boom")

        received = []

        async def good_callback(event):
            received.append(event)

        watcher.subscribe(bad_callback)
        watcher.subscribe(good_callback)
        event = TaskCompletionEvent(completed_task="test")
        watcher._loop = asyncio.get_event_loop()
        await watcher._notify_subscribers(event)
        assert len(received) == 1


class TestTailFollow:
    """Test _read_new_lines (returns raw strings, not events)."""

    def test_read_new_lines(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        jsonl_file = tmp_path / "session.jsonl"
        lines = [
            json.dumps({"type": "user", "message": "hi"}),
            json.dumps({"type": "result", "summary": "Bug fixed"}),
        ]
        jsonl_file.write_text("\n".join(lines) + "\n")

        raw_lines = watcher._read_new_lines(str(jsonl_file))
        assert len(raw_lines) == 2
        assert "user" in raw_lines[0]

    def test_tail_follow_tracks_position(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        jsonl_file = tmp_path / "session.jsonl"
        jsonl_file.write_text(json.dumps({"type": "result"}) + "\n")

        lines1 = watcher._read_new_lines(str(jsonl_file))
        assert len(lines1) == 1

        with open(jsonl_file, "a") as f:
            f.write(json.dumps({"type": "result", "summary": "T2"}) + "\n")

        lines2 = watcher._read_new_lines(str(jsonl_file))
        assert len(lines2) == 1
        assert "T2" in lines2[0]

    def test_read_nonexistent_file(self, tmp_path):
        watcher = SessionWatcher(str(tmp_path))
        lines = watcher._read_new_lines("/nonexistent/file.jsonl")
        assert lines == []


class TestExtractHelpers:
    def test_extract_task_from_summary(self):
        desc = SessionWatcher._extract_task_description({"summary": "Fixed auth bug"})
        assert desc == "Fixed auth bug"

    def test_extract_task_from_content_list(self):
        desc = SessionWatcher._extract_task_description(
            {"content": [{"text": "Refactored module"}]}
        )
        assert desc == "Refactored module"

    def test_extract_task_from_content_string(self):
        desc = SessionWatcher._extract_task_description({"content": "Added tests"})
        assert desc == "Added tests"

    def test_extract_task_fallback(self):
        desc = SessionWatcher._extract_task_description({})
        assert desc == "Task completed"

    def test_extract_files(self):
        files = SessionWatcher._extract_files({"files_changed": ["a.py", "b.py"]})
        assert files == ["a.py", "b.py"]

    def test_extract_files_empty(self):
        assert SessionWatcher._extract_files({}) == []

    def test_extract_errors(self):
        errors = SessionWatcher._extract_errors({"errors": ["fail1"]})
        assert errors == ["fail1"]

    def test_extract_errors_from_error_field(self):
        errors = SessionWatcher._extract_errors({"error": "something broke"})
        assert errors == ["something broke"]
