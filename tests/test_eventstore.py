"""Tests for EventStoreDB client wrapper."""

import json
import os
from unittest.mock import MagicMock, patch

import pytest

from kovrin.storage.eventstore import EventStoreClient, StoredEvent


class TestStoredEvent:
    def test_defaults(self):
        e = StoredEvent(stream_name="s1", event_type="TestEvent", data={"key": "val"})
        assert e.stream_name == "s1"
        assert e.event_type == "TestEvent"
        assert e.data == {"key": "val"}
        assert e.metadata == {}
        assert e.event_id == ""
        assert e.position == 0


class TestFromEnv:
    def test_returns_none_without_env(self):
        with patch.dict(os.environ, {}, clear=True):
            assert EventStoreClient.from_env() is None

    def test_returns_client_with_env(self):
        with patch.dict(os.environ, {"EVENTSTORE_URL": "esdb://localhost:2113?tls=false"}):
            client = EventStoreClient.from_env()
            assert client is not None
            assert client._connection_string == "esdb://localhost:2113?tls=false"


class TestConstruction:
    def test_lazy_connection(self):
        client = EventStoreClient("esdb://localhost:2113?tls=false")
        assert client._client is None  # Not connected yet
        assert client._connection_string == "esdb://localhost:2113?tls=false"


class TestEnsureClient:
    def test_import_error_without_esdbclient(self):
        client = EventStoreClient("esdb://localhost:2113")
        with patch.dict("sys.modules", {"esdbclient": None}):
            with pytest.raises(ImportError, match="esdbclient is required"):
                client._ensure_client()

    def test_creates_client_with_esdbclient(self):
        client = EventStoreClient("esdb://localhost:2113")
        mock_esdb_client = MagicMock()

        mock_module = MagicMock()
        mock_module.EventStoreDBClient.return_value = mock_esdb_client

        with patch.dict("sys.modules", {"esdbclient": mock_module}):
            client._ensure_client()
            assert client._client is mock_esdb_client


class TestAppend:
    def test_appends_event_to_stream(self):
        client = EventStoreClient("esdb://localhost:2113")
        mock_esdb = MagicMock()
        client._client = mock_esdb

        mock_module = MagicMock()
        mock_new_event = MagicMock()
        mock_module.NewEvent.return_value = mock_new_event

        with patch.dict("sys.modules", {"esdbclient": mock_module}):
            event_id = client.append(
                stream_name="pipeline-test",
                event_type="TraceAppended",
                data={"hash": "abc123"},
                metadata={"chain_head": "def456"},
            )

        assert isinstance(event_id, str)
        assert len(event_id) > 0
        mock_esdb.append_to_stream.assert_called_once()


class TestReadStream:
    def test_reads_events(self):
        client = EventStoreClient("esdb://localhost:2113")
        mock_esdb = MagicMock()
        client._client = mock_esdb

        mock_event = MagicMock()
        mock_event.type = "TraceAppended"
        mock_event.data = json.dumps({"hash": "abc"}).encode()
        mock_event.metadata = json.dumps({"chain": "head"}).encode()
        mock_event.id = "event-id-1"
        mock_event.stream_position = 0

        mock_esdb.get_stream.return_value = [mock_event]

        events = list(client.read_stream("pipeline-test"))
        assert len(events) == 1
        assert events[0].event_type == "TraceAppended"
        assert events[0].data == {"hash": "abc"}
        assert events[0].metadata == {"chain": "head"}

    def test_empty_on_error(self):
        client = EventStoreClient("esdb://localhost:2113")
        mock_esdb = MagicMock()
        mock_esdb.get_stream.side_effect = Exception("stream not found")
        client._client = mock_esdb

        events = list(client.read_stream("nonexistent"))
        assert events == []


class TestStreamExists:
    def test_exists_when_has_events(self):
        client = EventStoreClient("esdb://localhost:2113")
        mock_esdb = MagicMock()
        client._client = mock_esdb

        mock_event = MagicMock()
        mock_event.type = "Test"
        mock_event.data = b"{}"
        mock_event.metadata = b""
        mock_event.id = "id"
        mock_event.stream_position = 0

        mock_esdb.get_stream.return_value = [mock_event]
        assert client.stream_exists("s1") is True

    def test_not_exists_when_empty(self):
        client = EventStoreClient("esdb://localhost:2113")
        mock_esdb = MagicMock()
        mock_esdb.get_stream.side_effect = Exception("not found")
        client._client = mock_esdb
        assert client.stream_exists("s1") is False


class TestClose:
    def test_closes_client(self):
        client = EventStoreClient("esdb://localhost:2113")
        mock_esdb = MagicMock()
        client._client = mock_esdb
        client.close()
        mock_esdb.close.assert_called_once()
        assert client._client is None

    def test_close_without_connection(self):
        client = EventStoreClient("esdb://localhost:2113")
        client.close()  # Should not raise
