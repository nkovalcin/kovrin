"""EventStoreDB client wrapper for Kovrin.

Provides a thin abstraction over esdbclient for appending and reading
events from EventStoreDB streams. Opt-in via EVENTSTORE_URL env var.

EventStoreDB gives us:
- Immutable, append-only event streams
- Cross-session audit trail persistence
- Event subscriptions for real-time processing
- Built-in ordering and idempotency
"""

from __future__ import annotations

import json
import os
import uuid
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Generator


@dataclass
class StoredEvent:
    """An event read back from EventStoreDB."""

    stream_name: str
    event_type: str
    data: dict
    metadata: dict = field(default_factory=dict)
    event_id: str = ""
    position: int = 0


class EventStoreClient:
    """Thin wrapper around esdbclient for Kovrin audit persistence.

    Usage:
        client = EventStoreClient.from_env()
        if client:
            client.append("pipeline-abc123", "TraceAppended", {"hash": "..."})
            events = list(client.read_stream("pipeline-abc123"))
    """

    def __init__(self, connection_string: str):
        """Initialize with an EventStoreDB connection string.

        Args:
            connection_string: e.g. "esdb://localhost:2113?tls=false"
        """
        self._connection_string = connection_string
        self._client = None

    @classmethod
    def from_env(cls) -> EventStoreClient | None:
        """Create client from EVENTSTORE_URL env var. Returns None if not set."""
        url = os.environ.get("EVENTSTORE_URL")
        if not url:
            return None
        return cls(url)

    def _ensure_client(self):
        """Lazily connect to EventStoreDB."""
        if self._client is not None:
            return

        try:
            from esdbclient import EventStoreDBClient

            self._client = EventStoreDBClient(uri=self._connection_string)
        except ImportError as e:
            raise ImportError(
                "esdbclient is required for EventStoreDB support. "
                "Install with: pip install 'kovrin[eventstore]'"
            ) from e

    def append(
        self,
        stream_name: str,
        event_type: str,
        data: dict,
        metadata: dict | None = None,
    ) -> str:
        """Append an event to a stream.

        Args:
            stream_name: The stream to append to (e.g., "pipeline-{intent_id}").
            event_type: Event type name (e.g., "TraceAppended", "ChainVerified").
            data: Event payload dict.
            metadata: Optional metadata dict.

        Returns:
            The event ID (UUID string).
        """
        self._ensure_client()

        from esdbclient import NewEvent

        event_id = uuid.uuid4()
        event = NewEvent(
            type=event_type,
            data=json.dumps(data, default=str).encode("utf-8"),
            metadata=json.dumps(metadata or {}, default=str).encode("utf-8"),
            id=event_id,
        )

        self._client.append_to_stream(
            stream_name=stream_name,
            current_version="any",
            events=[event],
        )

        return str(event_id)

    def read_stream(
        self,
        stream_name: str,
        from_position: int = 0,
    ) -> Generator[StoredEvent, None, None]:
        """Read all events from a stream.

        Args:
            stream_name: The stream to read from.
            from_position: Start reading from this position (0-based).

        Yields:
            StoredEvent instances.
        """
        self._ensure_client()

        try:
            events = self._client.get_stream(
                stream_name=stream_name,
                stream_position=from_position,
            )
            for recorded in events:
                yield StoredEvent(
                    stream_name=stream_name,
                    event_type=recorded.type,
                    data=json.loads(recorded.data.decode("utf-8")),
                    metadata=json.loads(recorded.metadata.decode("utf-8")) if recorded.metadata else {},
                    event_id=str(recorded.id),
                    position=recorded.stream_position,
                )
        except Exception:
            # Stream not found or connection error — yield nothing
            return

    def stream_exists(self, stream_name: str) -> bool:
        """Check if a stream has any events."""
        for _ in self.read_stream(stream_name):
            return True
        return False

    def close(self) -> None:
        """Close the EventStoreDB connection."""
        if self._client is not None:
            try:
                self._client.close()
            except Exception:
                pass
            self._client = None
