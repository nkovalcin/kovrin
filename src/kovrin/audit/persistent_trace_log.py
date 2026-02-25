"""Persistent Trace Log — extends ImmutableTraceLog with EventStoreDB persistence.

The Merkle hash chain is computed in-memory first (preserving all safety
guarantees), then each hashed event is persisted to EventStoreDB for
cross-session durability.

Safety invariant: The in-memory chain is the source of truth for integrity
verification. EventStoreDB is a persistence layer, not a trust layer.
verify_integrity() works on the in-memory chain as before.
verify_from_store() provides cross-session verification by loading from ESDB.
"""

from __future__ import annotations

import hashlib
import json
from typing import TYPE_CHECKING

from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.models import Trace

if TYPE_CHECKING:
    from kovrin.storage.eventstore import EventStoreClient


class PersistentTraceLog(ImmutableTraceLog):
    """ImmutableTraceLog with EventStoreDB persistence.

    Extends the base trace log to persist every hashed event to
    an EventStoreDB stream. The stream name is based on the intent ID.

    Usage:
        from kovrin.storage.eventstore import EventStoreClient

        es_client = EventStoreClient("esdb://localhost:2113?tls=false")
        log = PersistentTraceLog(es_client, intent_id="abc123")
        await log.append_async(trace)  # Persists to ESDB automatically
    """

    def __init__(self, es_client: EventStoreClient, intent_id: str = "unknown"):
        super().__init__()
        self._es_client = es_client
        self._intent_id = intent_id
        self._stream_name = f"pipeline-{intent_id}"

    def append(self, trace: Trace) -> HashedTrace:
        """Append to in-memory chain, then persist to EventStoreDB."""
        hashed = super().append(trace)

        # Persist to EventStoreDB (best-effort — persistence failure
        # must not break the in-memory safety chain)
        try:
            self._es_client.append(
                stream_name=self._stream_name,
                event_type="TraceAppended",
                data={
                    "sequence": hashed.sequence,
                    "hash": hashed.hash,
                    "previous_hash": hashed.previous_hash,
                    "trace_id": trace.id,
                    "intent_id": trace.intent_id,
                    "task_id": trace.task_id,
                    "event_type": trace.event_type,
                    "description": trace.description,
                    "details": trace.details,
                    "risk_level": trace.risk_level.value if trace.risk_level else None,
                    "l0_passed": trace.l0_passed,
                    "timestamp": trace.timestamp.isoformat(),
                },
                metadata={
                    "chain_head": self._current_hash,
                    "stream": self._stream_name,
                },
            )
        except Exception:
            pass  # Persistence errors must not break the pipeline

        return hashed

    @classmethod
    def verify_from_store(
        cls,
        es_client: EventStoreClient,
        intent_id: str,
    ) -> tuple[bool, str]:
        """Verify chain integrity from EventStoreDB (cross-session).

        Loads all events from the ESDB stream and recomputes the hash chain.

        Returns:
            (is_valid, message) tuple.
        """
        stream_name = f"pipeline-{intent_id}"
        events = list(es_client.read_stream(stream_name))

        if not events:
            return True, "No events found in store"

        genesis_hash = "0" * 64
        expected_prev = genesis_hash

        for i, event in enumerate(events):
            data = event.data
            stored_hash = data.get("hash", "")
            stored_prev = data.get("previous_hash", "")

            # Verify chain link
            if stored_prev != expected_prev:
                return False, (
                    f"Chain broken at event {i}: "
                    f"expected previous_hash={expected_prev[:16]}..., "
                    f"got {stored_prev[:16]}..."
                )

            # Recompute hash to verify content integrity
            content = json.dumps(
                {
                    "id": data.get("trace_id", ""),
                    "timestamp": data.get("timestamp", ""),
                    "intent_id": data.get("intent_id", ""),
                    "task_id": data.get("task_id", ""),
                    "event_type": data.get("event_type", ""),
                    "description": data.get("description", ""),
                    "details": data.get("details"),
                    "previous_hash": stored_prev,
                    "sequence": data.get("sequence", i),
                },
                sort_keys=True,
                default=str,
            )
            recomputed = hashlib.sha256(content.encode()).hexdigest()

            if recomputed != stored_hash:
                return False, (
                    f"Tampered event at {i}: "
                    f"stored hash={stored_hash[:16]}..., "
                    f"recomputed={recomputed[:16]}..."
                )

            expected_prev = stored_hash

        return True, f"All {len(events)} events verified from store — chain intact"
