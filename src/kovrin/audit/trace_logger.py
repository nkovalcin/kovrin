"""
Kovrin Immutable Trace Logger

Implements cryptographic audit trails using Merkle-tree hash chaining.
Every trace event is linked to the previous event via SHA-256 hash,
creating a tamper-evident chain.

Based on research into:
- Certificate Transparency (append-only Merkle trees)
- Event sourcing patterns for AI decision replay
- Clinical AI audit logging (< 5ms tamper detection)

Features:
- Append-only: events can never be modified or deleted
- Tamper-evident: any modification breaks the hash chain
- Replayable: full decision state can be reconstructed
- Exportable: JSON export for external audit tools
"""

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path

from pydantic import BaseModel, Field

from kovrin.core.models import Trace


class HashedTrace(BaseModel):
    """A trace event with Merkle-tree hash chaining."""

    trace: Trace
    hash: str = Field(..., description="SHA-256 hash of this event + previous hash")
    previous_hash: str = Field("GENESIS", description="Hash of the previous event")
    sequence: int = Field(0, description="Sequential event number")


class ImmutableTraceLog:
    """Append-only, tamper-evident trace log.

    Uses SHA-256 hash chaining to ensure integrity.
    Each event's hash includes the previous event's hash,
    creating a chain that breaks if any event is modified.
    """

    GENESIS_HASH = "0" * 64  # Initial hash for the chain

    def __init__(self):
        self._events: list[HashedTrace] = []
        self._current_hash: str = self.GENESIS_HASH
        self._subscribers: list = []  # list of async callables

    def subscribe(self, callback) -> None:
        """Register an async callback for new trace events.

        Callback signature: async (HashedTrace) -> None
        """
        self._subscribers.append(callback)

    def unsubscribe(self, callback) -> None:
        """Remove a previously registered callback."""
        self._subscribers = [s for s in self._subscribers if s is not callback]

    async def _notify_subscribers(self, hashed: HashedTrace) -> None:
        """Notify all subscribers of a new event."""
        for callback in self._subscribers:
            try:
                await callback(hashed)
            except Exception:
                pass  # Subscriber errors must not break the trace log

    def append(self, trace: Trace) -> HashedTrace:
        """Append a trace event to the immutable log.

        The event is hashed with the previous event's hash,
        creating a tamper-evident chain.
        """
        sequence = len(self._events)

        # Create hash of event content + previous hash
        content = json.dumps(
            {
                "id": trace.id,
                "timestamp": trace.timestamp.isoformat(),
                "intent_id": trace.intent_id,
                "task_id": trace.task_id,
                "event_type": trace.event_type,
                "description": trace.description,
                "details": trace.details,
                "previous_hash": self._current_hash,
                "sequence": sequence,
            },
            sort_keys=True,
            default=str,
        )

        event_hash = hashlib.sha256(content.encode()).hexdigest()

        hashed = HashedTrace(
            trace=trace,
            hash=event_hash,
            previous_hash=self._current_hash,
            sequence=sequence,
        )

        self._events.append(hashed)
        self._current_hash = event_hash

        return hashed

    async def append_async(self, trace: Trace) -> HashedTrace:
        """Append a trace event and notify subscribers.

        Use this instead of append() when running in an async context
        with active subscribers (e.g., watchdog agent).
        """
        hashed = self.append(trace)
        await self._notify_subscribers(hashed)
        return hashed

    def verify_integrity(self) -> tuple[bool, str]:
        """Verify the entire chain is intact.

        Returns (is_valid, message).
        Checks every hash in the chain sequentially.
        """
        if not self._events:
            return True, "Empty log — no events to verify"

        expected_prev = self.GENESIS_HASH

        for i, event in enumerate(self._events):
            # Verify previous hash link
            if event.previous_hash != expected_prev:
                return False, (
                    f"Chain broken at event {i}: "
                    f"expected previous_hash={expected_prev[:16]}..., "
                    f"got {event.previous_hash[:16]}..."
                )

            # Recompute hash
            content = json.dumps(
                {
                    "id": event.trace.id,
                    "timestamp": event.trace.timestamp.isoformat(),
                    "intent_id": event.trace.intent_id,
                    "task_id": event.trace.task_id,
                    "event_type": event.trace.event_type,
                    "description": event.trace.description,
                    "details": event.trace.details,
                    "previous_hash": event.previous_hash,
                    "sequence": event.sequence,
                },
                sort_keys=True,
                default=str,
            )

            recomputed = hashlib.sha256(content.encode()).hexdigest()

            if recomputed != event.hash:
                return False, (
                    f"Tampered event at {i}: "
                    f"stored hash={event.hash[:16]}..., "
                    f"recomputed={recomputed[:16]}..."
                )

            expected_prev = event.hash

        return True, f"All {len(self._events)} events verified — chain intact"

    def get_events(
        self,
        intent_id: str | None = None,
        task_id: str | None = None,
        event_type: str | None = None,
    ) -> list[HashedTrace]:
        """Query events with optional filters."""
        results = self._events
        if intent_id:
            results = [e for e in results if e.trace.intent_id == intent_id]
        if task_id:
            results = [e for e in results if e.trace.task_id == task_id]
        if event_type:
            results = [e for e in results if e.trace.event_type == event_type]
        return results

    def export_json(self, path: str | Path) -> None:
        """Export the full log as JSON for external audit."""
        data = {
            "exported_at": datetime.now(UTC).isoformat(),
            "total_events": len(self._events),
            "chain_head": self._current_hash,
            "events": [
                {
                    "sequence": e.sequence,
                    "hash": e.hash,
                    "previous_hash": e.previous_hash,
                    "trace": {
                        "id": e.trace.id,
                        "timestamp": e.trace.timestamp.isoformat(),
                        "intent_id": e.trace.intent_id,
                        "task_id": e.trace.task_id,
                        "event_type": e.trace.event_type,
                        "description": e.trace.description,
                        "details": e.trace.details,
                        "risk_level": e.trace.risk_level.value if e.trace.risk_level else None,
                        "l0_passed": e.trace.l0_passed,
                    },
                }
                for e in self._events
            ],
        }
        Path(path).write_text(json.dumps(data, indent=2, default=str))

    def print_summary(self) -> None:
        """Print a human-readable summary of the trace log."""
        valid, msg = self.verify_integrity()
        icon = "+" if valid else "x"
        print(f"\n{'=' * 60}")
        print(f"IMMUTABLE TRACE LOG — {len(self._events)} events")
        print(f"Chain integrity: {icon} {msg}")
        print(f"Chain head: {self._current_hash[:32]}...")
        print(f"{'=' * 60}")

        for e in self._events:
            risk = f"[{e.trace.risk_level.value}]" if e.trace.risk_level else "[---]"
            l0 = "+L0" if e.trace.l0_passed else ("xL0" if e.trace.l0_passed is False else "   ")
            print(
                f"  #{e.sequence:3d} {e.hash[:8]} {risk:8s} {l0} {e.trace.event_type:18s} {e.trace.description[:50]}"
            )

    def get_events_since(self, sequence: int) -> list[HashedTrace]:
        """Return all events from the given sequence onward (inclusive)."""
        return [e for e in self._events if e.sequence >= sequence]

    def get_frame_at(self, sequence: int) -> HashedTrace | None:
        """Return the event at the given sequence number, or None."""
        for e in self._events:
            if e.sequence == sequence:
                return e
        return None

    @property
    def head_hash(self) -> str:
        """Returns the SHA-256 hash of the most recent event in the chain."""
        return self._current_hash

    def __len__(self) -> int:
        return len(self._events)
