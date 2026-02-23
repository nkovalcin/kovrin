"""
Kovrin SQLite Persistence

Stores pipeline results and trace events in SQLite for durability
across server restarts. Uses Python's built-in sqlite3 module
(no additional dependencies).

Schema:
- pipelines: stores ExecutionResult metadata
- traces: stores individual trace events with hash chain data
"""

import json
import sqlite3
from datetime import datetime, timezone
from pathlib import Path

from kovrin.core.models import (
    AutonomyProfile,
    AutonomySettings,
    ExecutionResult,
    RiskLevel,
    SubTask,
    Trace,
)


class PipelineRepository:
    """SQLite-backed storage for pipeline results and traces."""

    def __init__(self, db_path: str = "kovrin.db"):
        """Initialize repository.

        Args:
            db_path: Path to SQLite database file. Use ":memory:" for testing.
        """
        self._db_path = db_path
        self._conn = sqlite3.connect(db_path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._create_tables()

    def _create_tables(self) -> None:
        self._conn.executescript("""
            CREATE TABLE IF NOT EXISTS pipelines (
                intent_id TEXT PRIMARY KEY,
                intent TEXT DEFAULT '',
                constraints TEXT DEFAULT '[]',
                context TEXT DEFAULT '{}',
                status TEXT DEFAULT 'completed',
                success INTEGER DEFAULT 0,
                output TEXT DEFAULT '',
                sub_tasks TEXT DEFAULT '[]',
                rejected_tasks TEXT DEFAULT '[]',
                graph_summary TEXT DEFAULT '{}',
                created_at TEXT DEFAULT '',
                completed_at TEXT DEFAULT ''
            );

            CREATE TABLE IF NOT EXISTS traces (
                id TEXT PRIMARY KEY,
                intent_id TEXT NOT NULL,
                task_id TEXT DEFAULT '',
                event_type TEXT DEFAULT '',
                description TEXT DEFAULT '',
                details TEXT DEFAULT '{}',
                risk_level TEXT,
                l0_passed INTEGER,
                timestamp TEXT DEFAULT '',
                hash TEXT DEFAULT '',
                previous_hash TEXT DEFAULT '',
                sequence INTEGER DEFAULT 0,
                FOREIGN KEY (intent_id) REFERENCES pipelines(intent_id)
            );

            CREATE INDEX IF NOT EXISTS idx_traces_intent ON traces(intent_id);
            CREATE INDEX IF NOT EXISTS idx_traces_event ON traces(event_type);

            CREATE TABLE IF NOT EXISTS autonomy_settings (
                id INTEGER PRIMARY KEY CHECK (id = 1),
                profile TEXT DEFAULT 'DEFAULT',
                override_matrix TEXT DEFAULT '{}',
                updated_at TEXT DEFAULT ''
            );
        """)
        self._conn.commit()

    def save_result(
        self,
        result: ExecutionResult,
        intent: str = "",
        constraints: list[str] | None = None,
        context: dict | None = None,
        hashed_traces: list[dict] | None = None,
    ) -> None:
        """Save a pipeline execution result.

        Args:
            result: The execution result.
            intent: Original intent string.
            constraints: Original constraints.
            context: Original context.
            hashed_traces: Optional list of dicts with keys: trace_id, hash, previous_hash, sequence.
                           If provided, hash chain data is stored alongside traces.
        """
        now = datetime.now(timezone.utc).isoformat()
        self._conn.execute(
            """INSERT OR REPLACE INTO pipelines
               (intent_id, intent, constraints, context, status, success, output,
                sub_tasks, rejected_tasks, graph_summary, created_at, completed_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (
                result.intent_id,
                intent,
                json.dumps(constraints or []),
                json.dumps(context or {}),
                "completed",
                1 if result.success else 0,
                result.output,
                json.dumps([st.model_dump() for st in result.sub_tasks], default=str),
                json.dumps([st.model_dump() for st in result.rejected_tasks], default=str),
                json.dumps(result.graph_summary, default=str),
                now,
                now,
            ),
        )

        # Build hash lookup if provided
        hash_lookup: dict[str, dict] = {}
        if hashed_traces:
            for ht in hashed_traces:
                hash_lookup[ht["trace_id"]] = ht

        # Save traces with optional hash data
        for trace in result.traces:
            self._save_trace(result.intent_id, trace, hash_lookup.get(trace.id))

        self._conn.commit()

    def _save_trace(self, intent_id: str, trace: Trace, hash_data: dict | None = None) -> None:
        """Save a single trace event with optional hash chain data."""
        h = hash_data or {}
        self._conn.execute(
            """INSERT OR REPLACE INTO traces
               (id, intent_id, task_id, event_type, description, details,
                risk_level, l0_passed, timestamp, hash, previous_hash, sequence)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (
                trace.id,
                intent_id,
                trace.task_id,
                trace.event_type,
                trace.description,
                json.dumps(trace.details, default=str),
                trace.risk_level.value if trace.risk_level else None,
                1 if trace.l0_passed is True else (0 if trace.l0_passed is False else None),
                trace.timestamp.isoformat(),
                h.get("hash", ""),
                h.get("previous_hash", ""),
                h.get("sequence", 0),
            ),
        )

    def get_result(self, intent_id: str) -> ExecutionResult | None:
        """Retrieve a pipeline result by intent_id."""
        row = self._conn.execute(
            "SELECT * FROM pipelines WHERE intent_id = ?", (intent_id,)
        ).fetchone()
        if not row:
            return None

        traces = self.get_traces(intent_id)
        sub_tasks = self._parse_subtasks(row["sub_tasks"])
        rejected_tasks = self._parse_subtasks(row["rejected_tasks"])

        return ExecutionResult(
            intent_id=row["intent_id"],
            output=row["output"],
            success=bool(row["success"]),
            sub_tasks=sub_tasks,
            rejected_tasks=rejected_tasks,
            traces=traces,
            graph_summary=json.loads(row["graph_summary"]) if row["graph_summary"] else {},
        )

    def get_traces(self, intent_id: str) -> list[Trace]:
        """Retrieve all traces for a pipeline."""
        rows = self._conn.execute(
            "SELECT * FROM traces WHERE intent_id = ? ORDER BY timestamp",
            (intent_id,),
        ).fetchall()

        return [self._row_to_trace(row) for row in rows]

    def list_pipelines(self, limit: int = 50, offset: int = 0) -> list[dict]:
        """List pipeline runs, newest first."""
        rows = self._conn.execute(
            """SELECT intent_id, intent, status, success, created_at, completed_at
               FROM pipelines ORDER BY completed_at DESC LIMIT ? OFFSET ?""",
            (limit, offset),
        ).fetchall()

        return [
            {
                "intent_id": row["intent_id"],
                "intent": row["intent"],
                "status": row["status"],
                "success": bool(row["success"]),
                "created_at": row["created_at"],
                "completed_at": row["completed_at"],
            }
            for row in rows
        ]

    @property
    def pipeline_count(self) -> int:
        """Total number of stored pipelines."""
        row = self._conn.execute("SELECT COUNT(*) as cnt FROM pipelines").fetchone()
        return row["cnt"]

    def _row_to_trace(self, row) -> Trace:
        risk = RiskLevel(row["risk_level"]) if row["risk_level"] else None
        l0 = None
        if row["l0_passed"] is not None:
            l0 = bool(row["l0_passed"])

        return Trace(
            id=row["id"],
            intent_id=row["intent_id"],
            task_id=row["task_id"],
            event_type=row["event_type"],
            description=row["description"],
            details=json.loads(row["details"]) if row["details"] else {},
            risk_level=risk,
            l0_passed=l0,
            timestamp=datetime.fromisoformat(row["timestamp"]) if row["timestamp"] else datetime.now(timezone.utc),
        )

    def _parse_subtasks(self, data: str) -> list[SubTask]:
        try:
            items = json.loads(data) if data else []
            return [SubTask(**item) for item in items]
        except Exception:
            return []

    def save_autonomy_settings(self, settings: AutonomySettings) -> None:
        """Persist autonomy settings (single-row upsert)."""
        self._conn.execute(
            """INSERT OR REPLACE INTO autonomy_settings (id, profile, override_matrix, updated_at)
               VALUES (1, ?, ?, ?)""",
            (
                settings.profile.value,
                json.dumps(settings.override_matrix),
                settings.updated_at.isoformat(),
            ),
        )
        self._conn.commit()

    def get_autonomy_settings(self) -> AutonomySettings:
        """Load autonomy settings from DB. Returns DEFAULT if not set."""
        row = self._conn.execute(
            "SELECT profile, override_matrix, updated_at FROM autonomy_settings WHERE id = 1"
        ).fetchone()
        if not row:
            return AutonomySettings()
        return AutonomySettings(
            profile=AutonomyProfile(row["profile"]),
            override_matrix=json.loads(row["override_matrix"]) if row["override_matrix"] else {},
            updated_at=datetime.fromisoformat(row["updated_at"]) if row["updated_at"] else datetime.now(timezone.utc),
        )

    def get_traces_with_hashes(self, intent_id: str) -> list[dict]:
        """Retrieve traces with hash chain data for replay."""
        rows = self._conn.execute(
            """SELECT id, intent_id, task_id, event_type, description, details,
                      risk_level, l0_passed, timestamp, hash, previous_hash, sequence
               FROM traces WHERE intent_id = ? ORDER BY sequence, timestamp""",
            (intent_id,),
        ).fetchall()

        return [
            {
                "trace_id": row["id"],
                "intent_id": row["intent_id"],
                "task_id": row["task_id"],
                "event_type": row["event_type"],
                "description": row["description"],
                "details": json.loads(row["details"]) if row["details"] else {},
                "risk_level": row["risk_level"],
                "l0_passed": bool(row["l0_passed"]) if row["l0_passed"] is not None else None,
                "timestamp": row["timestamp"],
                "hash": row["hash"] or "",
                "previous_hash": row["previous_hash"] or "",
                "sequence": row["sequence"] or 0,
            }
            for row in rows
        ]

    def close(self) -> None:
        """Close the database connection."""
        self._conn.close()
