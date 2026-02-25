"""
Kovrin Pipeline Persistence

Stores pipeline results and trace events for durability
across server restarts. Supports SQLite and PostgreSQL
via the ``kovrin.storage.db`` connection wrapper.

Schema:
- pipelines: stores ExecutionResult metadata
- traces: stores individual trace events with hash chain data
"""

import json
from datetime import UTC, datetime

from kovrin.core.models import (
    AutonomyProfile,
    AutonomySettings,
    ExecutionResult,
    RiskLevel,
    SubTask,
    Trace,
)
from kovrin.storage.db import connect


class PipelineRepository:
    """Database-backed storage for pipeline results and traces."""

    def __init__(self, db_url: str = "kovrin.db"):
        """Initialize repository.

        Args:
            db_url: Database URL. Use ``postgresql://...`` for PostgreSQL
                    or a file path / ``:memory:`` for SQLite.
        """
        self._db_url = db_url
        self._conn = connect(db_url)
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

            CREATE TABLE IF NOT EXISTS token_usage (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                intent_id TEXT NOT NULL,
                task_id TEXT DEFAULT '',
                model TEXT DEFAULT '',
                provider TEXT DEFAULT '',
                input_tokens INTEGER DEFAULT 0,
                output_tokens INTEGER DEFAULT 0,
                cost_usd REAL DEFAULT 0.0,
                event_type TEXT DEFAULT 'task_execution',
                timestamp TEXT DEFAULT '',
                FOREIGN KEY (intent_id) REFERENCES pipelines(intent_id)
            );

            CREATE INDEX IF NOT EXISTS idx_token_usage_intent ON token_usage(intent_id);
            CREATE INDEX IF NOT EXISTS idx_token_usage_timestamp ON token_usage(timestamp)
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
        now = datetime.now(UTC).isoformat()
        self._conn.upsert(
            "pipelines",
            "intent_id",
            [
                "intent_id",
                "intent",
                "constraints",
                "context",
                "status",
                "success",
                "output",
                "sub_tasks",
                "rejected_tasks",
                "graph_summary",
                "created_at",
                "completed_at",
            ],
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
        self._conn.upsert(
            "traces",
            "id",
            [
                "id",
                "intent_id",
                "task_id",
                "event_type",
                "description",
                "details",
                "risk_level",
                "l0_passed",
                "timestamp",
                "hash",
                "previous_hash",
                "sequence",
            ],
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
        return row["cnt"] if row else 0

    def _row_to_trace(self, row: dict) -> Trace:
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
            timestamp=datetime.fromisoformat(row["timestamp"])
            if row["timestamp"]
            else datetime.now(UTC),
        )

    def _parse_subtasks(self, data: str) -> list[SubTask]:
        try:
            items = json.loads(data) if data else []
            return [SubTask(**item) for item in items]
        except Exception:
            return []

    def save_autonomy_settings(self, settings: AutonomySettings) -> None:
        """Persist autonomy settings (single-row upsert)."""
        self._conn.upsert(
            "autonomy_settings",
            "id",
            ["id", "profile", "override_matrix", "updated_at"],
            (
                1,
                settings.profile.value,
                json.dumps(settings.override_matrix),
                settings.updated_at.isoformat(),
            ),
        )
        self._conn.commit()

    def get_autonomy_settings(self) -> AutonomySettings:
        """Load autonomy settings from DB. Returns DEFAULT if not set."""
        row = self._conn.execute(
            "SELECT profile, override_matrix, updated_at FROM autonomy_settings WHERE id = ?",
            (1,),
        ).fetchone()
        if not row:
            return AutonomySettings()
        return AutonomySettings(
            profile=AutonomyProfile(row["profile"]),
            override_matrix=json.loads(row["override_matrix"]) if row["override_matrix"] else {},
            updated_at=datetime.fromisoformat(row["updated_at"])
            if row["updated_at"]
            else datetime.now(UTC),
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

    def save_token_usage(
        self,
        intent_id: str,
        task_id: str,
        model: str,
        provider: str,
        input_tokens: int,
        output_tokens: int,
        cost_usd: float,
        event_type: str = "task_execution",
    ) -> None:
        """Record token usage for a single LLM call."""
        self._conn.execute(
            """INSERT INTO token_usage
               (intent_id, task_id, model, provider, input_tokens, output_tokens,
                cost_usd, event_type, timestamp)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (
                intent_id,
                task_id,
                model,
                provider,
                input_tokens,
                output_tokens,
                cost_usd,
                event_type,
                datetime.now(UTC).isoformat(),
            ),
        )
        self._conn.commit()

    def get_costs(
        self,
        period_days: int = 30,
        intent_id: str | None = None,
    ) -> dict:
        """Get cost summary, optionally filtered by intent_id or time period.

        Returns:
            Dict with total_cost_usd, per_model breakdown, per_pipeline breakdown,
            and daily_series.
        """
        base_where = "WHERE timestamp >= ?"
        params: list = [
            (datetime.now(UTC).replace(hour=0, minute=0, second=0)
             .__class__(datetime.now(UTC).year, datetime.now(UTC).month, datetime.now(UTC).day, tzinfo=UTC)
             - __import__("datetime").timedelta(days=period_days)).isoformat()
        ]

        if intent_id:
            base_where += " AND intent_id = ?"
            params.append(intent_id)

        # Total
        row = self._conn.execute(
            f"""SELECT COALESCE(SUM(cost_usd), 0) as total,
                       COALESCE(SUM(input_tokens), 0) as input_t,
                       COALESCE(SUM(output_tokens), 0) as output_t
                FROM token_usage {base_where}""",
            tuple(params),
        ).fetchone()

        total_cost = row["total"] if row else 0.0
        total_input = row["input_t"] if row else 0
        total_output = row["output_t"] if row else 0

        # Per model
        model_rows = self._conn.execute(
            f"""SELECT model,
                       SUM(input_tokens) as input_t,
                       SUM(output_tokens) as output_t,
                       SUM(cost_usd) as cost,
                       COUNT(*) as calls
                FROM token_usage {base_where}
                GROUP BY model ORDER BY cost DESC""",
            tuple(params),
        ).fetchall()

        per_model = {
            r["model"]: {
                "input_tokens": r["input_t"],
                "output_tokens": r["output_t"],
                "cost_usd": round(r["cost"], 6),
                "calls": r["calls"],
            }
            for r in model_rows
        }

        # Per pipeline (top 20)
        pipeline_rows = self._conn.execute(
            f"""SELECT tu.intent_id,
                       COALESCE(p.intent, '') as intent,
                       SUM(tu.input_tokens) as input_t,
                       SUM(tu.output_tokens) as output_t,
                       SUM(tu.cost_usd) as cost,
                       COUNT(*) as calls
                FROM token_usage tu
                LEFT JOIN pipelines p ON tu.intent_id = p.intent_id
                {base_where.replace('timestamp', 'tu.timestamp')}
                GROUP BY tu.intent_id ORDER BY cost DESC LIMIT 20""",
            tuple(params),
        ).fetchall()

        per_pipeline = [
            {
                "intent_id": r["intent_id"],
                "intent": r["intent"],
                "input_tokens": r["input_t"],
                "output_tokens": r["output_t"],
                "cost_usd": round(r["cost"], 6),
                "calls": r["calls"],
            }
            for r in pipeline_rows
        ]

        # Daily series
        daily_rows = self._conn.execute(
            f"""SELECT DATE(timestamp) as day,
                       SUM(cost_usd) as cost,
                       SUM(input_tokens) as input_t,
                       SUM(output_tokens) as output_t
                FROM token_usage {base_where}
                GROUP BY DATE(timestamp) ORDER BY day""",
            tuple(params),
        ).fetchall()

        daily_series = [
            {
                "date": r["day"],
                "cost_usd": round(r["cost"], 6),
                "input_tokens": r["input_t"],
                "output_tokens": r["output_t"],
            }
            for r in daily_rows
        ]

        return {
            "total_cost_usd": round(total_cost, 6),
            "total_input_tokens": total_input,
            "total_output_tokens": total_output,
            "per_model": per_model,
            "per_pipeline": per_pipeline,
            "daily_series": daily_series,
            "period_days": period_days,
        }

    def close(self) -> None:
        """Close the database connection."""
        self._conn.close()
