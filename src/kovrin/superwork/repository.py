"""
SuperWork Pipeline Persistence

Stores sessions, proposals, metrics, and events for durability
across server restarts. Supports SQLite and PostgreSQL
via the ``kovrin.storage.db`` connection wrapper.

Schema:
- superwork_sessions: supervisor session state
- superwork_proposals: orchestrator task proposals
- superwork_metrics: point-in-time metrics snapshots
- superwork_events: task completion events from session watcher
"""

import json
from datetime import UTC, datetime

from kovrin.storage.db import connect
from kovrin.superwork.models import (
    MetricsSnapshot,
    ProposalStatus,
    SessionStatus,
    SuperWorkSession,
    TaskCompletionEvent,
    TaskProposal,
)


class SuperWorkRepository:
    """Database-backed storage for SuperWork sessions and proposals."""

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
        """Create SuperWork tables if they don't exist."""
        self._conn.executescript("""
            CREATE TABLE IF NOT EXISTS superwork_sessions (
                id TEXT PRIMARY KEY,
                project_path TEXT NOT NULL,
                status TEXT DEFAULT 'INITIALIZING',
                started_at TEXT DEFAULT '',
                stopped_at TEXT DEFAULT ''
            );

            CREATE TABLE IF NOT EXISTS superwork_proposals (
                id TEXT PRIMARY KEY,
                session_id TEXT NOT NULL,
                title TEXT DEFAULT '',
                description TEXT DEFAULT '',
                rationale TEXT DEFAULT '',
                risk_level TEXT DEFAULT 'LOW',
                estimated_tokens INTEGER DEFAULT 0,
                auto_execute INTEGER DEFAULT 0,
                dependencies TEXT DEFAULT '[]',
                status TEXT DEFAULT 'PENDING',
                priority INTEGER DEFAULT 0,
                created_at TEXT DEFAULT '',
                resolved_at TEXT DEFAULT '',
                FOREIGN KEY (session_id) REFERENCES superwork_sessions(id)
            );

            CREATE TABLE IF NOT EXISTS superwork_metrics (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                session_id TEXT NOT NULL,
                tasks_completed INTEGER DEFAULT 0,
                tasks_failed INTEGER DEFAULT 0,
                tokens_used INTEGER DEFAULT 0,
                cost_usd REAL DEFAULT 0.0,
                velocity REAL DEFAULT 0.0,
                success_rate REAL DEFAULT 1.0,
                session_duration INTEGER DEFAULT 0,
                timestamp TEXT DEFAULT '',
                FOREIGN KEY (session_id) REFERENCES superwork_sessions(id)
            );

            CREATE TABLE IF NOT EXISTS superwork_events (
                id TEXT PRIMARY KEY,
                session_id TEXT NOT NULL,
                completed_task TEXT DEFAULT '',
                output_summary TEXT DEFAULT '',
                files_changed TEXT DEFAULT '[]',
                errors TEXT DEFAULT '[]',
                duration_seconds INTEGER DEFAULT 0,
                timestamp TEXT DEFAULT '',
                FOREIGN KEY (session_id) REFERENCES superwork_sessions(id)
            );

            CREATE INDEX IF NOT EXISTS idx_sw_proposals_session
                ON superwork_proposals(session_id);
            CREATE INDEX IF NOT EXISTS idx_sw_metrics_session
                ON superwork_metrics(session_id);
            CREATE INDEX IF NOT EXISTS idx_sw_events_session
                ON superwork_events(session_id)
        """)

    # ── Sessions ─────────────────────────────────────────────

    def save_session(self, session: SuperWorkSession) -> None:
        """Insert or replace a SuperWork session."""
        self._conn.upsert(
            "superwork_sessions",
            "id",
            ["id", "project_path", "status", "started_at", "stopped_at"],
            (
                session.id,
                session.project_path,
                session.status.value,
                session.started_at.isoformat(),
                session.stopped_at.isoformat() if session.stopped_at else "",
            ),
        )
        self._conn.commit()

    def get_session(self, session_id: str) -> SuperWorkSession | None:
        """Retrieve a session by ID."""
        row = self._conn.execute(
            "SELECT * FROM superwork_sessions WHERE id = ?", (session_id,)
        ).fetchone()
        if not row:
            return None
        return self._row_to_session(row)

    def list_sessions(self, limit: int = 50) -> list[SuperWorkSession]:
        """List recent sessions, newest first."""
        rows = self._conn.execute(
            "SELECT * FROM superwork_sessions ORDER BY started_at DESC LIMIT ?",
            (limit,),
        ).fetchall()
        return [self._row_to_session(r) for r in rows]

    def update_session_status(self, session_id: str, status: SessionStatus) -> None:
        """Update session status."""
        params: list = [status.value]
        sql = "UPDATE superwork_sessions SET status = ?"
        if status == SessionStatus.STOPPED:
            sql += ", stopped_at = ?"
            params.append(datetime.now(UTC).isoformat())
        sql += " WHERE id = ?"
        params.append(session_id)
        self._conn.execute(sql, tuple(params))
        self._conn.commit()

    # ── Proposals ────────────────────────────────────────────

    def save_proposal(self, proposal: TaskProposal, session_id: str) -> None:
        """Insert or replace a task proposal."""
        self._conn.upsert(
            "superwork_proposals",
            "id",
            ["id", "session_id", "title", "description", "rationale",
             "risk_level", "estimated_tokens", "auto_execute",
             "dependencies", "status", "priority", "created_at", "resolved_at"],
            (
                proposal.id,
                session_id,
                proposal.title,
                proposal.description,
                proposal.rationale,
                proposal.risk_level.value,
                proposal.estimated_tokens,
                int(proposal.auto_execute),
                json.dumps(proposal.dependencies),
                proposal.status.value,
                proposal.priority,
                proposal.created_at.isoformat(),
                proposal.resolved_at.isoformat() if proposal.resolved_at else "",
            ),
        )
        self._conn.commit()

    def get_proposals(
        self,
        session_id: str,
        status: ProposalStatus | None = None,
    ) -> list[TaskProposal]:
        """Get proposals for a session, optionally filtered by status."""
        if status:
            rows = self._conn.execute(
                """SELECT * FROM superwork_proposals
                   WHERE session_id = ? AND status = ?
                   ORDER BY priority ASC""",
                (session_id, status.value),
            ).fetchall()
        else:
            rows = self._conn.execute(
                """SELECT * FROM superwork_proposals
                   WHERE session_id = ?
                   ORDER BY priority ASC""",
                (session_id,),
            ).fetchall()
        return [self._row_to_proposal(r) for r in rows]

    def update_proposal_status(self, proposal_id: str, status: ProposalStatus) -> None:
        """Update a proposal's status (approve, skip, etc.)."""
        resolved_at = ""
        if status in (ProposalStatus.APPROVED, ProposalStatus.SKIPPED):
            resolved_at = datetime.now(UTC).isoformat()
        self._conn.execute(
            """UPDATE superwork_proposals
               SET status = ?, resolved_at = ?
               WHERE id = ?""",
            (status.value, resolved_at, proposal_id),
        )
        self._conn.commit()

    # ── Metrics ──────────────────────────────────────────────

    def save_metrics(self, session_id: str, metrics: MetricsSnapshot) -> None:
        """Append a metrics snapshot."""
        self._conn.execute(
            """INSERT INTO superwork_metrics
               (session_id, tasks_completed, tasks_failed, tokens_used,
                cost_usd, velocity, success_rate, session_duration, timestamp)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (
                session_id,
                metrics.tasks_completed,
                metrics.tasks_failed,
                metrics.tokens_used,
                metrics.cost_usd,
                metrics.velocity_tasks_per_hour,
                metrics.success_rate,
                metrics.session_duration_seconds,
                metrics.timestamp.isoformat(),
            ),
        )
        self._conn.commit()

    def get_latest_metrics(self, session_id: str) -> MetricsSnapshot | None:
        """Get the most recent metrics snapshot for a session."""
        row = self._conn.execute(
            """SELECT * FROM superwork_metrics
               WHERE session_id = ?
               ORDER BY timestamp DESC LIMIT 1""",
            (session_id,),
        ).fetchone()
        if not row:
            return None
        return self._row_to_metrics(row)

    def get_metrics_history(self, session_id: str, limit: int = 100) -> list[MetricsSnapshot]:
        """Get metrics history for a session, newest first."""
        rows = self._conn.execute(
            """SELECT * FROM superwork_metrics
               WHERE session_id = ?
               ORDER BY timestamp DESC LIMIT ?""",
            (session_id, limit),
        ).fetchall()
        return [self._row_to_metrics(r) for r in rows]

    # ── Events ───────────────────────────────────────────────

    def save_event(self, session_id: str, event: TaskCompletionEvent) -> None:
        """Save a task completion event."""
        self._conn.upsert(
            "superwork_events",
            "id",
            ["id", "session_id", "completed_task", "output_summary",
             "files_changed", "errors", "duration_seconds", "timestamp"],
            (
                event.id,
                session_id,
                event.completed_task,
                event.output_summary,
                json.dumps(event.files_changed),
                json.dumps(event.errors),
                event.duration_seconds,
                event.timestamp.isoformat(),
            ),
        )
        self._conn.commit()

    def get_events(self, session_id: str, limit: int = 100) -> list[TaskCompletionEvent]:
        """Get events for a session, newest first."""
        rows = self._conn.execute(
            """SELECT * FROM superwork_events
               WHERE session_id = ?
               ORDER BY timestamp DESC LIMIT ?""",
            (session_id, limit),
        ).fetchall()
        return [self._row_to_event(r) for r in rows]

    # ── Helpers ──────────────────────────────────────────────

    def close(self) -> None:
        """Close the database connection."""
        self._conn.close()

    @staticmethod
    def _row_to_session(row: dict) -> SuperWorkSession:
        return SuperWorkSession(
            id=row["id"],
            project_path=row["project_path"],
            status=SessionStatus(row["status"]),
            started_at=datetime.fromisoformat(row["started_at"])
            if row["started_at"]
            else datetime.now(UTC),
            stopped_at=datetime.fromisoformat(row["stopped_at"]) if row["stopped_at"] else None,
        )

    @staticmethod
    def _row_to_proposal(row: dict) -> TaskProposal:
        from kovrin.core.models import RiskLevel

        return TaskProposal(
            id=row["id"],
            title=row["title"],
            description=row["description"],
            rationale=row["rationale"],
            risk_level=RiskLevel(row["risk_level"]),
            estimated_tokens=row["estimated_tokens"],
            auto_execute=bool(row["auto_execute"]),
            dependencies=json.loads(row["dependencies"]),
            status=ProposalStatus(row["status"]),
            priority=row["priority"],
            created_at=datetime.fromisoformat(row["created_at"])
            if row["created_at"]
            else datetime.now(UTC),
            resolved_at=datetime.fromisoformat(row["resolved_at"]) if row["resolved_at"] else None,
        )

    @staticmethod
    def _row_to_metrics(row: dict) -> MetricsSnapshot:
        return MetricsSnapshot(
            tasks_completed=row["tasks_completed"],
            tasks_failed=row["tasks_failed"],
            tokens_used=row["tokens_used"],
            cost_usd=row["cost_usd"],
            velocity_tasks_per_hour=row["velocity"],
            success_rate=row["success_rate"],
            session_duration_seconds=row["session_duration"],
            timestamp=datetime.fromisoformat(row["timestamp"])
            if row["timestamp"]
            else datetime.now(UTC),
        )

    @staticmethod
    def _row_to_event(row: dict) -> TaskCompletionEvent:
        return TaskCompletionEvent(
            id=row["id"],
            completed_task=row["completed_task"],
            output_summary=row["output_summary"],
            files_changed=json.loads(row["files_changed"]),
            errors=json.loads(row["errors"]),
            duration_seconds=row["duration_seconds"],
            timestamp=datetime.fromisoformat(row["timestamp"])
            if row["timestamp"]
            else datetime.now(UTC),
        )
