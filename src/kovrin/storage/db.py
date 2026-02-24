"""
Kovrin Database Connection Abstraction

Provides a unified interface for SQLite and PostgreSQL.
Detects the backend from the connection URL:
- ``postgresql://`` or ``postgres://`` → psycopg (PostgreSQL)
- anything else (file path, ``:memory:``) → sqlite3

Usage::

    from kovrin.storage.db import connect

    conn = connect(os.environ.get("DATABASE_URL", "kovrin.db"))
    conn.execute("CREATE TABLE IF NOT EXISTS t (id TEXT PRIMARY KEY)")
    conn.execute("INSERT INTO t (id) VALUES (?)", ("abc",))
    conn.commit()
    conn.close()

The ``?`` placeholder is automatically converted to ``%s`` for PostgreSQL.
"""

from __future__ import annotations

import re
import sqlite3
from typing import Any


class DbConnection:
    """Unified database connection wrapper."""

    def __init__(self, conn: Any, *, is_postgres: bool = False) -> None:
        self._conn = conn
        self._cursor: Any = None
        self.is_postgres = is_postgres

    def _convert_sql(self, sql: str) -> str:
        """Convert SQLite-style ``?`` placeholders to ``%s`` for PostgreSQL."""
        if not self.is_postgres:
            return sql
        return sql.replace("?", "%s")

    def _convert_ddl(self, sql: str) -> str:
        """Convert SQLite DDL to PostgreSQL DDL."""
        if not self.is_postgres:
            return sql
        # INTEGER PRIMARY KEY AUTOINCREMENT → SERIAL PRIMARY KEY
        sql = re.sub(
            r"INTEGER\s+PRIMARY\s+KEY\s+AUTOINCREMENT",
            "SERIAL PRIMARY KEY",
            sql,
            flags=re.IGNORECASE,
        )
        # INTEGER PRIMARY KEY CHECK (id = 1) → INTEGER PRIMARY KEY
        sql = re.sub(
            r"INTEGER\s+PRIMARY\s+KEY\s+CHECK\s*\([^)]+\)",
            "INTEGER PRIMARY KEY",
            sql,
            flags=re.IGNORECASE,
        )
        return sql

    def execute(self, sql: str, params: tuple = ()) -> DbConnection:
        """Execute a single SQL statement. Returns self for chaining."""
        sql = self._convert_ddl(self._convert_sql(sql))
        if self.is_postgres:
            self._cursor = self._conn.cursor()
            self._cursor.execute(sql, params or None)
        else:
            self._cursor = self._conn.execute(sql, params)
        return self

    def executescript(self, sql: str) -> None:
        """Execute multiple SQL statements separated by semicolons."""
        if self.is_postgres:
            sql = self._convert_ddl(sql)
            cur = self._conn.cursor()
            # Split on semicolons, execute non-empty statements
            for stmt in sql.split(";"):
                stmt = stmt.strip()
                if stmt:
                    cur.execute(stmt)
            self._conn.commit()
        else:
            self._conn.executescript(sql)

    def fetchone(self) -> dict[str, Any] | None:
        """Fetch one row as a dict."""
        if self._cursor is None:
            return None
        row = self._cursor.fetchone()
        if row is None:
            return None
        if self.is_postgres:
            return dict(row)
        # sqlite3.Row → dict
        return dict(row)

    def fetchall(self) -> list[dict[str, Any]]:
        """Fetch all rows as list of dicts."""
        if self._cursor is None:
            return []
        rows = self._cursor.fetchall()
        if self.is_postgres:
            return [dict(r) for r in rows]
        return [dict(r) for r in rows]

    def commit(self) -> None:
        """Commit the current transaction."""
        self._conn.commit()

    def close(self) -> None:
        """Close the connection."""
        self._conn.close()

    def upsert(
        self,
        table: str,
        pk: str,
        columns: list[str],
        values: tuple,
    ) -> None:
        """Insert or update a row.

        Args:
            table: Table name.
            pk: Primary key column name.
            columns: All column names (including pk).
            values: Values tuple matching columns order.
        """
        placeholders = ", ".join(["?"] * len(columns))
        col_list = ", ".join(columns)

        if self.is_postgres:
            placeholders = ", ".join(["%s"] * len(columns))
            non_pk = [c for c in columns if c != pk]
            update_clause = ", ".join(f"{c} = EXCLUDED.{c}" for c in non_pk)
            sql = (
                f"INSERT INTO {table} ({col_list}) VALUES ({placeholders}) "
                f"ON CONFLICT ({pk}) DO UPDATE SET {update_clause}"
            )
            cur = self._conn.cursor()
            cur.execute(sql, values)
        else:
            sql = f"INSERT OR REPLACE INTO {table} ({col_list}) VALUES ({placeholders})"
            self._conn.execute(sql, values)


def connect(db_url: str) -> DbConnection:
    """Create a database connection from a URL or path.

    Args:
        db_url: PostgreSQL URL (``postgresql://...`` or ``postgres://...``)
                or SQLite path (file path or ``:memory:``).

    Returns:
        A unified DbConnection wrapper.
    """
    if db_url.startswith(("postgresql://", "postgres://")):
        try:
            import psycopg
            from psycopg.rows import dict_row
        except ImportError:
            raise ImportError(
                "PostgreSQL support requires psycopg. Install with: pip install 'kovrin[api]'"
            ) from None

        conn = psycopg.connect(db_url, row_factory=dict_row, autocommit=False)
        return DbConnection(conn, is_postgres=True)

    # SQLite fallback
    conn = sqlite3.connect(db_url, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return DbConnection(conn, is_postgres=False)
