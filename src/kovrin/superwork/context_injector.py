"""
Context Injector — Project-Aware RAG via ChromaDB

Indexes project files into a local vector database and retrieves
relevant context chunks for each task. Uses sentence-transformers
for local embedding generation (no cloud API needed).

Supports incremental re-indexing: only changed files are re-processed.
"""

from __future__ import annotations

import hashlib
import logging
from pathlib import Path
from typing import Any

logger = logging.getLogger(__name__)

# File extensions worth indexing
INDEXABLE_EXTENSIONS = {
    ".py",
    ".ts",
    ".tsx",
    ".js",
    ".jsx",
    ".md",
    ".rst",
    ".txt",
    ".toml",
    ".yaml",
    ".yml",
    ".json",
    ".cfg",
    ".ini",
}

# Skip files larger than 500 KB
MAX_FILE_SIZE = 512_000

# Chunking parameters
CHUNK_SIZE = 1000
CHUNK_OVERLAP = 200

# Directories to exclude from indexing
EXCLUDED_DIRS = {
    ".git",
    ".venv",
    "venv",
    "node_modules",
    "__pycache__",
    ".kovrin",
    ".mypy_cache",
    ".ruff_cache",
    ".pytest_cache",
    "dist",
    "build",
    ".next",
}


class ContextInjector:
    """Indexes project files and retrieves relevant context via RAG.

    Uses ChromaDB for local vector storage and sentence-transformers
    for embedding generation. Both are lazy-imported to keep the base
    ``kovrin`` package dependency-free.
    """

    def __init__(
        self,
        project_path: str | Path,
        db_path: str | Path | None = None,
        embedding_model: str = "all-MiniLM-L6-v2",
    ):
        """Initialize Context Injector.

        Args:
            project_path: Root directory of the project to index.
            db_path: Where to store the ChromaDB data.
                Defaults to ``{project}/.kovrin/context_db/``.
            embedding_model: Sentence-transformer model name.
        """
        self._project_path = Path(project_path).resolve()
        self._db_path = Path(db_path) if db_path else self._project_path / ".kovrin" / "context_db"
        self._embedding_model_name = embedding_model
        self._client: Any = None
        self._collection: Any = None
        self._file_hashes: dict[str, str] = {}

    def _ensure_initialized(self) -> None:
        """Lazy-initialize ChromaDB and sentence-transformers."""
        if self._client is not None:
            return

        import chromadb
        from chromadb.utils import embedding_functions

        self._db_path.mkdir(parents=True, exist_ok=True)
        self._client = chromadb.PersistentClient(path=str(self._db_path))

        ef = embedding_functions.SentenceTransformerEmbeddingFunction(
            model_name=self._embedding_model_name
        )
        self._collection = self._client.get_or_create_collection(
            name="project_context",
            embedding_function=ef,
        )
        logger.info(
            "ContextInjector initialized (model=%s, db=%s)",
            self._embedding_model_name,
            self._db_path,
        )

    async def index_project(self) -> int:
        """Full index of the project directory.

        Returns:
            Number of chunks indexed.
        """
        self._ensure_initialized()
        total_chunks = 0
        for file_path in self._iter_files():
            total_chunks += self._index_file(file_path)
        logger.info("Indexed %d chunks from %s", total_chunks, self._project_path)
        return total_chunks

    async def update_on_change(self, changed_files: list[str]) -> int:
        """Incremental re-index of only changed files.

        Args:
            changed_files: List of absolute or relative file paths.

        Returns:
            Number of chunks updated.
        """
        self._ensure_initialized()
        chunks_updated = 0
        for file_str in changed_files:
            file_path = Path(file_str)
            if not file_path.is_absolute():
                file_path = self._project_path / file_path
            if file_path.exists() and file_path.suffix in INDEXABLE_EXTENSIONS:
                self._delete_file_chunks(file_path)
                chunks_updated += self._index_file(file_path)
        return chunks_updated

    def get_relevant_context(self, query: str, top_k: int = 5) -> str:
        """Retrieve relevant project context for a task description.

        Args:
            query: Natural language description of the task.
            top_k: Number of context chunks to retrieve.

        Returns:
            Formatted string of relevant code/doc snippets.
        """
        self._ensure_initialized()
        results = self._collection.query(
            query_texts=[query],
            n_results=top_k,
        )
        return self._format_results(results)

    @property
    def chunk_count(self) -> int:
        """Number of chunks currently in the collection."""
        if self._collection is None:
            return 0
        return self._collection.count()

    # ── Internal Methods ─────────────────────────────────────

    def _iter_files(self):
        """Yield indexable files in the project directory."""
        for path in self._project_path.rglob("*"):
            if (
                path.is_file()
                and path.suffix in INDEXABLE_EXTENSIONS
                and path.stat().st_size <= MAX_FILE_SIZE
                and not self._is_excluded(path)
            ):
                yield path

    def _is_excluded(self, path: Path) -> bool:
        """Check if a path should be excluded from indexing."""
        return any(part in EXCLUDED_DIRS for part in path.parts)

    def _index_file(self, file_path: Path) -> int:
        """Index a single file. Returns number of chunks created."""
        try:
            content = file_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            return 0

        content_hash = hashlib.md5(content.encode()).hexdigest()
        rel_path = str(file_path.relative_to(self._project_path))

        # Skip if unchanged
        if self._file_hashes.get(rel_path) == content_hash:
            return 0
        self._file_hashes[rel_path] = content_hash

        chunks = self._chunk_text(content, rel_path)
        if not chunks:
            return 0

        ids = [f"{rel_path}::{i}" for i in range(len(chunks))]
        documents = [c["text"] for c in chunks]
        metadatas = [
            {
                "file": rel_path,
                "chunk_index": c["index"],
                "type": file_path.suffix,
            }
            for c in chunks
        ]

        self._collection.upsert(ids=ids, documents=documents, metadatas=metadatas)
        return len(chunks)

    def _delete_file_chunks(self, file_path: Path) -> None:
        """Delete all chunks for a given file."""
        rel_path = str(file_path.relative_to(self._project_path))
        try:
            results = self._collection.get(where={"file": rel_path})
            if results["ids"]:
                self._collection.delete(ids=results["ids"])
        except Exception:
            pass

    @staticmethod
    def _chunk_text(content: str, file_path: str) -> list[dict]:
        """Split content into overlapping chunks with file path prefix."""
        chunks: list[dict] = []
        step = max(CHUNK_SIZE - CHUNK_OVERLAP, 1)
        for i in range(0, len(content), step):
            chunk_text = content[i : i + CHUNK_SIZE]
            if chunk_text.strip():
                chunks.append(
                    {
                        "text": f"[{file_path}]\n{chunk_text}",
                        "index": len(chunks),
                    }
                )
        return chunks

    @staticmethod
    def _format_results(results: dict) -> str:
        """Format ChromaDB query results into a readable context string."""
        if not results or not results.get("documents"):
            return ""
        parts: list[str] = []
        for doc_list, meta_list in zip(results["documents"], results["metadatas"], strict=False):
            for doc, meta in zip(doc_list, meta_list, strict=False):
                parts.append(f"--- {meta.get('file', 'unknown')} ---\n{doc}")
        return "\n\n".join(parts)
