"""Tests for SuperWork Context Injector."""

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from kovrin.superwork.context_injector import (
    CHUNK_OVERLAP,
    CHUNK_SIZE,
    EXCLUDED_DIRS,
    INDEXABLE_EXTENSIONS,
    MAX_FILE_SIZE,
    ContextInjector,
)


class TestConstruction:
    def test_defaults(self, tmp_path):
        ci = ContextInjector(project_path=tmp_path)
        assert ci._project_path == tmp_path.resolve()
        assert ci._db_path == tmp_path.resolve() / ".kovrin" / "context_db"
        assert ci._embedding_model_name == "all-MiniLM-L6-v2"
        assert ci._client is None
        assert ci._collection is None
        assert ci._file_hashes == {}

    def test_custom_db_path(self, tmp_path):
        db = tmp_path / "custom_db"
        ci = ContextInjector(project_path=tmp_path, db_path=db)
        assert ci._db_path == db

    def test_chunk_count_before_init(self, tmp_path):
        ci = ContextInjector(project_path=tmp_path)
        assert ci.chunk_count == 0


class TestIsExcluded:
    def test_excluded_dirs(self, tmp_path):
        ci = ContextInjector(project_path=tmp_path)
        for d in [".git", "node_modules", "__pycache__", ".venv"]:
            path = tmp_path / d / "file.py"
            assert ci._is_excluded(path) is True

    def test_normal_path_not_excluded(self, tmp_path):
        ci = ContextInjector(project_path=tmp_path)
        path = tmp_path / "src" / "app.py"
        assert ci._is_excluded(path) is False

    def test_all_excluded_dirs_in_constant(self):
        expected = {".git", ".venv", "venv", "node_modules", "__pycache__",
                    ".kovrin", ".mypy_cache", ".ruff_cache", ".pytest_cache",
                    "dist", "build", ".next"}
        assert EXCLUDED_DIRS == expected


class TestChunkText:
    def test_short_content_single_chunk(self):
        chunks = ContextInjector._chunk_text("hello world", "file.py")
        assert len(chunks) == 1
        assert chunks[0]["text"].startswith("[file.py]\n")
        assert "hello world" in chunks[0]["text"]
        assert chunks[0]["index"] == 0

    def test_empty_content(self):
        chunks = ContextInjector._chunk_text("", "file.py")
        assert chunks == []

    def test_whitespace_only(self):
        chunks = ContextInjector._chunk_text("   \n  \n  ", "file.py")
        assert chunks == []

    def test_long_content_multiple_chunks(self):
        content = "x" * (CHUNK_SIZE * 3)
        chunks = ContextInjector._chunk_text(content, "big.py")
        assert len(chunks) > 1
        # Each chunk starts with the file path prefix
        for c in chunks:
            assert c["text"].startswith("[big.py]\n")

    def test_overlap(self):
        # Content exactly 2 chunks worth (with overlap)
        content = "a" * (CHUNK_SIZE + 100)
        chunks = ContextInjector._chunk_text(content, "f.py")
        assert len(chunks) >= 2

    def test_indices_sequential(self):
        content = "x" * 5000
        chunks = ContextInjector._chunk_text(content, "f.py")
        for i, c in enumerate(chunks):
            assert c["index"] == i


class TestFormatResults:
    def test_formats_results(self):
        results = {
            "documents": [["code snippet 1", "code snippet 2"]],
            "metadatas": [[{"file": "a.py"}, {"file": "b.py"}]],
        }
        out = ContextInjector._format_results(results)
        assert "--- a.py ---" in out
        assert "--- b.py ---" in out
        assert "code snippet 1" in out
        assert "code snippet 2" in out

    def test_empty_results(self):
        assert ContextInjector._format_results({}) == ""
        assert ContextInjector._format_results({"documents": []}) == ""
        assert ContextInjector._format_results(None) == ""

    def test_unknown_file_metadata(self):
        results = {
            "documents": [["text"]],
            "metadatas": [[{}]],
        }
        out = ContextInjector._format_results(results)
        assert "--- unknown ---" in out


class TestIterFiles:
    def test_yields_indexable_files(self, tmp_path):
        (tmp_path / "app.py").write_text("# python")
        (tmp_path / "config.toml").write_text("[section]")
        (tmp_path / "image.png").write_bytes(b"\x89PNG")

        ci = ContextInjector(project_path=tmp_path)
        files = list(ci._iter_files())
        names = {f.name for f in files}
        assert "app.py" in names
        assert "config.toml" in names
        assert "image.png" not in names

    def test_skips_excluded_dirs(self, tmp_path):
        excluded = tmp_path / "node_modules"
        excluded.mkdir()
        (excluded / "index.js").write_text("module.exports = {}")
        (tmp_path / "src" / "app.py").mkdir(parents=True, exist_ok=True)
        # Write to a file, not dir
        src_file = tmp_path / "src" / "main.py"
        src_file.write_text("print()")

        ci = ContextInjector(project_path=tmp_path)
        files = list(ci._iter_files())
        paths = [str(f) for f in files]
        assert not any("node_modules" in p for p in paths)

    def test_skips_large_files(self, tmp_path):
        big = tmp_path / "big.py"
        big.write_text("x" * (MAX_FILE_SIZE + 1))
        small = tmp_path / "small.py"
        small.write_text("x")

        ci = ContextInjector(project_path=tmp_path)
        files = list(ci._iter_files())
        names = {f.name for f in files}
        assert "small.py" in names
        assert "big.py" not in names


class TestIndexProject:
    @pytest.mark.asyncio
    async def test_indexes_files(self, tmp_path):
        (tmp_path / "app.py").write_text("def main(): pass")
        ci = ContextInjector(project_path=tmp_path)

        mock_collection = MagicMock()
        mock_collection.count.return_value = 1
        mock_collection.upsert = MagicMock()

        # Bypass lazy init by setting client/collection directly
        ci._client = MagicMock()
        ci._collection = mock_collection

        count = await ci.index_project()
        assert count >= 1
        mock_collection.upsert.assert_called()


class TestGetRelevantContext:
    def test_queries_collection(self, tmp_path):
        ci = ContextInjector(project_path=tmp_path)
        mock_collection = MagicMock()
        mock_collection.query.return_value = {
            "documents": [["relevant code"]],
            "metadatas": [[{"file": "module.py"}]],
        }
        ci._client = MagicMock()
        ci._collection = mock_collection

        result = ci.get_relevant_context("fix the bug")
        assert "relevant code" in result
        mock_collection.query.assert_called_once()
