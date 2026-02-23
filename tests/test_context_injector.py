"""Tests for SuperWork Context Injector."""

from pathlib import Path

from kovrin.superwork.context_injector import (
    CHUNK_OVERLAP,
    CHUNK_SIZE,
    EXCLUDED_DIRS,
    ContextInjector,
)


class TestContextInjectorImport:
    def test_import(self):
        assert ContextInjector is not None


class TestChunking:
    """Test _chunk_text static method (no ChromaDB needed)."""

    def test_chunk_small_text(self):
        chunks = ContextInjector._chunk_text("Hello world", "test.py")
        assert len(chunks) == 1
        assert "[test.py]" in chunks[0]["text"]
        assert "Hello world" in chunks[0]["text"]

    def test_chunk_large_text(self):
        text = "A" * (CHUNK_SIZE * 3)
        chunks = ContextInjector._chunk_text(text, "big.py")
        assert len(chunks) >= 3
        for c in chunks:
            # chunk text includes file path prefix, so slightly larger
            assert len(c["text"]) <= CHUNK_SIZE + len("[big.py]\n")

    def test_chunk_overlap_produces_multiple(self):
        text = "B" * (CHUNK_SIZE + 1)
        chunks = ContextInjector._chunk_text(text, "f.py")
        assert len(chunks) >= 2

    def test_empty_text(self):
        chunks = ContextInjector._chunk_text("", "empty.py")
        assert len(chunks) == 0

    def test_whitespace_only_text(self):
        chunks = ContextInjector._chunk_text("   \n\n  ", "blank.py")
        assert len(chunks) == 0

    def test_chunk_index_sequential(self):
        text = "X" * (CHUNK_SIZE * 2)
        chunks = ContextInjector._chunk_text(text, "test.py")
        indices = [c["index"] for c in chunks]
        assert indices == list(range(len(chunks)))


class TestFileExclusion:
    """Test _is_excluded method."""

    def test_excludes_git(self):
        ci = ContextInjector.__new__(ContextInjector)
        assert ci._is_excluded(Path("/project/.git/objects/abc")) is True

    def test_excludes_pycache(self):
        ci = ContextInjector.__new__(ContextInjector)
        assert ci._is_excluded(Path("/project/__pycache__/mod.cpython-312.pyc")) is True

    def test_excludes_node_modules(self):
        ci = ContextInjector.__new__(ContextInjector)
        assert ci._is_excluded(Path("/project/node_modules/pkg/index.js")) is True

    def test_excludes_venv(self):
        ci = ContextInjector.__new__(ContextInjector)
        assert ci._is_excluded(Path("/project/.venv/lib/python/site.py")) is True

    def test_allows_src(self):
        ci = ContextInjector.__new__(ContextInjector)
        assert ci._is_excluded(Path("/project/src/main.py")) is False

    def test_allows_readme(self):
        ci = ContextInjector.__new__(ContextInjector)
        assert ci._is_excluded(Path("/project/README.md")) is False


class TestFormatResults:
    """Test _format_results static method."""

    def test_format_empty(self):
        assert ContextInjector._format_results({}) == ""
        assert ContextInjector._format_results({"documents": []}) == ""

    def test_format_results(self):
        results = {
            "documents": [["doc content here"]],
            "metadatas": [[{"file": "src/main.py"}]],
        }
        formatted = ContextInjector._format_results(results)
        assert "src/main.py" in formatted
        assert "doc content here" in formatted


class TestModuleConstants:
    def test_excluded_dirs_contains_git(self):
        assert ".git" in EXCLUDED_DIRS

    def test_chunk_size_positive(self):
        assert CHUNK_SIZE > 0

    def test_chunk_overlap_less_than_size(self):
        assert CHUNK_OVERLAP < CHUNK_SIZE
