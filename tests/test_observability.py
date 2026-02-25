"""Tests for Kovrin Observability (OpenTelemetry tracing + metrics)."""

from unittest.mock import MagicMock, patch

import pytest

from kovrin.observability.tracing import (
    _NoOpSpan,
    _NoOpTracer,
    get_tracer,
    init_tracing,
    shutdown,
)


class TestNoOpTracer:
    """No-op tracer/span work without opentelemetry installed."""

    def test_noop_span_context_manager(self):
        span = _NoOpSpan()
        with span as s:
            assert s is span

    def test_noop_span_set_attribute(self):
        span = _NoOpSpan()
        span.set_attribute("key", "value")  # Should not raise

    def test_noop_span_set_status(self):
        span = _NoOpSpan()
        span.set_status("ok")

    def test_noop_span_record_exception(self):
        span = _NoOpSpan()
        span.record_exception(RuntimeError("test"))

    def test_noop_span_add_event(self):
        span = _NoOpSpan()
        span.add_event("test_event", {"key": "value"})

    def test_noop_tracer_returns_noop_span(self):
        tracer = _NoOpTracer()
        span = tracer.start_as_current_span("test")
        assert isinstance(span, _NoOpSpan)


class TestInitTracing:
    def setup_method(self):
        """Reset global state before each test."""
        import kovrin.observability.tracing as mod
        mod._tracer = None
        mod._initialized = False

    def test_no_endpoint_returns_false(self):
        with patch.dict("os.environ", {}, clear=True):
            result = init_tracing(endpoint=None)
            assert result is False

    def test_with_endpoint_but_no_otel_installed(self):
        import kovrin.observability.tracing as mod
        mod._initialized = False
        mod._tracer = None

        with patch.dict("os.environ", {"OTEL_EXPORTER_OTLP_ENDPOINT": "http://localhost:4317"}):
            # Simulate ImportError for opentelemetry
            with patch.dict("sys.modules", {"opentelemetry": None}):
                import kovrin.observability.tracing as mod2
                mod2._initialized = False
                mod2._tracer = None
                result = mod2.init_tracing(endpoint="http://localhost:4317")
                assert result is False

    def test_idempotent_call(self):
        """Second call returns same result without reinitializing."""
        import kovrin.observability.tracing as mod
        mod._initialized = True
        mod._tracer = None  # No OTEL
        result = init_tracing(endpoint="http://localhost:4317")
        assert result is False  # Already initialized, tracer is None

    def test_env_var_fallback(self):
        """Reads endpoint from env var when not passed directly."""
        import kovrin.observability.tracing as mod
        mod._initialized = False
        mod._tracer = None

        # No endpoint in env, no endpoint arg
        with patch.dict("os.environ", {}, clear=True):
            result = init_tracing()
            assert result is False


class TestGetTracer:
    def setup_method(self):
        import kovrin.observability.tracing as mod
        mod._tracer = None
        mod._initialized = False

    def test_returns_noop_when_not_installed(self):
        """Without opentelemetry, returns _NoOpTracer."""
        with patch.dict("sys.modules", {"opentelemetry": None, "opentelemetry.trace": None}):
            import kovrin.observability.tracing as mod
            mod._tracer = None
            tracer = mod.get_tracer()
            assert isinstance(tracer, _NoOpTracer)

    def test_returns_set_tracer(self):
        """When _tracer is set, returns it directly."""
        import kovrin.observability.tracing as mod
        mock_tracer = MagicMock()
        mod._tracer = mock_tracer
        result = mod.get_tracer()
        assert result is mock_tracer
        mod._tracer = None


class TestShutdown:
    def test_shutdown_resets_state(self):
        import kovrin.observability.tracing as mod
        mod._initialized = True
        mod._tracer = MagicMock()
        shutdown()
        assert mod._tracer is None
        assert mod._initialized is False

    def test_shutdown_without_init(self):
        """Shutdown when never initialized — no crash."""
        import kovrin.observability.tracing as mod
        mod._initialized = False
        mod._tracer = None
        shutdown()  # Should not raise


class TestMetrics:
    """Test metric recording functions (no-op when OTEL not installed)."""

    def setup_method(self):
        import kovrin.observability.metrics as mod
        mod._initialized = False
        mod._meter = None
        mod._pipelines_total = None
        mod._tasks_total = None
        mod._task_duration = None
        mod._tool_calls_total = None

    def test_record_pipeline_noop(self):
        from kovrin.observability.metrics import record_pipeline_complete
        # Should not raise even without OTEL
        record_pipeline_complete(intent_id="test", success=True, task_count=3)

    def test_record_task_noop(self):
        from kovrin.observability.metrics import record_task_complete
        record_task_complete(task_id="t1", success=True, risk_level="LOW")

    def test_record_task_duration_noop(self):
        from kovrin.observability.metrics import record_task_duration
        record_task_duration(task_id="t1", duration_seconds=1.5, risk_level="MEDIUM")

    def test_record_tool_call_noop(self):
        from kovrin.observability.metrics import record_tool_call
        record_tool_call(tool_name="web_search", allowed=True, risk_level="LOW")

    def test_measure_task_duration_context_manager(self):
        from kovrin.observability.metrics import measure_task_duration
        with measure_task_duration("t1", "LOW"):
            pass  # Should not raise

    def test_ensure_meter_without_otel(self):
        """_ensure_meter returns False when opentelemetry not installed."""
        from kovrin.observability.metrics import _ensure_meter
        with patch.dict("sys.modules", {"opentelemetry": None, "opentelemetry.metrics": None}):
            import kovrin.observability.metrics as mod
            mod._initialized = False
            result = mod._ensure_meter()
            assert result is False

    def test_ensure_meter_idempotent(self):
        import kovrin.observability.metrics as mod
        mod._initialized = True
        mod._meter = None
        result = mod._ensure_meter()
        assert result is False  # Already init'd, no meter
