"""OpenTelemetry tracing setup for Kovrin.

Initializes OTLP exporter when OTEL_EXPORTER_OTLP_ENDPOINT is set.
Without endpoint, returns a no-op tracer that adds zero overhead.
"""

from __future__ import annotations

import os
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from opentelemetry.trace import Tracer

_tracer: Tracer | None = None
_initialized = False


def init_tracing(
    endpoint: str | None = None,
    service_name: str | None = None,
) -> bool:
    """Initialize OpenTelemetry tracing.

    Args:
        endpoint: OTLP endpoint URL. Falls back to OTEL_EXPORTER_OTLP_ENDPOINT env var.
        service_name: Service name for traces. Falls back to OTEL_SERVICE_NAME env var.

    Returns:
        True if tracing was initialized, False if skipped (no endpoint or missing deps).
    """
    global _tracer, _initialized

    if _initialized:
        return _tracer is not None

    _initialized = True

    endpoint = endpoint or os.environ.get("OTEL_EXPORTER_OTLP_ENDPOINT")
    if not endpoint:
        return False

    service_name = service_name or os.environ.get("OTEL_SERVICE_NAME", "kovrin-api")

    try:
        from opentelemetry import trace
        from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
        from opentelemetry.sdk.resources import Resource
        from opentelemetry.sdk.trace import TracerProvider
        from opentelemetry.sdk.trace.export import BatchSpanProcessor

        resource = Resource.create({"service.name": service_name})
        provider = TracerProvider(resource=resource)
        exporter = OTLPSpanExporter(endpoint=endpoint)
        provider.add_span_processor(BatchSpanProcessor(exporter))
        trace.set_tracer_provider(provider)

        _tracer = trace.get_tracer("kovrin", "2.0.0a1")
        return True
    except ImportError:
        return False


def get_tracer() -> Tracer:
    """Get the Kovrin tracer.

    Returns a real tracer if initialized, or a no-op tracer from the OTel API
    (or a stub if opentelemetry is not installed).
    """
    global _tracer

    if _tracer is not None:
        return _tracer

    try:
        from opentelemetry import trace

        return trace.get_tracer("kovrin", "2.0.0a1")
    except ImportError:
        return _NoOpTracer()


def shutdown() -> None:
    """Flush and shut down the tracer provider."""
    global _tracer, _initialized
    try:
        from opentelemetry import trace

        provider = trace.get_tracer_provider()
        if hasattr(provider, "shutdown"):
            provider.shutdown()
    except (ImportError, Exception):
        pass
    _tracer = None
    _initialized = False


class _NoOpSpan:
    """Minimal no-op span for when opentelemetry is not installed."""

    def __enter__(self):
        return self

    def __exit__(self, *args):
        pass

    def set_attribute(self, key: str, value: object) -> None:
        pass

    def set_status(self, status: object) -> None:
        pass

    def record_exception(self, exception: BaseException) -> None:
        pass

    def add_event(self, name: str, attributes: dict | None = None) -> None:
        pass


class _NoOpTracer:
    """Minimal no-op tracer for when opentelemetry is not installed."""

    def start_as_current_span(self, name: str, **kwargs):
        return _NoOpSpan()
