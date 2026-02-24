"""Tests for the LATTICE API Server.

Covers REST endpoints and WebSocket connection.
Uses httpx + FastAPI TestClient.
"""

from httpx import ASGITransport, AsyncClient

from kovrin.api.server import PipelineManager, RunRequest, StatusResponse, app, manager
from kovrin.core.models import ExecutionResult

# ─── Status Endpoint ─────────────────────────────────────────


class TestStatusEndpoint:
    async def test_get_status(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/status")
            assert response.status_code == 200
            data = response.json()
            assert "running_pipelines" in data
            assert "completed_pipelines" in data
            assert data["version"] == "2.0.0a1"


# ─── Traces Endpoint ─────────────────────────────────────────


class TestTracesEndpoint:
    async def test_get_traces_not_found(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/traces/nonexistent-id")
            assert response.status_code == 200
            data = response.json()
            assert "error" in data

    async def test_get_traces_with_result(self):
        # Inject a fake result
        intent_id = "test-intent-123"
        manager._results[intent_id] = ExecutionResult(
            intent_id=intent_id,
            output="Test output",
            success=True,
            traces=[],
        )

        try:
            async with AsyncClient(
                transport=ASGITransport(app=app),
                base_url="http://test",
            ) as client:
                response = await client.get(f"/api/traces/{intent_id}")
                assert response.status_code == 200
                data = response.json()
                assert data["intent_id"] == intent_id
                assert data["total"] == 0
        finally:
            manager._results.pop(intent_id, None)


# ─── Graph Endpoint ──────────────────────────────────────────


class TestGraphEndpoint:
    async def test_get_graph_not_found(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/graph/nonexistent")
            assert response.status_code == 200
            data = response.json()
            assert "error" in data

    async def test_get_graph_with_result(self):
        intent_id = "test-graph-123"
        manager._results[intent_id] = ExecutionResult(
            intent_id=intent_id,
            graph_summary={"nodes": [], "edges": []},
        )

        try:
            async with AsyncClient(
                transport=ASGITransport(app=app),
                base_url="http://test",
            ) as client:
                response = await client.get(f"/api/graph/{intent_id}")
                assert response.status_code == 200
                data = response.json()
                assert data["intent_id"] == intent_id
                assert "graph" in data
        finally:
            manager._results.pop(intent_id, None)


# ─── Result Endpoint ─────────────────────────────────────────


class TestResultEndpoint:
    async def test_get_result_not_found(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/result/nonexistent")
            assert response.status_code == 200
            data = response.json()
            assert "error" in data

    async def test_get_result_with_data(self):
        intent_id = "test-result-123"
        manager._results[intent_id] = ExecutionResult(
            intent_id=intent_id,
            output="Final output",
            success=True,
        )

        try:
            async with AsyncClient(
                transport=ASGITransport(app=app),
                base_url="http://test",
            ) as client:
                response = await client.get(f"/api/result/{intent_id}")
                assert response.status_code == 200
                data = response.json()
                assert data["intent_id"] == intent_id
                assert data["output"] == "Final output"
                assert data["success"] is True
        finally:
            manager._results.pop(intent_id, None)


# ─── PipelineManager ─────────────────────────────────────────


class TestPipelineManager:
    def test_initial_status(self):
        pm = PipelineManager()
        status = pm.status
        assert status.running_pipelines == 0
        assert status.completed_pipelines == 0

    def test_get_result_nonexistent(self):
        pm = PipelineManager()
        assert pm.get_result("nonexistent") is None

    def test_get_result_exists(self):
        pm = PipelineManager()
        result = ExecutionResult(intent_id="test", output="ok")
        pm._results["test"] = result
        assert pm.get_result("test") is result


# ─── Request/Response Models ─────────────────────────────────


class TestRequestModels:
    def test_run_request_defaults(self):
        req = RunRequest(intent="test intent")
        assert req.intent == "test intent"
        assert req.constraints == []
        assert req.context == {}

    def test_run_request_full(self):
        req = RunRequest(
            intent="analyze expenses",
            constraints=["no layoffs"],
            context={"budget": 10000},
        )
        assert len(req.constraints) == 1
        assert req.context["budget"] == 10000

    def test_status_response(self):
        sr = StatusResponse(
            running_pipelines=2,
            completed_pipelines=5,
        )
        assert sr.version == "2.0.0a1"
