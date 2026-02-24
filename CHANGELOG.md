# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [2.0.0a1] - 2026-02-24

### Added

- **Constitutional Core (Layer 0)** — 5 immutable axioms with SHA-256 integrity verification. All-or-nothing: one axiom fails = entire task rejected.
- **Risk-Based Routing Matrix** — Deterministic `(RiskLevel x SpeculationTier) -> RoutingAction` table with 4 autonomy profiles (DEFAULT, CAUTIOUS, AGGRESSIVE, LOCKED). CRITICAL risk always routes to HUMAN_APPROVAL — hardcoded, non-overridable.
- **Merkle Audit Trail** — SHA-256 hash chain, append-only, tamper-evident. `ImmutableTraceLog` with `verify_integrity()`.
- **Critic Pipeline** — SafetyCritic (L0 compliance), FeasibilityCritic (capability matching), PolicyCritic (organizational constraints). All must PASS for task execution.
- **IntentV2 Schema** — AMR-inspired graph with speech act performatives, semantic frames, and HTN decomposition via Claude API.
- **ExecutionGraph** — DAG-based execution with topological sort, wave-based parallel execution, and dependency resolution.
- **Watchdog Agent** — Independent safety monitor with temporal rules (NoExecutionAfterRejection, ExcessiveFailureRate, UnexpectedEventSequence). Graduated containment: WARN -> PAUSE -> KILL (irreversible).
- **Delegation Capability Tokens (DCT)** — HMAC-SHA256 signed tokens with scope narrowing, cascading revocation via TokenAuthority.
- **MCTS Explorer** — Monte Carlo Tree Search with UCB1 for decomposition exploration.
- **Beam Search Executor** — Parallel beam execution with pruning.
- **Process Reward Model (PRM)** — Step-level scoring for agent drift detection.
- **Speculative Execution** — Three tiers: FREE (read-only), GUARDED (checkpoint/rollback), NONE (human approval).
- **Safety-Gated Tools** — 8 built-in tools (web_search, calculator, datetime, json_transform, code_analysis, http_request, file_read, file_write) with per-tool risk profiles, sandboxed execution, and Merkle-audited calls.
- **Multi-Model Providers** — ClaudeProvider, OpenAIProvider, OllamaProvider with ModelRouter and CircuitBreakerProvider for fault tolerance.
- **Multi-Agent Coordination** — AgentCoordinator with AgentRegistry and DCT-scoped delegation.
- **CLI** — `kovrin run`, `kovrin verify`, `kovrin audit`, `kovrin serve`, `kovrin status`.
- **FastAPI Server** — REST + WebSocket + SSE endpoints for pipeline execution, audit, and real-time events.
- **Schema Exporter** — JSON Schema + TypeScript type generation from Pydantic models (42 models, 17 enums).
- **TLA+ Formal Verification** — 8 specification modules with 10 machine-checked safety invariants.
- **741 tests** — Including 42 adversarial attack tests targeting safety bypasses.
- **CI/CD** — GitHub Actions (pytest, mypy, pip-audit) + Railway auto-deploy.
- **Brave Search Integration** — Real web search via Brave Search API (free tier).
- **Custom Exceptions** — KovrinError hierarchy with 10 specific exception types.
- **Structured Logging** — JSON + human-readable output via `kovrin.logging`.

### Fixed

- FeasibilityCritic false rejections — improved prompt with detailed tool capabilities and explicit evaluation rules. Verified: 4/4 tasks PASS in production.

[2.0.0a1]: https://github.com/nkovalcin/kovrin/releases/tag/v2.0.0a1
