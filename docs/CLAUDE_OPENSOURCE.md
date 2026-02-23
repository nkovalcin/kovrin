# CLAUDE.md — Instructions for Claude Code

## Project Identity

**Name**: KOVRIN
**Type**: AI agent safety framework (Python, open-source, MIT)
**Author**: Norbert Kovalčín / DIGITAL SPECIALISTS s.r.o.
**Domains**: kovrin.ai (marketing), app.kovrin.ai (SaaS), docs.kovrin.dev (docs)

## Project Structure

```
kovrin/
├── src/kovrin/              # Core framework (37 Python files)
│   ├── __init__.py          # Public API: Kovrin, AutonomyProfile, etc.
│   ├── engine.py            # Main orchestrator — Kovrin class, engine.run()
│   ├── intent/
│   │   ├── parser.py        # IntentParser → Claude API → list[SubTask]
│   │   ├── v2.py            # IntentV2 (AMR graph, speech act, semantic frame)
│   │   └── mcts.py          # MCTSExplorer (optional, UCB1 tree search)
│   ├── critics/
│   │   ├── pipeline.py      # CriticPipeline — runs all critics per subtask
│   │   ├── safety.py        # SafetyCritic → ConstitutionalCore
│   │   ├── feasibility.py   # FeasibilityCritic → Claude API
│   │   └── policy.py        # PolicyCritic → Claude API
│   ├── constitution/
│   │   └── core.py          # ConstitutionalCore — 5 axioms, SHA-256 integrity
│   ├── execution/
│   │   ├── graph.py         # ExecutionGraph — DAG, topological sort, waves
│   │   ├── executor.py      # GraphExecutor — semaphore, concurrent execution
│   │   ├── task.py          # TaskExecutor — per-task execution with risk routing
│   │   └── beam.py          # BeamSearchExecutor (optional)
│   ├── risk/
│   │   ├── router.py        # RiskRouter — 4×3 matrix + profile overrides
│   │   └── profiles.py      # AutonomyProfile: FREE, GUARDED, NONE
│   ├── agents/
│   │   ├── coordinator.py   # AgentCoordinator — multi-agent orchestration
│   │   ├── registry.py      # AgentRegistry — agent management
│   │   ├── agent.py         # Agent class — role-specific execution
│   │   └── tokens.py        # TokenAuthority — DCT (Delegation Capability Tokens)
│   ├── audit/
│   │   ├── trace.py         # ImmutableTraceLog, HashedTrace (Merkle chain)
│   │   └── export.py        # Audit trail export (JSON, compliance formats)
│   ├── watchdog/
│   │   └── agent.py         # WatchdogAgent — independent safety monitor
│   ├── prm/
│   │   └── model.py         # ProcessRewardModel — step-level scoring
│   └── models/
│       └── *.py             # Pydantic models (29 models, 13 enums)
├── tests/                   # pytest test suite
├── docs/                    # Documentation source (Fumadocs or similar)
├── examples/                # Usage examples
├── tla/                     # TLA+ specifications
├── pyproject.toml           # Package configuration
├── README.md                # Project README
├── CLAUDE.md                # This file
├── CONTRIBUTING.md          # Contribution guidelines
├── LICENSE                  # MIT License
└── .github/
    └── workflows/
        └── ci.yml           # GitHub Actions: pytest + mypy + ruff
```

## Coding Conventions

### Python Style

- **Python version**: 3.11+ (use modern syntax: `match`, `|` union types, etc.)
- **Formatter**: `ruff format` (line length 100)
- **Linter**: `ruff check` (strict mode)
- **Type checking**: `mypy --strict` on all public API
- **Type hints**: Required on ALL public functions and methods. Internal helpers can use inference.
- **Imports**: Use absolute imports from `kovrin.*`. No relative imports except within same package.
- **Docstrings**: Google style. Required on all public classes and methods.

```python
# Good
from kovrin.risk.router import RiskRouter
from kovrin.models.task import SubTask

# Bad
from .router import RiskRouter
from ..models.task import SubTask
```

### Naming

- Classes: `PascalCase` — `RiskRouter`, `TaskExecutor`, `ConstitutionalCore`
- Functions/methods: `snake_case` — `route_task`, `verify_integrity`
- Constants: `UPPER_SNAKE` — `DEFAULT_TIMEOUT`, `MAX_CONCURRENT`
- Enums: `PascalCase` class, `UPPER_SNAKE` values — `RiskLevel.HIGH`
- Private: Single underscore prefix — `_compute_hash`, `_validate_token`
- Files: `snake_case.py` — `risk_router.py`, `trace_log.py`

### Pydantic Models

- All data structures are Pydantic v2 `BaseModel`
- Use `model_validator` for complex validation, not `__init__` overrides
- Immutable where possible: `model_config = ConfigDict(frozen=True)`
- All models in `src/kovrin/models/` unless tightly coupled to a single module

```python
from pydantic import BaseModel, ConfigDict

class SubTask(BaseModel):
    model_config = ConfigDict(frozen=True)
    
    id: str
    description: str
    risk_level: RiskLevel
    dependencies: list[str] = []
```

### Async

- Core engine is async (`asyncio`)
- Use `asyncio.Semaphore` for concurrency control (default: 5)
- All Claude API calls are async
- Public API provides sync wrapper: `engine.run()` calls `asyncio.run(engine.arun())`

### Error Handling

- Custom exceptions in `src/kovrin/exceptions.py`
- Never catch bare `Exception` — always specific
- Constitutional violations raise `ConstitutionalViolationError` (non-recoverable)
- Scope violations raise `ScopeViolationError`
- API errors raise `KovrinAPIError` with retry info

### Testing

- Framework: `pytest` + `pytest-asyncio`
- Minimum coverage: 80% on public API
- Mock Claude API calls in tests (never hit real API in CI)
- Test files mirror source structure: `tests/test_risk/test_router.py`
- Use fixtures for common setup (engine instances, mock responses)

## Architecture Rules (CRITICAL)

### Safety Invariants — NEVER VIOLATE

1. **Constitutional Core is immutable at runtime.** Once loaded, the 5 axioms cannot be modified. SHA-256 integrity check on every critic pipeline run.

2. **CRITICAL risk level ALWAYS requires HUMAN_APPROVAL.** No override, no profile, no configuration can change this. This is the hardcoded safety floor.

3. **Merkle chain is append-only.** `ImmutableTraceLog` never deletes, never modifies. `verify_integrity()` recomputes entire chain.

4. **Scope can only narrow, never widen.** DCT tokens issued to child agents must have equal or narrower scope than parent. `ScopeViolationError` if attempted.

5. **Watchdog containment is irreversible.** KILL cannot be downgraded to PAUSE or WARN. PAUSE cannot be downgraded to WARN.

6. **Rejected tasks never execute.** If critic pipeline returns REJECT, the task MUST NOT reach TaskExecutor. Watchdog monitors this as `NoExecutionAfterRejection`.

### Component Boundaries

- `ConstitutionalCore` has ZERO external dependencies. No API calls, no I/O. Pure computation + SHA-256.
- `RiskRouter` is pure data (matrix + overrides). No side effects. No API calls.
- `ImmutableTraceLog` is write-only from engine's perspective. Read-only for Watchdog.
- `WatchdogAgent` is read-only observer. It can trigger WARN/PAUSE/KILL but never modifies tasks or results.
- `TokenAuthority` is the ONLY component that issues/validates/revokes DCT tokens.

### Claude API Usage

- Model: `claude-sonnet-4-20250514` (default, configurable)
- API key from environment: `ANTHROPIC_API_KEY` or constructor parameter
- Never log API keys. Never include in traces.
- Retry: 3 attempts with exponential backoff (1s, 2s, 4s)
- Timeout: 30s per call (configurable)
- Token budget tracking per run (for cost estimation)

## Git Conventions

- **Branch naming**: `feat/risk-router-override`, `fix/merkle-chain-verify`, `docs/quickstart`
- **Commit format**: Conventional Commits — `feat:`, `fix:`, `docs:`, `test:`, `refactor:`, `chore:`
- **PR size**: Max 400 lines changed (excluding tests). Split larger changes.
- **Never commit**: API keys, `.env` files, `__pycache__`, `.pyc`, `kovrin.db`

## What to Build vs. What Exists

### Exists (functional, needs cleanup for open-source):
- Core engine pipeline (intent → critics → execution → output)
- IntentV2 with AMR-inspired parsing
- Critic pipeline (3 critics, parallel)
- ConstitutionalCore (5 axioms, SHA-256)
- RiskRouter (4×3 matrix, profile overrides)
- ExecutionGraph (DAG, topological sort, waves)
- GraphExecutor (semaphore, concurrent)
- TaskExecutor (risk routing per task)
- MCTSExplorer (optional, UCB1)
- BeamSearchExecutor (optional)
- AgentCoordinator + TokenAuthority (DCT)
- WatchdogAgent (kill/pause/warn)
- ImmutableTraceLog (Merkle hash chain)
- ProcessRewardModel (optional, step scoring)

### Needs building:
- Clean public API (`__init__.py` exports)
- `pyproject.toml` with proper metadata
- Comprehensive test suite (currently minimal)
- Documentation site (docs.kovrin.dev)
- CLI (`kovrin run`, `kovrin verify`, `kovrin audit`)
- Marketing website (kovrin.ai)
- SaaS dashboard (app.kovrin.ai) — Phase 2
- OpenTelemetry export for traces
- LangGraph integration wrapper (`kovrin.integrations.langgraph`)
- GitHub Actions CI pipeline
- PyPI package publishing

## Design System Reference (for web/dashboard work)

- **Border radius**: 0px everywhere
- **Primary color**: #10B981 (Emerald — safety green)
- **Background**: #0A0A0B (near black)
- **Surface**: #111113
- **Border**: #27272A
- **Font (code/UI)**: JetBrains Mono
- **Font (display)**: Instrument Sans
- **Font (body)**: DM Sans
- **Framework**: Next.js 15 + Tailwind CSS v4 + shadcn/ui (0 radius)
- **Icons**: Lucide React

See `design-spec.jsx` for complete design system documentation.

## Priority Order

When working on KOVRIN, prioritize in this order:

1. **Safety correctness** — Never break the 6 invariants above
2. **Public API clarity** — Clean, minimal, well-typed surface
3. **Test coverage** — Every public method has tests
4. **Documentation** — Docstrings + docs site
5. **Performance** — Optimize after correctness
6. **Features** — New capabilities after core is solid
