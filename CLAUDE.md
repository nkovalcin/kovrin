<!--
╔══════════════════════════════════════════════════════════════════════════════╗
║                         KOVRIN — CLAUDE.md                                   ║
║           Inštrukcie pre Claude Code (AI coding assistant)                   ║
║                                                                              ║
║  Tento súbor je primárny zdroj pravdy pre každého AI asistenta pracujúceho   ║
║  na tomto projekte. Prečítaj ho celý pred akoukoľvek akciou.                 ║
╚══════════════════════════════════════════════════════════════════════════════╝
-->

# KOVRIN — Safety-First Intent-Based AI Orchestration Framework

> **Formerly "LATTICE"** — Language for Autonomous Thinking, Transformation, and Intelligent Coordination at Emergent Scale. Premenovaný na **Kovrin** vo februári 2026.

**Verzia frameworku:** `2.0.0a1`
**Python:** `3.12+`
**Stav:** Alpha — core + tools + providers + CLI + dashboard LIVE, **production-verified na Railway**
**Licencia:** MIT
**Deployment:** Railway (auto-deploy z `main`) — kovrin-api (FastAPI) + kovrin-web (Next.js, 3 služby)
**Posledný verified test:** 2026-02-26 — 978 tests PASS, full stack LIVE (dashboard CONNECTED, API healthy, WS active)
**CLAUDE.md stratégia:** Tento súbor je **jediný globálny CLAUDE.md** pre oba repozitáre (kovrin + kovrin-web). V kovrin-web/ je len pointer sem.

---

## Autor & Komunikácia

| | |
|---|---|
| **Autor** | Norbert Kovalčín — AI Engineer & Digital Solutions Architect |
| **Firma** | DIGITAL SPECIALISTS s.r.o. (Česká republika / Prešov, SR) |
| **Web** | [nkovalcin.com](https://nkovalcin.com) |
| **Email** | norbert@nkovalcin.com |
| **Jazyk komunikácie** | 🇸🇰 Slovenčina (chat) / 🇬🇧 Angličtina (kód, komentáre, testy, docs) |

---

## Čo je Kovrin

Framework kde bezpečnosť AI agentov nie je runtime filter, ale **architektonická garancia**. Whitepaper syntetizuje výskum z 9 domén (grafová výpočtová paradigma, formálna verifikácia, HTN plánovanie, AI alignment, filozofia jazyka, paralelná explorácia, immutable audit, UX, competitive analysis) do jednej implementácie.

**Centrálna téza**: Žiadny produkčný framework netreatuje bezpečnosť ako architektonickú garanciu. Kovrin túto medzeru zapĺňa.

### Kľúčové čísla

| Metrika | Hodnota |
|---------|---------|
| Fázy whitepaperu | 6/6 implementovaných (Phase 7 neexistuje) |
| Testy | **978** (z toho 42 adversarial, 84 E2E, 60 test súborov) |
| TLA+ špecifikácie | **8 modulov**, 10 safety invariantov |
| Pydantic modely | **53 modelov, 22 enumov** (29/13 v core, zvyšok v tools/providers/intent/superwork/observability) |
| Dashboard komponenty | **16** (11 kovrin + 5 superwork, React/TypeScript) |
| LLM Providers | **3** (Claude, OpenAI, Ollama) |
| Built-in Tools | **8** (safety-gated, Merkle-audited) |
| Virtual env | `.venv/bin/python` |

---

## Projektová štruktúra

```
kovrin/
├── src/kovrin/              # Core framework
│   ├── __init__.py          # Hlavné API: Kovrin, AutonomyProfile, ...
│   ├── core/
│   │   ├── constitutional.py  # Layer 0 — 5 axiómov, SHA-256 integrity
│   │   └── models.py          # 29 Pydantic modelov, 13 enumov (core only)
│   ├── intent/
│   │   ├── schema.py          # IntentV2, Performative, SemanticFrame
│   │   └── parser.py          # HTN decomposition cez Claude API
│   ├── engine/
│   │   ├── graph.py           # ExecutionGraph, GraphExecutor (DAG)
│   │   ├── risk_router.py     # RiskRouter, _MATRIX, safety guard
│   │   ├── executor.py        # TaskExecutor
│   │   ├── mcts.py            # MCTSExplorer, UCB1
│   │   ├── beam_search.py     # BeamSearchExecutor
│   │   ├── speculation.py     # SpeculativeContext (FREE/GUARDED/NONE)
│   │   ├── confidence.py      # ConfidenceEstimator
│   │   ├── prm.py             # ProcessRewardModel (step-level scoring)
│   │   ├── tokens.py          # TokenAuthority, DCT
│   │   ├── topology.py        # TopologyAnalyzer
│   │   └── pricing.py         # MODEL_PRICING, calculate_cost, detect_provider
│   ├── safety/
│   │   ├── critics.py         # SafetyCritic, FeasibilityCritic, PolicyCritic
│   │   └── watchdog.py        # WatchdogAgent, temporal rules, drift detection
│   ├── audit/
│   │   └── trace_logger.py    # ImmutableTraceLog (Merkle hash chain)
│   ├── agents/
│   │   ├── base.py            # BaseAgent
│   │   ├── coordinator.py     # AgentCoordinator
│   │   └── registry.py        # AgentRegistry
│   ├── tools/                 # Safety-gated tool execution (Phase 1)
│   │   ├── models.py          # ToolRiskProfile, ToolCallRequest, ToolCallDecision
│   │   ├── registry.py        # ToolRegistry — central tool registration
│   │   ├── router.py          # SafeToolRouter — safety pipeline for tool calls
│   │   ├── sandbox.py         # SandboxedExecutor — isolated execution
│   │   └── builtin/           # 8 built-in tools (calc, datetime, json, code, web, http, file r/w)
│   ├── providers/             # Multi-model abstraction (Phase 2)
│   │   ├── base.py            # LLMProvider ABC, LLMResponse, ContentBlock
│   │   ├── claude.py          # ClaudeProvider (Anthropic SDK wrapper)
│   │   ├── openai.py          # OpenAIProvider (GPT-4o, o1, compatible APIs)
│   │   ├── ollama.py          # OllamaProvider (local models)
│   │   ├── router.py          # ModelRouter — task-based model selection
│   │   └── circuit_breaker.py # CircuitBreakerProvider — fault tolerance
│   ├── observability/          # OpenTelemetry instrumentation
│   │   ├── tracing.py          # get_tracer(), _NoOpTracer, OTEL setup
│   │   └── metrics.py          # Prometheus-style metrics
│   ├── api/
│   │   ├── server.py           # FastAPI — REST + WebSocket
│   │   └── superwork_router.py # SuperWork API endpoints + WebSocket feed
│   ├── schema/
│   │   ├── exporter.py        # SchemaExporter (JSON Schema + TypeScript)
│   │   └── __main__.py        # CLI: python -m kovrin.schema
│   ├── storage/
│   │   └── repository.py      # SQLite persistence
│   ├── superwork/              # SuperWork supervisor platform
│   │   ├── models.py           # SuperWork Pydantic models
│   │   ├── repository.py       # SuperWork SQLite persistence
│   │   ├── session_watcher.py  # Watches ~/.claude/projects/, detects task completion
│   │   ├── context_injector.py # ChromaDB + RAG, surgical context per task
│   │   ├── orchestrator.py     # Opus — analyzes state, proposes next steps
│   │   ├── metrics.py          # Velocity, cost, completion prediction
│   │   └── cli.py              # `kovrin superwork --project <path>`
│   ├── exceptions.py          # KovrinError hierarchy (10 exception types)
│   ├── logging.py             # Structured logging (JSON + human-readable)
│   ├── cli.py                 # CLI: kovrin run, verify, audit, serve, status, shell
│   └── examples/
│       └── company_ops.py     # Demo
├── specs/                   # TLA+ formálna verifikácia (8 modulov)
│   ├── TaskStateMachine.tla
│   ├── AxiomValidation.tla
│   ├── RoutingMatrix.tla
│   ├── GraphExecution.tla
│   ├── WatchdogMonitor.tla
│   ├── SpeculationModel.tla
│   ├── HashChain.tla
│   ├── KovrinSafety.tla       # Top-level kompozícia (10 invariantov)
│   └── README.md              # TLC konfigurácia, bounds
├── tests/                   # 978 testov (60 súborov)
│   ├── test_adversarial.py        # 30 adversarial (P0 + P1)
│   ├── test_adversarial_tokens.py # 11 adversarial (P2)
│   ├── test_adversarial_tools.py  # 13 adversarial (tool safety)
│   ├── test_api_e2e.py            # 19 E2E (API endpoints)
│   ├── test_audit_e2e.py          # 15 E2E (Merkle audit)
│   ├── test_pipeline_e2e.py       # 16 E2E (full pipeline)
│   ├── test_safety_e2e.py         # 18 E2E (safety integration)
│   ├── test_tools_e2e.py          # 16 E2E (tool execution)
│   ├── test_pricing.py            # 20 testov (model pricing)
│   ├── test_critics.py            # 15 testov (critic pipeline)
│   ├── test_cli.py                # 20 testov (CLI commands)
│   ├── test_providers.py          # Provider abstraction tests
│   ├── test_schema_exporter.py    # 24 testov
│   └── test_*.py                  # Unit + integration (60 files total)
├── docs/
│   ├── Kovrin_Whitepaper_v2.docx
│   ├── ARCHITECTURE.md
│   ├── README_OPENSOURCE.md       # Public-facing README pre launch
│   ├── SUPERWORK.md               # SuperWork supervisor platform spec
│   ├── KOVRIN_Phase1_Plan.docx
│   ├── kovrin-design-spec.jsx     # Design system, wireframy, sitemap
│   └── prototypes/                # Early standalone skripty
├── kovrin.db                # SQLite databáza (lokálna, neinkomitovať)
├── pyproject.toml
├── .env.example
├── CLAUDE.md                # Tento súbor
└── README.md
```

---

## Architektonické rozhodnutia

### Layer 0 — Constitutional Core (`src/kovrin/core/constitutional.py`)

5 nemeniteľných axiómov validovaných **pred každou akciou**:

| Axiom | Garancia |
|-------|----------|
| Human Agency | Žiadna akcia neodstráni schopnosť ľudského override |
| Harm Floor | Očakávaná škoda nikdy neprekročí threshold |
| Transparency | Všetky rozhodnutia sledovateľné k intenciu |
| Reversibility | Preferovať reverzibilné pred irereverzibilným |
| Scope Limit | Nikdy nepresiahni autorizovanú hranicu |

- SHA-256 integrity hash — axiomy nemožno modifikovať za behu
- **All-or-nothing**: ak 1 axiom zlyhá, celý task zamietnutý. Žiadne výnimky.
- Zero externé závislosti — pure computation

### Risk Routing Matrix (`src/kovrin/engine/risk_router.py`)

Deterministická tabuľka: `(RiskLevel × SpeculationTier) → RoutingAction`

- **CRITICAL safety guard (riadky 98–99)**: CRITICAL vždy → HUMAN_APPROVAL, hardcoded, žiadny profil ani override to neprepíše
- 4 profily: `DEFAULT`, `CAUTIOUS`, `AGGRESSIVE`, `LOCKED`
- Cell-level overrides cez `AutonomySettings.override_matrix`

### Speculative Execution (`src/kovrin/engine/speculation.py`)

| Tier | Správanie |
|------|-----------|
| `FREE` | Read-only, auto-execute |
| `GUARDED` | Checkpoint → execute → commit/rollback |
| `NONE` | Irereverzibilné → human approval |

### Merkle Audit Trail (`src/kovrin/audit/trace_logger.py`)

- SHA-256 hash chain, append-only, tamper-evident
- `verify_integrity()` detekuje akúkoľvek modifikáciu
- Subscribers cez `subscribe(callback)` pre watchdog integráciu

### Watchdog (`src/kovrin/safety/watchdog.py`)

- Temporal rules: `NoExecutionAfterRejection`, `ExcessiveFailureRate`, `UnexpectedEventSequence`
- Graduated containment: `WARN → PAUSE → KILL` (KILL je irereverzibilný)
- `AgentDriftTracker` — threshold-based drift classification na PRM scores a success rate, `CrossAgentConsistency` keyword-based sentiment heuristic

### DCT — Delegation Capability Tokens (`src/kovrin/engine/tokens.py`)

- HMAC-SHA256 podpísané
- Scope narrowing: child nikdy nemôže mať širšie oprávnenia než parent
- Cascading revocation cez `TokenAuthority`

### LLM-Modulo Critics (`src/kovrin/safety/critics.py`)

- `SafetyCritic` → L0 compliance
- `FeasibilityCritic` → capability matching
- `PolicyCritic` → organizačné constraints
- `CriticPipeline` ich orchestruje

### Intent Schema (`src/kovrin/intent/schema.py`)

- `IntentV2` — AMR-inspired graf, speech act performatives, semantic frames
- 6 filozofických/lingvistických tradícií (Wittgenstein, Fodor, AMR, Austin/Searle, Fillmore, Iverson)
- `max_decomposition_depth`: ge=1, le=20

---

## Safety Invarianty — NIKDY NEPORUŠIŤ

> Claude Code musí tieto invarianty vždy rešpektovať pri akomkoľvek refactoringu alebo pridávaní kódu.

1. **Constitutional Core je immutable za behu.** SHA-256 integrity check pri každom spustení critic pipeline.
2. **CRITICAL risk level VŽDY → HUMAN_APPROVAL.** Žiadny override, žiadny profil, žiadna konfigurácia to nezmení. Hardcoded safety floor.
3. **Merkle chain je append-only.** `ImmutableTraceLog` nikdy nemaže, nikdy nemodifikuje.
4. **Scope sa môže len zužovať, nikdy rozširovať.** DCT child tokeny musia mať rovnaký alebo užší scope ako parent.
5. **Watchdog containment je irereverzibilný.** KILL → nie je downgrade. PAUSE → nie je downgrade.
6. **Zamietnuté tasky nikdy nespúšťaj.** Ak critic pipeline vráti REJECT, task NESMIE dosiahnuť TaskExecutor.

---

## Component Boundaries

| Komponent | Pravidlo |
|-----------|---------|
| `ConstitutionalCore` | Axiom definície, integrity hash a statické metódy sú zero-dependency pure computation. `check()` deleguje na Claude API pre sémantickú axiom evaluáciu. |
| `RiskRouter` | Pure data matrix + overrides pre `route()`. `request_human_approval()` vykonáva I/O. |
| `ImmutableTraceLog` | Write-only z pohľadu engine. Read-only pre Watchdog. |
| `WatchdogAgent` | Read-only observer. Môže triggernúť WARN/PAUSE/KILL, ale nikdy nemodifikuje tasky. |
| `TokenAuthority` | Jediný komponent vydávajúci/validujúci/revokujúci DCT tokeny. |

---

## Coding Conventions

### Python

- **Python 3.12+** — používaj moderný syntax: `match`, `|` union types, `TypeAlias`
- **Formatter**: `ruff format` (line length 100)
- **Linter**: `ruff check` (strict)
- **Type checking**: `mypy --strict` na všetkom public API
- **Type hints**: Povinné na VŠETKÝCH public funkciách. Interné helpery môžu inference.
- **Importy**: Absolútne `from kovrin.xxx import ...`. Žiadne relatívne importy mimo rovnaký balíček.
- **Docstrings**: Google style. Povinné na všetkých public triedach a metódach.
- **Enums**: `PascalCase` trieda, `UPPER_SNAKE` hodnoty — `RiskLevel.HIGH`
- **Private**: Single underscore prefix — `_compute_hash`, `_validate_token`

### Async

- Core engine je async (`asyncio`)
- `asyncio.Semaphore` pre concurrency control (default: 5)
- Všetky Claude API volania sú async
- Public API poskytuje sync wrapper: `engine.run()` → `asyncio.run(engine.arun())`

### Pydantic Models

```python
from pydantic import BaseModel, ConfigDict

class SubTask(BaseModel):
    model_config = ConfigDict(frozen=True)
    
    id: str
    description: str
    risk_level: RiskLevel
    dependencies: list[str] = []
```

- Všetky modely v `src/kovrin/core/models.py` (alebo tightly coupled vedľa modulu)
- `model_validator` pre komplexnú validáciu, nie `__init__` override
- Immutable kde možné: `frozen=True`

### Claude API

- Model: `claude-sonnet-4-20250514` (default, konfigurovateľné)
- API key: `ANTHROPIC_API_KEY` env alebo constructor parameter
- **Nikdy neloguj API kľúče. Nikdy ich nevkladaj do traces.**
- Retry: 3 pokusy s exponential backoff (1s, 2s, 4s)
- Timeout: 30s per call (konfigurovateľné)
- Token budget tracking per run (pre cost estimation)

### Error Handling

- Custom exceptions v `src/kovrin/exceptions.py`
- Nikdy `except Exception:` — vždy špecifické
- Constitutional violations → `ConstitutionalViolationError` (non-recoverable)
- Scope violations → `ScopeViolationError`
- API errors → `KovrinAPIError` s retry info

---

## Príkazy

```bash
# ── Základné nastavenie ──────────────────────────────────────────────────────
source .venv/bin/activate            # Aktivuj venv
# alebo použiť priamo:
.venv/bin/python -m ...

# ── Testy ────────────────────────────────────────────────────────────────────
.venv/bin/python -m pytest tests/ -v --ignore=tests/test_api.py --ignore=tests/test_superwork_api.py  # Všetky (978)
.venv/bin/python -m pytest tests/ -m adversarial -v              # Adversarial (42)
.venv/bin/python -m pytest tests/test_schema_exporter.py -v      # Schema (24)
.venv/bin/python -m pytest tests/ -m "not integration" -v        # Bez API calls

# ── CLI ───────────────────────────────────────────────────────────────────────
.venv/bin/python -m kovrin.cli run "Search for Python 3.13 features" --tools
.venv/bin/python -m kovrin.cli shell                              # Interactive REPL (continuous)
.venv/bin/python -m kovrin.cli verify                             # Merkle chain integrity
.venv/bin/python -m kovrin.cli audit                              # List pipelines
.venv/bin/python -m kovrin.cli audit <intent_id>                  # View audit trail
.venv/bin/python -m kovrin.cli serve --port 8000                  # Start API server
.venv/bin/python -m kovrin.cli status                             # Show framework status

# ── Schema export ─────────────────────────────────────────────────────────────
.venv/bin/python -m kovrin.schema.exporter --list
.venv/bin/python -m kovrin.schema.exporter --json-schema schemas/
.venv/bin/python -m kovrin.schema.exporter --typescript dashboard/src/types/generated.ts
.venv/bin/python -m kovrin.schema.exporter --validate dashboard/src/types/kovrin.ts

# ── Server ────────────────────────────────────────────────────────────────────
.venv/bin/python -m uvicorn kovrin.api.server:app --reload

# ── Example ───────────────────────────────────────────────────────────────────
.venv/bin/python -m kovrin.examples.company_ops

# ── TLA+ verifikácia (manuálne, vyžaduje TLC) ─────────────────────────────────
# Pozri specs/README.md pre TLC konfiguráciu a bounds
```

---

## Architektúra repozitárov a domén

### Dva separátne repozitáre

| Repo | Cesta | Framework | Účel |
|------|-------|-----------|------|
| **kovrin** | `~/Desktop/projects/kovrin/` | Python 3.12 + FastAPI | Backend API + core framework |
| **kovrin-web** | `~/Desktop/projects/kovrin-web/` | Next.js 16 + React 19 + Tailwind v4 | Marketing landing page + app dashboard |

> **DÔLEŽITÉ:** `dashboard/` v kovrin repo je STARÝ Vite+React prototyp. Produkčný frontend je `kovrin-web/`.

### Schéma domén — 3-service architektúra

Každá doména je **samostatná Railway služba** (rovnaký kovrin-web repo, rôzny `SITE_MODE`):

| Doména | Čo servuje | Railway služba | SITE_MODE |
|--------|-----------|----------------|-----------|
| **kovrin.dev** | Marketing landing page (hero, features, pricing, waitlist, blog) | kovrin-marketing | `marketing` |
| **app.kovrin.dev** | App dashboard (SuperWork, pipeline, audit, approvals, settings) | kovrin-dashboard | `dashboard` |
| **docs.kovrin.dev** | Dokumentácia (getting-started, architecture, api-reference) | kovrin-docs | `docs` |
| **api.kovrin.dev** | FastAPI backend (REST + WebSocket) | kovrin-api | — |

> **Routing**: Next.js middleware v `src/middleware.ts` kontroluje `SITE_MODE` env var a restricuje routes podľa domény. Cross-domain linky používajú `src/lib/domains.ts` helper.

### Sitemap (podľa design spec)

**kovrin.dev (marketing):**
- `/` — Homepage (hero + terminal demo + how it works + code example + social proof + CTA)
- `/features` — 6 safety features, architecture diagram, comparison table
- `/pricing` — Open Source ($0) / Pro ($79/mo) / Enterprise (custom)
- `/blog` — Technical blog, case studies
- `/about` — Story, mission
- `/security` — Security practices, disclosure
- `/changelog` — Version history

**app.kovrin.dev (dashboard):**
- `/overview` — Agent overview, risk scores, real-time events (root `/` redirects here)
- `/pipeline` — Pipeline management
- `/pipeline/[id]` — Pipeline detail (cost, model, tokens, duration stats)
- `/approvals` — Human-in-the-loop approval queue
- `/audit` — Merkle-verified audit log
- `/compliance` — Compliance report, safety scores
- `/costs` — Cost tracking, token usage analytics
- `/settings` — Autonomy profiles, risk routing matrix, system status
- `/superwork` — SuperWork dashboard (session control + metrics)
- `/superwork/proposals` — Task proposals from Orchestrator
- `/superwork/feed` — Live event feed (WebSocket)

---

## Deployment — Railway (Production)

### Služby (4 Railway services)
| Služba | Repo | Builder | Custom domain | SITE_MODE |
|--------|------|---------|---------------|-----------|
| **kovrin-api** | `kovrin` | Dockerfile (Python 3.12-slim + uvicorn) | `api.kovrin.dev` | — |
| **kovrin-marketing** | `kovrin-web` | Nixpacks (Node 20 + Next.js) | `kovrin.dev` | `marketing` |
| **kovrin-dashboard** | `kovrin-web` | Nixpacks (Node 20 + Next.js) | `app.kovrin.dev` | `dashboard` |
| **kovrin-docs** | `kovrin-web` | Nixpacks (Node 20 + Next.js) | `docs.kovrin.dev` | `docs` |

### Environment Variables — kovrin-api (Railway)
| Key | Popis |
|-----|-------|
| `ANTHROPIC_API_KEY` | Claude API — pre intent parsing, critic pipeline, task execution |
| `BRAVE_SEARCH_API_KEY` | Brave Search API — pre `web_search` tool (free tier 2000 req/month) |

### Environment Variables — kovrin-web (Railway, per service)
| Key | Služba | Povinné | Popis |
|-----|--------|---------|-------|
| `SITE_MODE` | všetky 3 | 🔴 ÁNO | `marketing` / `dashboard` / `docs` — určuje ktoré routes sa servujú |
| `DATABASE_URL` | marketing | 🟡 Voliteľné | PostgreSQL pre waitlist. Bez nej graceful degradation. |
| `KOVRIN_API_INTERNAL_URL` | dashboard | 🔴 ÁNO | URL kovrin-api. Produkcia: `https://api.kovrin.dev`. (Internal `.railway.internal` nefunguje spoľahlivo — porty.) |
| `NEXT_PUBLIC_KOVRIN_WS_URL` | dashboard | 🟡 Build-time | Verejná WS URL: `wss://api.kovrin.dev`. Bez nej WebSocket disabled. |
| `NEXT_PUBLIC_MARKETING_URL` | všetky 3 | 🟡 | Default: `https://kovrin.dev` |
| `NEXT_PUBLIC_DASHBOARD_URL` | všetky 3 | 🟡 | Default: `https://app.kovrin.dev` |
| `NEXT_PUBLIC_DOCS_URL` | všetky 3 | 🟡 | Default: `https://docs.kovrin.dev` |

### kovrin-web — Kľúčové súbory
```
kovrin-web/
├── src/
│   ├── middleware.ts              # SITE_MODE routing (marketing/dashboard/docs)
│   ├── lib/
│   │   ├── domains.ts            # Cross-domain URL helpers (docsUrl, dashboardUrl, marketingUrl)
│   │   ├── kovrin/
│   │   │   ├── api.ts            # Kovrin pipeline API client + WebSocket
│   │   │   ├── context.tsx       # KovrinProvider — React context (pipelines, WS, approvals)
│   │   │   └── types.ts          # TypeScript types (PipelineStatus, Trace, WsMessage, ...)
│   │   └── superwork/
│   │       ├── api.ts            # SuperWork API client + WebSocket
│   │       ├── context.tsx       # SuperWorkProvider — React context (session, metrics, proposals)
│   │       └── types.ts          # SuperWork types (TaskProposal, MetricsSnapshot, ...)
│   ├── app/
│   │   ├── (marketing)/          # Route group — landing page (kovrin.dev)
│   │   │   ├── layout.tsx
│   │   │   └── page.tsx          # Hero, Features, Pricing, Waitlist, Comparison
│   │   ├── (dashboard)/          # Route group — dashboard (app.kovrin.dev)
│   │   │   ├── layout.tsx        # KovrinProvider + Sidebar wrapper
│   │   │   ├── overview/page.tsx
│   │   │   ├── pipeline/page.tsx
│   │   │   ├── pipeline/[id]/page.tsx
│   │   │   ├── approvals/page.tsx
│   │   │   ├── audit/page.tsx
│   │   │   ├── compliance/page.tsx  # Compliance report, safety scores
│   │   │   ├── costs/page.tsx       # Cost tracking, token usage
│   │   │   ├── settings/page.tsx    # Autonomy profiles + risk routing matrix
│   │   │   └── superwork/        # SuperWork sub-routes (SuperWorkProvider wrapper)
│   │   │       ├── layout.tsx
│   │   │       ├── page.tsx      # Session control + metrics
│   │   │       ├── proposals/page.tsx
│   │   │       └── feed/page.tsx
│   │   ├── docs/                 # Documentation (docs.kovrin.dev)
│   │   │   ├── getting-started/
│   │   │   ├── architecture/
│   │   │   └── api-reference/
│   │   └── api/
│   │       ├── waitlist/route.ts         # PostgreSQL waitlist (lazy pool)
│   │       └── proxy/
│   │           ├── kovrin/[...path]/     # Proxy → kovrin-api /api/*
│   │           └── superwork/[...path]/  # Proxy → kovrin-api /api/superwork/*
│   └── components/
│       ├── kovrin/               # 11 pipeline dashboard components (sidebar, pipeline-list, risk-badge, risk-matrix, autonomy-controls, ...)
│       └── superwork/            # 5 SuperWork components (session-control, metrics-panel, proposal-queue, live-feed, metric-card)
├── CLAUDE.md                 # Pointer → kovrin/CLAUDE.md
├── railway.toml              # builder = nixpacks
├── nixpacks.toml             # Node 20, npm ci, npm run build
└── package.json              # Next.js 16, React 19, Tailwind v4
```

### Deployment Flow
**kovrin-api:** `git push origin main` → Railway auto-builds z Dockerfile → `uvicorn kovrin.api.server:app`
**kovrin-web (3 služby):** `git push origin main` → Railway Nixpacks → `npm ci && npm run build && npm start` (každá služba má iný `SITE_MODE`)

### Testovanie v produkcii
```bash
# Marketing
curl -s -o /dev/null -w "%{http_code}" https://kovrin.dev/

# Docs
curl -s -o /dev/null -w "%{http_code}" https://docs.kovrin.dev/getting-started

# Dashboard (redirects / → /overview)
curl -s -o /dev/null -w "%{http_code}" https://app.kovrin.dev/overview

# Dashboard → API proxy (should return JSON, not 502)
curl https://app.kovrin.dev/api/proxy/kovrin/status

# API direct
curl https://api.kovrin.dev/api/health

# Run pipeline
curl -X POST https://api.kovrin.dev/api/run \
  -H "Content-Type: application/json" \
  -d '{"intent": "Search for AI safety frameworks", "constraints": [], "context": {}}'
```

---

## Git Konvencie

- **Branch naming**: `feat/risk-router-override`, `fix/merkle-chain-verify`, `docs/quickstart`
- **Commit format** (Conventional Commits): `feat:`, `fix:`, `docs:`, `test:`, `refactor:`, `chore:`
- **PR veľkosť**: Max 400 riadkov (bez testov). Väčšie zmeny rozdeliť.
- **Nikdy nekomitovať**: `.env`, `kovrin.db`, `__pycache__`, `.pyc`, API kľúče
- **Dual-repo workflow**: Zmeny často zasahujú **oba** repozitáre (kovrin + kovrin-web). Vždy commitni a pushni oba ak boli zmenené. Poradie: kovrin (backend) prvý, potom kovrin-web (frontend).

---

## CI/CD Pipeline

### kovrin (Python backend) — `.github/workflows/ci.yml`

| Job | Čo robí | Blocking? |
|-----|---------|-----------|
| **test** | `pytest` (Python 3.12 + 3.13), 70% coverage requirement, Codecov upload | ✅ Áno |
| **typecheck** | `mypy` s `--disallow-untyped-defs` (excludes superwork/examples) | ⚠️ Non-blocking (warning) |
| **security** | `pip-audit` dependency vulnerability scan | ⚠️ Non-blocking (warning) |

**Trigger:** push/PR na `main`
**Skipped tests:** `test_api.py`, `test_superwork_api.py` (vyžadujú bežiaci server)

### kovrin-web (Next.js frontend) — `.github/workflows/ci.yml`

| Job | Čo robí | Blocking? |
|-----|---------|-----------|
| **lint** | ESLint (`npm run lint`) | ✅ Áno |
| **typecheck** | TypeScript (`tsc --noEmit`) | ✅ Áno |
| **build** | Next.js production build (`npm run build`), závisí na lint + typecheck | ✅ Áno |
| **security** | `npm audit --audit-level=high` | ⚠️ Non-blocking (warning) |

**Trigger:** push/PR na `main`

### Railway Deployment (Production)

| Služba | Builder | Health check | Auto-deploy |
|--------|---------|-------------|-------------|
| **kovrin-api** | Dockerfile (Python 3.12-slim + uvicorn) | `/api/health` | ✅ push na `main` |
| **kovrin-web** | Nixpacks (Node 20 + Next.js) | `/` | ✅ push na `main` |

**Flow:** `git push origin main` → GitHub Actions CI → (ak pass) → Railway auto-build → deploy

> **Poznámka:** Railway deploy nie je gated za CI — spustí sa paralelne. Pre gated deploy treba Railway GitHub integration s required checks.

---

## Known Issues & Tech Debt

| Problém | Priorita | Poznámka |
|---------|----------|---------|
| SQLite v produkcii | 🟡 Stredná | Pre produkciu → Temporal/EventStoreDB/Kafka |
| Pre-existing API tests | 🟡 Nízka | `test_api.py` + `test_superwork_api.py` vyžadujú bežiaci server. Skip cez `--ignore`. |
| End-to-end SuperWork pipeline | 🟡 Stredná | Posledný item Fázy 1 — celý SuperWork flow ešte nebol testovaný end-to-end. |
| FeasibilityCritic tuning | 🟢 Nízka | Funguje (4/4 PASS), ale pri zložitejších promptoch môže rejected rate byť vysoký. |

---

## Competitive Landscape (február 2026)

### 8 funkcií, ktoré nemá nikto iný

| # | Feature |
|---|---------|
| 1 | TLA+ formálna verifikácia |
| 2 | Constitutional Layer 0 axiomy |
| 3 | Merkle hash chain audit trail |
| 4 | Delegation Capability Tokens |
| 5 | Risk-based routing matrix s CRITICAL guard |
| 6 | Tiered speculative execution |
| 7 | MCTS + beam search pre decision exploration |
| 8 | Process Reward Models |

### Konkurencia

| Framework | Stars | Funding | Safety |
|-----------|-------|---------|--------|
| LangGraph | 24.9K | $260M | ❌ Žiadna safety architektúra |
| CrewAI | 44K | $18–24.5M | ⚠️ Basic guardrails |
| AutoGen → Microsoft | 50.4K | — | ⚠️ Basic |
| NeMo Guardrails | 5.7K | — | ✅ Guardrails, nie orchestrácia |
| Temporal | — | $300M | ❌ Durable execution, žiadna safety |

> Nikto nemá formálnu verifikáciu, kryptografický audit, ani risk routing.

### Trh

- ~$7–8B (2025) → $50–100B (2030)
- EU AI Act: compliance od augusta 2026
- 78% firiem s AI agentmi nemá security guardrails
- $9.77M priemerný breach v healthcare

### Stratégia

**Dual approach**:
1. **Vertical Safety SaaS** pre regulované odvetvia (healthcare, fintech, government)
2. **Safety middleware** pre existujúce frameworky (`pip install kovrin-safety`)

**Čo posilniť** (obraniteľné, regulácia vyžaduje): TLA+, Merkle audit, Layer 0, risk routing  
**Čo odložiť** (trh dnes nepýta): MCTS/beam search, speculative execution

---

## Design System (pre dashboard/web prácu)

| Token | Hodnota |
|-------|---------|
| Border radius | `0px` všade |
| Primary | `#10B981` (Emerald — safety green) |
| Background | `#0A0A0B` (near black) |
| Surface | `#111113` |
| Border | `#27272A` |
| Font (code/UI) | JetBrains Mono |
| Font (display) | Instrument Sans |
| Font (body) | DM Sans |
| Framework | Next.js 16 + Tailwind CSS v4 + shadcn/ui (0 radius) |
| Icons | Lucide React |

Kompletná design spec: `docs/kovrin-design-spec.jsx`

---

## SuperWork — Supervisor Platform (IMPLEMENTOVANÉ)

SuperWork je vrstva nad KOVRIN frameworkom — supervisor platforma kde ty vidíš agentov "cez sklo", schvaľuješ kroky a sleduješ globálne metriky. **Kompletná dokumentácia:** `docs/SUPERWORK.md`

### Implementované komponenty

| Komponent | Súbor | Čo robí | Stav |
|-----------|-------|--------|------|
| Session Watcher | `src/kovrin/superwork/session_watcher.py` | `fs.watch` na `~/.claude/projects/`, detekuje task completion | ✅ |
| Context Injector | `src/kovrin/superwork/context_injector.py` | ChromaDB + RAG, chirurgický kontext pre každý task | ✅ |
| Orchestrator Agent | `src/kovrin/superwork/orchestrator.py` | Opus — analyzuje stav, navrhuje ďalšie kroky | ✅ |
| Metrics Tracker | `src/kovrin/superwork/metrics.py` | Velocity, cost, predikcia dokončenia | ✅ |
| SuperWork CLI | `src/kovrin/superwork/cli.py` | `kovrin superwork --project <path>` | ✅ |
| Supervisor Dashboard | `kovrin-web/src/components/superwork/` | 5 React komponentov (session, metrics, proposals, feed, metric-card) | ✅ |
| SuperWork API routes | `src/kovrin/api/superwork_router.py` | FastAPI endpoints + WebSocket live feed | ✅ |

### Ako to celé funguje

```
kovrin superwork --project ~/projects/bidbox
      │
      ├── Session Watcher → sleduje ~/.claude/projects/bidbox/
      ├── Context DB → zaindexuje celý projekt (RAG)
      ├── Orchestrator → analyzuje stav, navrhne 3 tasky
      └── Dashboard → ty schváliš, KOVRIN spustí agentov
            └── po dokončení → späť na Orchestrator → dookola
```

### Nové závislosti (superwork extra)

```toml
superwork = [
    "watchdog>=4.0",               # fs.watch
    "chromadb>=0.5",               # Vector DB
    "sentence-transformers>=3.0",  # Lokálne embeddings
    "rich>=13.0",                  # CLI output
    "click>=8.0",                  # CLI
]
```

---

## Čo chýba pre produkciu

**Fáza 0 — Open Source Launch** ✅ KOMPLETNÁ (2026-02-25)
- [x] Landing page kovrin.dev (hero + waitlist + features + pricing) — `kovrin-web` repo
- [x] Doména `kovrin.dev` zakúpená
- [x] Opraviť kovrin-web deploy na Railway (waitlist graceful degradation bez DATABASE_URL)
- [x] Docs cleanup — 100% presné API ukážky, správne domény (kovrin.dev), aktuálne test counts
- [x] PEP 440 verzia (`2.0.0a1`) pre PyPI kompatibilitu
- [x] CHANGELOG.md (Keep a Changelog formát)
- [x] `pip install kovrin` na PyPI — `kovrin-2.0.0a1` (whl + sdist, published 2026-02-24)
- [x] GitHub Release v2.0.0a1 — prerelease, published 2026-02-24
- [x] GitHub repo public — `github.com/nkovalcin/kovrin`
- [x] DNS verifikácia — všetky 4 domény live: kovrin.dev, app.kovrin.dev, docs.kovrin.dev, api.kovrin.dev
- [x] kovrin-api na Railway — custom domain `api.kovrin.dev`, health OK, PipelineManager initialized
- [x] 3-service architektúra — marketing/dashboard/docs z jedného repo cez SITE_MODE middleware
- [x] Čisté dashboard URL — `app.kovrin.dev/overview` (nie `/app/overview`)

**Fáza 1 — SuperWork MVP** ✅ (okrem E2E testu)
- [x] Session Watcher daemon — `src/kovrin/superwork/session_watcher.py`
- [x] Context Injector (ChromaDB + sentence-transformers) — `src/kovrin/superwork/context_injector.py`
- [x] Orchestrator Agent (Opus) — `src/kovrin/superwork/orchestrator.py`
- [x] Metrics Tracker — `src/kovrin/superwork/metrics.py`
- [x] SuperWork models + repository — `src/kovrin/superwork/models.py`, `repository.py`
- [x] SuperWork API routes — `src/kovrin/api/superwork_router.py`
- [x] `kovrin superwork` CLI — `src/kovrin/superwork/cli.py`
- [x] Web Supervisor Dashboard (kovrin-web) — overview, proposals, feed, approvals
- [x] Dashboard v kovrin repo (Vite, starý prototyp) — 5 SuperWork komponentov
- [ ] End-to-end testovanie SuperWork pipeline

**Fáza 2 — Native Mac App (4-8 týždne)**
- [ ] Tauri wrapper, Menu Bar ikonka, macOS notifikácie

**Fáza 3 — Produkcia (2-3 mesiace)**
- [ ] Temporal (durable execution), EventStoreDB
- [x] OpenTelemetry — instrumented: constitutional, critics, parser, risk_router, watchdog, executor

**Fáza 4 — SaaS (3-6 mesiacov)**
- [ ] Team features, multi-tenant, SOC 2, marketplace

**Fáza X — KOVRIN ako AI Operating System (dlhodobá vízia)**

Kovrin sa stane keyboard-first AI workspace — nie framework knižnica, ale plnohodnotná aplikácia (web/desktop) kde user ovláda všetko z jedného textového inputu.

Koncept:
- **Jeden input v strede obrazovky.** User píše, Kovrin orchestruje.
- **Multi-projekt, multi-session, multi-agent.** User má otvorených N projektov, každý má sessions, agenti pracujú paralelne.
- **Opus rozhoduje, Sonnet stavia.** Smart model switching — Opus ako orchestrátor, Sonnet na implementáciu, Haiku na triviálne tasky. Cost efficiency.
- **Keyboard-first, mouse-less.** Žiadna myš. Všetko cez klávesové skratky a text. Efektívnejšie, zdravšie, sústrednejšie.
- **User vidí všetko.** Sessions, agenti, ktoré súbory sa menia (live), generované obrázky/videá, orchestrátor status.
- **Plne autonómny ale s human loop.** Agenti si sami definujú ďalšie prompty, systematicky vylepšujú. User koriguje smer.

Layout:
```
┌─Sessions──┐  ┌─Agenti────┐  ┌─Súbory (live)─┐  ┌─Media──┐
│ projekt A  │  │ agent 1   │  │ src/app.py    │  │ images │
│ projekt B  │  │ agent 2   │  │ src/api.py    │  │ video  │
│ projekt C  │  │ agent 3   │  │ LIVE CHANGES  │  │ gen    │
└────────────┘  └───────────┘  └───────────────┘  └────────┘

┌─Orchestrator (Opus)──────────────────────────────────────┐
│ "Projekt A: refactor → 3 tasks → Sonnet, parallel, 4m"  │
└──────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────┐
│  > _  jeden input. píšeš. všetko sa deje.                │
└──────────────────────────────────────────────────────────┘
```

5 pilierov:
1. **Security** — Constitutional Core, Merkle audit, DCT tokeny (máme)
2. **Smart Model Switching** — Opus/Sonnet/Haiku routing (máme providers)
3. **Cost Efficiency** — správny model na správny task
4. **Autonomy** — agenti si sami plánujú ďalšie kroky
5. **Human Loop** — user vidí a koriguje, jeden input

Integrácie: MCP, Chrome automation, Playwright, screen recording — všetko cez kvalitné prompty.
Platforma: Web app (Next.js) → Desktop (Tauri) → Mouse-less AI workspace.

> Toto je Y Combinator level vízia. Engine pod kapotou = to čo máme. UI/UX = to čo treba postaviť.

---

## Priorita práce (poradie pre Claude Code)

1. 🔴 **Safety correctness** — Nikdy neporušiť 6 invariantov
2. 🟡 **End-to-end SuperWork pipeline test** — posledný item Fázy 1
3. 🟡 **SuperWork UI doladenie** — UX nie je ešte kompletné
4. 🟢 **Docs site** — docs.kovrin.dev (content, Fumadocs)
5. 🔵 **Fáza 2** — Native Mac App (Tauri)

---

<!--
╔══════════════════════════════════════════════════════════════════════════════╗
║  CLAUDE CODE — RÝCHLA ORIENTÁCIA                                             ║
║                                                                              ║
║  KOVRIN REPO (tento):                                                        ║
║    Začni tu:    src/kovrin/__init__.py  (hlavné API)                         ║
║    Safety:      src/kovrin/core/constitutional.py  (Layer 0, NEDOTÝKAJ SA)  ║
║    SuperWork:   src/kovrin/superwork/  (session_watcher, orchestrator, ...)  ║
║    Testy:       .venv/bin/python -m pytest tests/ -v                         ║
║                                                                              ║
║  KOVRIN-WEB REPO (~/Desktop/projects/kovrin-web/):                           ║
║    Marketing:   src/app/(marketing)/page.tsx                                 ║
║    Dashboard:   src/app/(dashboard)/  (overview, pipeline, superwork, ...)   ║
║    Proxy:       src/app/api/proxy/  (→ api.kovrin.dev)                       ║
║    Stack:       Next.js 16 + React 19 + Tailwind v4                          ║
║                                                                              ║
║  DOMÉNY: kovrin.dev (marketing) | app.kovrin.dev (dashboard)                 ║
║          api.kovrin.dev (backend) | docs.kovrin.dev (docs, TBD)              ║
║                                                                              ║
║  "The question isn't whether we'll build AGI.                                ║
║   The question is whether we'll build the safety infrastructure first."      ║
╚══════════════════════════════════════════════════════════════════════════════╝
-->
