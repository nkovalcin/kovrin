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

**Verzia frameworku:** `2.0.0-alpha`  
**Python:** `3.12+`  
**Stav:** Alpha — core implementovaný, prebieha open-source poriadok  
**Licencia:** MIT

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
| Testy | **734** (z toho 41 adversarial) |
| TLA+ špecifikácie | **8 modulov**, 10 safety invariantov |
| Pydantic modely | **29 modelov, 13 enumov** |
| Dashboard komponenty | **12** (React/TypeScript) |
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
│   │   └── models.py          # 29 Pydantic modelov, 13 enumov
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
│   │   └── topology.py        # TopologyAnalyzer
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
│   ├── api/
│   │   └── server.py          # FastAPI — REST + WebSocket + SSE
│   ├── schema/
│   │   ├── exporter.py        # SchemaExporter (JSON Schema + TypeScript)
│   │   └── __main__.py        # CLI: python -m kovrin.schema
│   ├── storage/
│   │   └── repository.py      # SQLite persistence
│   ├── exceptions.py          # KovrinError hierarchy (9 exception types)
│   ├── logging.py             # Structured logging (JSON + human-readable)
│   ├── cli.py                 # CLI: kovrin run, verify, audit, serve, status
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
├── dashboard/               # React/TypeScript dashboard
│   ├── src/
│   │   ├── App.tsx
│   │   ├── types/kovrin.ts    # ✅ Auto-generated by SchemaExporter (29 models, 13 enums)
│   │   ├── api/client.ts
│   │   └── components/        # 12 komponentov
│   └── package.json
├── tests/                   # 734 testov
│   ├── test_adversarial.py        # 30 adversarial (P0 + P1)
│   ├── test_adversarial_tokens.py # 11 adversarial (P2)
│   ├── test_adversarial_tools.py  # 13 adversarial (tool safety)
│   ├── test_providers.py          # Provider abstraction tests
│   ├── test_web_search.py         # Brave Search integration tests
│   ├── test_exceptions.py         # Exception hierarchy tests
│   ├── test_cli.py                # CLI command tests
│   ├── test_schema_exporter.py    # 24 testov
│   └── test_*.py                  # Unit + integration
├── docs/
│   ├── Kovrin_Whitepaper_v2.docx
│   ├── ARCHITECTURE.md
│   ├── CLAUDE_OPENSOURCE.md       # TARGET CLAUDE.md pre open-source release
│   ├── README_OPENSOURCE.md       # TARGET README pre open-source release
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
- `AgentDriftTracker` — Jensen-Shannon divergencia, `CrossAgentConsistency`

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
| `ConstitutionalCore` | Zero externé závislosti. Žiadne API volania, žiadne I/O. |
| `RiskRouter` | Pure data — matrix + overrides. Žiadne side effects. |
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
.venv/bin/python -m pytest tests/ -v                              # Všetky (734)
.venv/bin/python -m pytest tests/ -m adversarial -v              # Adversarial (41)
.venv/bin/python -m pytest tests/test_schema_exporter.py -v      # Schema (24)
.venv/bin/python -m pytest tests/ -m "not integration" -v        # Bez API calls

# ── CLI ───────────────────────────────────────────────────────────────────────
.venv/bin/python -m kovrin.cli run "Search for Python 3.13 features" --tools
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

## Git Konvencie

- **Branch naming**: `feat/risk-router-override`, `fix/merkle-chain-verify`, `docs/quickstart`
- **Commit format** (Conventional Commits): `feat:`, `fix:`, `docs:`, `test:`, `refactor:`, `chore:`
- **PR veľkosť**: Max 400 riadkov (bez testov). Väčšie zmeny rozdeliť.
- **Nikdy nekomitovať**: `.env`, `kovrin.db`, `__pycache__`, `.pyc`, API kľúče

---

## Known Issues & Tech Debt

| Problém | Priorita | Poznámka |
|---------|----------|---------|
| `dashboard/src/types/kovrin.ts` | ✅ Vyriešené | Regenerované cez SchemaExporter (29 models, 13 enums). Udržiavať cez `--typescript` exporter. |
| `docs/CLAUDE_OPENSOURCE.md` je TARGET súbor | 🟡 Stredná | Obsahuje idealizovanú štruktúru, nie súčasný stav. Po cleanup merge do tohto CLAUDE.md. |
| SQLite v produkcii | 🟡 Stredná | Pre produkciu → Temporal/EventStoreDB/Kafka |
| Multi-model | ✅ Vyriešené | ClaudeProvider, OpenAIProvider, OllamaProvider + ModelRouter |
| CLI | ✅ Vyriešené | `kovrin run`, `kovrin verify`, `kovrin audit`, `kovrin serve`, `kovrin status` |
| GitHub Actions CI | ✅ Vyriešené | pytest + coverage + mypy + ruff + pip-audit |
| Tool execution | ✅ Vyriešené | 8 safety-gated tools, SafeToolRouter, Brave Search API |
| Custom exceptions | ✅ Vyriešené | KovrinError hierarchy (9 types) |
| Structured logging | ✅ Vyriešené | JSON + human-readable via kovrin.logging |

---

## Čo chýba pre produkciu

1. **Infraštruktúra**: in-memory → Temporal (durable execution), EventStoreDB, Kafka
2. ~~**Integrácie**: len Claude API → multi-model~~ ✅ (OpenAI, Ollama + ModelRouter)
3. **LangGraph middleware**: `pip install kovrin-safety` wrapper
4. ~~**CLI**: `kovrin run`, `kovrin verify`, `kovrin audit`~~ ✅
5. **Certifikácie**: SOC 2, HIPAA, FedRAMP
6. **OpenTelemetry**: export traces do štandardných observability nástrojov
7. **Komunita**: 0 stars, 0 externých používateľov — potrebná launch stratégia
8. ~~**GitHub Actions CI**: pytest + mypy + ruff pipeline~~ ✅ (+ coverage + pip-audit)
9. **Docs site**: docs.kovrin.dev (Fumadocs alebo podobné)
10. **Refactor hardcoded model strings**: 10 miest s `claude-sonnet-4-20250514` → provider abstrakcia

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
| Framework | Next.js 15 + Tailwind CSS v4 + shadcn/ui (0 radius) |
| Icons | Lucide React |

Kompletná design spec: `docs/kovrin-design-spec.jsx`

---

## SuperWork — Produkčná nadstavba (NOVÁ PRIORITA)

SuperWork je vrstva nad KOVRIN frameworkom — supervisor platforma kde ty vidíš agentov "cez sklo", schvaľuješ kroky a sleduješ globálne metriky. **Kompletná dokumentácia:** `docs/SUPERWORK.md`

### Nové komponenty (treba postaviť)

| Komponent | Súbor | Čo robí |
|-----------|-------|--------|
| Session Watcher | `src/kovrin/superwork/session_watcher.py` | `fs.watch` na `~/.claude/projects/`, detekuje task completion |
| Context Injector | `src/kovrin/superwork/context_injector.py` | ChromaDB + RAG, chirurgický kontext pre každý task |
| Orchestrator Agent | `src/kovrin/superwork/orchestrator.py` | Opus — analyzuje stav, navrhuje ďalšie kroky |
| Metrics Tracker | `src/kovrin/superwork/metrics.py` | Velocity, cost, predikcia dokončenia |
| SuperWork CLI | `src/kovrin/superwork/cli.py` | `kovrin superwork --project <path>` |
| Supervisor Dashboard | `dashboard/src/components/` | React UI — stromový view, schvaľovanie, metriky |
| SuperWork API routes | `src/kovrin/api/superwork_router.py` | FastAPI endpoints + WebSocket live feed |

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

**Fáza 0 — Open Source Launch (ZAJTRA)**
- [ ] GitHub release + `pip install kovrin` na PyPI
- [ ] Landing page kovrin.ai (hero + waitlist)

**Fáza 1 — SuperWork MVP (2-4 týždne)**
- [ ] Session Watcher daemon
- [ ] Context Injector (ChromaDB + sentence-transformers)
- [ ] Orchestrator Agent (Opus)
- [ ] Web Supervisor Dashboard (React)
- [ ] `kovrin superwork` CLI

**Fáza 2 — Native Mac App (4-8 týždne)**
- [ ] Tauri wrapper, Menu Bar ikonka, macOS notifikácie

**Fáza 3 — Produkcia (2-3 mesiace)**
- [ ] Temporal (durable execution), EventStoreDB, multi-model, OpenTelemetry

**Fáza 4 — SaaS (3-6 mesiacov)**
- [ ] app.kovrin.ai, team features, SOC 2, marketplace

---

## Priorita práce (poradie pre Claude Code)

1. 🔴 **Safety correctness** — Nikdy neporušiť 6 invariantov
2. ✅ ~~TypeScript drift fix~~ — Vyriešené (regenerované cez SchemaExporter)
3. 🟡 **SuperWork — Session Watcher** — základ celej SuperWork vrstvy
4. 🟡 **SuperWork — Context Injector** — ChromaDB + RAG
5. 🟡 **SuperWork — Orchestrator** — Opus analysis + proposals
6. 🟡 **SuperWork — Dashboard** — React supervisor UI
7. 🟢 **Public API poriadok** — Čisté exports z `__init__.py`
8. 🟢 **Test coverage** — Každá public metóda má testy
9. 🔵 **CLI** — `kovrin run`, `kovrin verify`, `kovrin audit`, `kovrin superwork`

---

<!--
╔══════════════════════════════════════════════════════════════════════════════╗
║  CLAUDE CODE — RÝCHLA ORIENTÁCIA                                             ║
║                                                                              ║
║  Začni tu:    src/kovrin/__init__.py  (hlavné API)                           ║
║  Safety:      src/kovrin/core/constitutional.py  (Layer 0, NEDOTÝKAJ SA)    ║
║  Testy:       .venv/bin/python -m pytest tests/ -v                           ║
║  Types:       dashboard/src/types/kovrin.ts (auto-generated, 29+13)          ║
║                                                                              ║
║  "The question isn't whether we'll build AGI.                                ║
║   The question is whether we'll build the safety infrastructure first."      ║
╚══════════════════════════════════════════════════════════════════════════════╝
-->
