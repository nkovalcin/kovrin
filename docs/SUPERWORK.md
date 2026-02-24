# KOVRIN — SuperWork Layer: Supervisor Platform

> Interný dokument. Verzia: 1.0 | Február 2026 | Norbert Kovalčín

---

## Čo je SuperWork vrstva

SuperWork je produkčná nadstavba nad KOVRIN frameworkom. Zatiaľ čo KOVRIN rieši *bezpečnosť* AI agentov (constitutional safety, audit, risk routing), SuperWork rieši *prevádzku* — ako agenti pracujú nepretržite, ako ty ako supervisor vidíš čo robia, a ako sa rozhoduješ o ďalších krokoch.

**Metafora**: KOVRIN je motor lietadla (bezpečnostné záruky, fyzika letu). SuperWork je kokpit (ty vidíš inštrumenty, rozhoduješ o kurze, zasahuješ keď treba).

```
TY (Supervisor)
└── SuperWork Dashboard (macOS / Web)
    ├── Orchestrator Agent (Opus — analyzuje, plánuje, rozhoduje)
    │   ├── Session Watcher (číta Claude Code output)
    │   ├── Context Injector (Vector DB → chirurgický kontext)
    │   └── Next Step Proposer (navrhuje ďalšie tasky)
    └── Executor Agent(s) (1-2 × Claude Code / Sonnet)
        ├── Executor A — kód, testy, refactoring
        └── Executor B — docs, review, deploy prep
        
KOVRIN Framework (pod kapotou každého agenta)
├── Constitutional safety
├── Risk routing + HUMAN_APPROVAL gate
├── Merkle audit trail
└── Watchdog (WARN → PAUSE → KILL)
```

---

## Nové komponenty (čo treba postaviť)

### 1. Session Watcher (`src/kovrin/superwork/session_watcher.py`)

Claude Code ukladá sessions v `~/.claude/projects/`. Každý projekt má JSON súbory s celou konverzáciou.

**Čo robí:**
- `fs.watch` (Python: `watchdog` knižnica) na `~/.claude/projects/`
- Parsuje nové/zmenené JSON session súbory
- Detekuje "task completion" eventy (keď Claude Code skončí task)
- Extrahuje: čo sa urobilo, čo sa pokazilo, aký je výsledok
- Posiela event do Orchestrator Agenta

**Štruktúra session súboru (Claude Code):**
```
~/.claude/projects/<project-hash>/
├── <session-uuid>.jsonl     # JSONL — každý riadok je jeden event
└── ...
```

Každý riadok v `.jsonl`:
```json
{"type": "assistant", "content": "...", "timestamp": "..."}
{"type": "tool_use", "name": "bash", "input": {...}}
{"type": "tool_result", "content": "...", "exit_code": 0}
```

**Implementácia:**
```python
# src/kovrin/superwork/session_watcher.py
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler
import json, asyncio
from pathlib import Path

CLAUDE_SESSIONS_PATH = Path.home() / ".claude" / "projects"

class SessionWatcher:
    def __init__(self, on_task_complete: callable):
        self.on_task_complete = on_task_complete  # callback
        self._observer = Observer()
        
    def start(self):
        handler = SessionEventHandler(self.on_task_complete)
        self._observer.schedule(handler, str(CLAUDE_SESSIONS_PATH), recursive=True)
        self._observer.start()
        
    def stop(self):
        self._observer.stop()
        self._observer.join()

class SessionEventHandler(FileSystemEventHandler):
    def on_modified(self, event):
        if event.src_path.endswith(".jsonl"):
            self._parse_session(event.src_path)
    
    def _parse_session(self, path: str):
        # Čítaj posledné riadky, detekuj completion
        # Emituj TaskCompletionEvent
        ...

class TaskCompletionEvent:
    session_id: str
    project_path: str
    completed_task: str     # čo sa urobilo
    output_summary: str     # výsledok
    files_changed: list[str]
    errors: list[str]
    duration_seconds: int
    timestamp: str
```

---

### 2. Context Injector / Vector DB (`src/kovrin/superwork/context_injector.py`)

**Problém**: Keď agent dostane task, nemôže dostať celý projekt (príliš drahé, halucinácie). Musí dostať len relevantnú časť.

**Riešenie**: Vector DB s celým projektovým kontextom. Pred každým `engine.run()` sa urobí RAG — retrieval relevantných chunks.

**Čo sa indexuje:**
- Celá codebase (súbory, funkcie, triedy)
- README, CLAUDE.md, ARCHITECTURE.md
- Biznis pravidlá a constraints
- História predchádzajúcich taskov a ich výsledkov
- Otvorené bugy, TODO komentáre

**Implementácia (ChromaDB — lokálne, žiadny cloud):**
```python
# src/kovrin/superwork/context_injector.py
import chromadb
from pathlib import Path

class ProjectContextDB:
    def __init__(self, project_path: str):
        self.client = chromadb.PersistentClient(
            path=str(Path(project_path) / ".kovrin" / "context_db")
        )
        self.collection = self.client.get_or_create_collection("project_context")
    
    def index_project(self, project_path: str):
        """Zaindexuj celý projekt pri štarte."""
        # Prechádzaj všetky .py, .ts, .md súbory
        # Chunking: funkcie, triedy, sekcie docs
        # Embeddings cez sentence-transformers (lokálne, free)
        # Ulož do ChromaDB
        ...
    
    def get_relevant_context(self, task: str, max_chunks: int = 10) -> str:
        """Chirurgicky presný výsek kontextu pre daný task."""
        results = self.collection.query(
            query_texts=[task],
            n_results=max_chunks
        )
        # Zoraď podľa relevance, zformatuj ako string
        return self._format_context(results)
    
    def update_on_change(self, changed_files: list[str]):
        """Re-indexuj len zmenené súbory po každom task completion."""
        ...
```

**Integrácia do KOVRIN engine:**
```python
# Modifikácia src/kovrin/core/engine.py
async def arun(self, intent: str) -> ExecutionResult:
    # NOVÉ: Inject relevantný kontext pred parsovaním
    if self.context_db:
        relevant_context = self.context_db.get_relevant_context(intent)
        enriched_intent = f"{intent}\n\n[PROJECT CONTEXT]\n{relevant_context}"
    else:
        enriched_intent = intent
    
    # Existujúci pipeline...
    parsed = await self.intent_parser.parse(enriched_intent)
    ...
```

---

### 3. Orchestrator Agent (`src/kovrin/superwork/orchestrator.py`)

Mozog systému. Beží ako daemon, analyzuje stav projektu, navrhuje ďalšie kroky.

**Zodpovednosti:**
- Prijíma `TaskCompletionEvent` od Session Watchera
- Analyzuje celkový progress (kde sme, čo zostáva)
- Navrhuje ďalšie tasky (s prioritou a odôvodnením)
- Rozhoduje či ísť auto alebo čakať na tvoje schválenie
- Generuje denné/týždenné správy

**Model routing:**
- Orchestrator → `claude-opus-4-20250514` (hlboká analýza, rozhodovanie)
- Executori → `claude-sonnet-4-20250514` (rýchle kódovanie)
- Metriky/sumarizácia → `claude-haiku-4-5-20251001` (lacné, rýchle)

```python
# src/kovrin/superwork/orchestrator.py
class OrchestratorAgent:
    def __init__(self, kovrin_engine: Kovrin, context_db: ProjectContextDB):
        self.engine = kovrin_engine
        self.context_db = context_db
        self.task_history: list[TaskCompletionEvent] = []
        
    async def on_task_complete(self, event: TaskCompletionEvent):
        """Zavolá sa po každom dokončenom tasku."""
        self.task_history.append(event)
        self.context_db.update_on_change(event.files_changed)
        
        analysis = await self._analyze_state()
        proposals = await self._propose_next_steps(analysis)
        
        # Zašli návrhy do dashboardu / čakaj na schválenie
        await self._send_proposals_to_dashboard(proposals)
    
    async def _analyze_state(self) -> ProjectAnalysis:
        """Opus analyzuje celkový stav projektu."""
        # Zober posledných 10 taskov, README, TODO
        # Pošli Opusovi, dostaneš štruktúrovanú analýzu
        ...
    
    async def _propose_next_steps(self, analysis: ProjectAnalysis) -> list[TaskProposal]:
        """Opus navrhne 3-5 ďalších taskov s prioritou."""
        ...

class TaskProposal:
    title: str
    description: str          # Čo presne urobiť
    rationale: str            # Prečo to teraz
    estimated_tokens: int     # Odhadovaná cena
    risk_level: RiskLevel     # LOW/MEDIUM/HIGH
    auto_execute: bool        # Môže ísť auto, alebo čaká na teba
    dependencies: list[str]   # Čo musí byť hotové pred
```

---

### 4. Supervisor Dashboard (`dashboard/src/`)

**Čo vidíš** (React + WebSocket stream):

```
┌─────────────────────────────────────────────────────────────┐
│  KOVRIN SuperWork                              [●] LIVE      │
├─────────────────┬───────────────────────────────────────────┤
│  AGENT TREE     │  ORCHESTRATOR CONTEXT                     │
│                 │  "Analyzing BidBox API layer..."          │
│  ◎ Orchestrator │  Last task: Fixed payment endpoint        │
│  │  (thinking)  │  Next: Add rate limiting middleware       │
│  │              │  Confidence: 87%                          │
│  ├─● Executor A │                                           │
│  │  (executing) │  PROPOSALS (awaiting your approval)       │
│  │              │  ┌─────────────────────────────────────┐  │
│  └─○ Executor B │  │ 1. Add Redis rate limiting   [HIGH] │  │
│     (idle)      │  │    ~800 tokens | 2 files            │  │
│                 │  │    [✓ Auto-execute] [✗ Skip]        │  │
│                 │  ├─────────────────────────────────────┤  │
│                 │  │ 2. Write tests for payment flow [MED│  │
│                 │  │    ~1200 tokens | 3 files           │  │
│                 │  │    [✓ Approve] [✗ Skip]             │  │
│                 │  └─────────────────────────────────────┘  │
├─────────────────┴───────────────────────────────────────────┤
│  GLOBAL METRICS                                             │
│  Tasks today: 23  │  Tokens: 48,420  │  Cost: $0.87        │
│  Velocity: 4.6/hr │  Success: 96%    │  Errors: 1          │
├─────────────────────────────────────────────────────────────┤
│  PREDICTION (based on current velocity)                     │
│  ████████████████████░░░░░░░░░░  67% complete               │
│  At this pace → MVP ready in 18 days (March 13)            │
│  ○ Tasks remaining: 47  ○ Est. total cost: $12.40          │
└─────────────────────────────────────────────────────────────┘
```

**Technológia:**
- React 18 + TypeScript
- WebSocket pre real-time streamy
- Tailwind + shadcn/ui (0 border-radius, dark mode)
- Tauri wrapper pre native macOS app (Phase 2)

**API endpoints (FastAPI):**
```
GET  /api/status              # Aktuálny stav agentov
GET  /api/proposals           # Čakajúce návrhy
POST /api/proposals/{id}/approve  # Schváliť a spustiť task
POST /api/proposals/{id}/skip     # Preskočiť
POST /api/agents/{id}/pause       # Pauznúť agenta
POST /api/agents/{id}/kill        # KILL (cez KOVRIN Watchdog)
WS   /ws/live                 # Real-time event stream
```

---

### 5. Prediktívne metriky (`src/kovrin/superwork/metrics.py`)

```python
class VelocityTracker:
    """Sleduje rýchlosť práce a predikuje dokončenie."""
    
    def tasks_per_hour(self) -> float: ...
    def tokens_per_task(self) -> float: ...
    def success_rate(self) -> float: ...
    def cost_today(self) -> float: ...
    def cost_per_task(self) -> float: ...
    
    def predict_completion(self, remaining_tasks: int) -> PredictionResult:
        """Na základe velocity predikuje kedy bude produkt hotový."""
        hours_remaining = remaining_tasks / self.tasks_per_hour()
        cost_remaining = remaining_tasks * self.cost_per_task()
        return PredictionResult(
            completion_date=datetime.now() + timedelta(hours=hours_remaining),
            estimated_cost=cost_remaining,
            confidence=self._confidence_score()
        )
```

---

## Ako to celé funguje spolu

```
1. Ty spustíš: `kovrin superwork --project ~/projects/bidbox`

2. Session Watcher začne sledovať ~/.claude/projects/bidbox/

3. Context Injector zaindexuje celý projekt do Vector DB

4. Orchestrator sa prebudí, analyzuje stav, navrhne 3 tasky

5. Dashboard zobrazí návrhy — ty klikneš "Approve" na 2 z nich

6. KOVRIN engine spustí 2 executor agenty paralelne:
   - Constitutional check (Layer 0)
   - Risk routing (LOW → AUTO_EXECUTE)
   - Claude Code beží, píše kód
   - Merkle trail loguje každý krok

7. Claude Code skončí → Session Watcher detekuje completion

8. Context Injector aktualizuje Vector DB (len zmenené súbory)

9. Orchestrator analyzuje výsledok, navrhne ďalšie kroky

10. → späť na krok 4, dookola, celý deň

TY len: schvaľuješ, zasahuješ, sleduješ progress cez "sklo"
```

---

## Roadmap k produkčnému produktu

### Fáza 0 — Open Source Launch (ZAJTRA)
- [x] KOVRIN core framework (480 testov, TLA+, constitutional safety)
- [x] CLAUDE.md, README, ARCHITECTURE.md
- [ ] GitHub release + PyPI `pip install kovrin`
- [ ] Landing page kovrin.dev (jednoduchá, len hero + waitlist)

### Fáza 1 — SuperWork MVP (2-4 týždne)
- [ ] Session Watcher (Python daemon, watchdog knižnica)
- [ ] Context Injector (ChromaDB, sentence-transformers)
- [ ] Orchestrator Agent (Opus API calls)
- [ ] Simple web dashboard (React, no Tauri yet)
- [ ] CLI: `kovrin superwork --project <path>`
- [ ] Prediktívne metriky (velocity, cost, ETA)

### Fáza 2 — Native Mac App (4-8 týždne po Fáze 1)
- [ ] Tauri wrapper pre dashboard
- [ ] Menu Bar ikonka s live statusom
- [ ] Notifikácie (macOS native)
- [ ] Multi-project support

### Fáza 3 — Produkčná infraštruktúra (2-3 mesiace)
- [ ] Temporal namiesto asyncio (durable execution, crash recovery)
- [ ] EventStoreDB pre audit trail (namiesto in-memory)
- [ ] Multi-model support (OpenAI, Mistral, Gemini) 
- [ ] LangGraph integrácia (`kovrin-safety` middleware)
- [ ] OpenTelemetry export

### Fáza 4 — SaaS (3-6 mesiacov)
- [ ] app.kovrin.dev (hosted dashboard)
- [ ] Team features (viac supervisorov, role)
- [ ] Compliance exports (SOC 2, HIPAA ready)
- [ ] Marketplace taskov / workflow šablóny

---

## Nové súbory na vytvorenie

```
src/kovrin/superwork/
├── __init__.py
├── session_watcher.py    # fs.watch na ~/.claude/projects/
├── context_injector.py   # ChromaDB + RAG
├── orchestrator.py       # Opus-powered analysis + proposals
├── metrics.py            # Velocity tracking + predictions
└── cli.py                # `kovrin superwork` entry point

dashboard/src/
├── components/
│   ├── AgentTree.tsx      # Stromový view agentov
│   ├── ProposalCard.tsx   # Návrh s Approve/Skip tlačidlami
│   ├── MetricsBar.tsx     # Tasks/tokens/cost/velocity
│   ├── PredictionBar.tsx  # 300-dňová predikcia
│   └── LiveFeed.tsx       # Real-time event stream
└── hooks/
    └── useWebSocket.ts    # WS connection na /ws/live

src/kovrin/api/
└── superwork_router.py   # FastAPI routes pre SuperWork UI
```

---

## Nové závislosti

```toml
# pyproject.toml additions
[project.optional-dependencies]
superwork = [
    "watchdog>=4.0",           # fs.watch pre session files
    "chromadb>=0.5",           # Vector DB (lokálne)
    "sentence-transformers>=3.0",  # Lokálne embeddings (free)
    "rich>=13.0",              # CLI output
    "click>=8.0",              # CLI framework
]
```

---

## Strategická pozícia

SuperWork + KOVRIN = prvý **safety-first AI agent supervisor** s:

1. **Formálnou verifikáciou** (TLA+, jediný na trhu)
2. **Constitutional safety** (nie runtime filter, ale architektonická garancia)
3. **Kryptografickým auditom** (Merkle chain, tamper-evident)
4. **Chirurgickým context managementom** (Vector DB, šetrí tokeny)
5. **Supervisor dashboard** ("sklenená stena" — ty vidíš každého agenta)
6. **Prediktívnymi metrikami** (kde budeš o 300 dní)

Nikto toto nemá v jednom produkte. LangGraph, CrewAI, AutoGen — žiadny nemá body 1-3.
SuperWork pridáva body 4-6 a robí z toho kompletný produkčný nástroj.
