# KOVRIN — Technical Architecture Document

> Internal reference for development. Not for public distribution.
> Version: 1.0 | February 2026 | Norbert Kovalčín

---

## 1. System Overview

KOVRIN is a Python framework for orchestrating AI agents with provable safety guarantees. It combines formal verification (TLA+), constitutional constraints, risk-based routing, and a cryptographic audit trail into a single execution engine.

**Core pipeline**: Intent parsing → Critic evaluation → DAG construction → Risk-routed execution → Audited output.

**Key numbers**:
- 37 Python source files in `src/kovrin/`
- 29 Pydantic models, 13 enums
- 3-7 Claude API calls per intent (standard), 15-30 with MCTS
- SHA-256 for hash chain and constitutional integrity
- HMAC-SHA256 for delegation token signing

---

## 2. Pipeline Flow

### 2.1 Intent Processing

```
User input (natural language)
     │
     ▼
IntentParser.parse(input) → Claude API
     │
     ▼
IntentV2:
  ├── amr_graph: AMR-inspired semantic representation
  ├── speech_act: DIRECTIVE | QUERY | COMMISSIVE | ...
  ├── semantic_frame: structured slots (agent, action, object, constraints)
  └── subtasks: list[SubTask] — decomposed actionable units
```

**IntentV2** is the internal representation. It captures not just "what" the user wants but "how" (speech act), "within what constraints" (semantic frame), and "in what order" (subtask decomposition with dependencies).

**Optional: MCTS Exploration** (`explore=True`):
- Generates 5 prompt variants of the same intent
- UCB1 tree search over variant space
- CriticBasedScorer evaluates each via critic pipeline
- Returns best variant + all candidates for comparison
- Cost: 5× more API calls (15-30 total)

### 2.2 Critic Pipeline

Runs for **every SubTask** independently. All three critics must PASS.

```
SubTask
  │
  ├──→ SafetyCritic
  │      └──→ ConstitutionalCore.evaluate()
  │             ├── 5 axioms checked (all-or-nothing)
  │             ├── SHA-256 integrity of axiom definitions
  │             └── Result: PASS or REJECT + violation details
  │
  ├──→ FeasibilityCritic (parallel)
  │      └──→ Claude API: "Is this task achievable given context?"
  │             └── Result: PASS or REJECT + reasoning
  │
  └──→ PolicyCritic (parallel)
         └──→ Claude API: "Does this violate any constraints?"
                └── Result: PASS or REJECT + violated constraint

All PASS → task proceeds to execution
Any REJECT → task status = REJECTED_BY_L0, never executes
```

**SafetyCritic** is the only critic that does NOT call Claude API. It runs against `ConstitutionalCore` which is pure local computation. This is intentional — the safety floor cannot depend on an external API.

**FeasibilityCritic** and **PolicyCritic** run in parallel (`asyncio.gather`) against Claude API.

### 2.3 Constitutional Core

The heart of KOVRIN's safety model.

```
ConstitutionalCore:
  ├── axioms: list[Axiom] — 5 hardcoded safety rules
  ├── custom_constraints: list[str] — user-defined rules
  ├── integrity_hash: str — SHA-256 of axiom definitions
  │
  ├── evaluate(subtask) → ConstitutionalResult
  │     ├── Checks all 5 axioms against subtask
  │     ├── All-or-nothing: if ANY axiom fails → REJECT
  │     └── Returns: pass/fail per axiom + overall result
  │
  └── verify_integrity() → bool
        └── Recomputes SHA-256, compares to stored hash
            If mismatch → axioms were tampered → engine refuses to start
```

**Axiom verification is non-bypassable.** There is no flag, no override, no admin mode that skips constitutional checks. The SHA-256 integrity verification ensures axiom definitions haven't been modified at runtime.

### 2.4 Execution Graph

```
Approved subtasks → ExecutionGraph
  │
  ├── Build DAG: nodes = tasks, edges = dependency relationships
  ├── Cycle detection (raises if cycles found)
  ├── Topological sort → execution waves
  │     Wave 0: [tasks with no dependencies]
  │     Wave 1: [tasks depending only on Wave 0]
  │     Wave 2: ...
  │
  └── Optional: TopologyAnalyzer
        └── Classify: SEQUENTIAL | PARALLEL | PIPELINE
            (informational, doesn't change execution)
```

### 2.5 Execution Strategies

Three execution strategies, selectable per run:

**GraphExecutor** (default):
- Executes waves sequentially, tasks within wave concurrently
- `asyncio.Semaphore(max_concurrent)` — default 5
- Each task → `TaskExecutor.execute()`

**BeamSearchExecutor** (optional):
- Maintains top-K candidates per wave
- Prunes based on score: `0.4 * critic_score + 0.6 * success_probability`
- Useful for exploration with pruning

**Multi-Agent via AgentCoordinator** (optional):
- `AgentCoordinator` assigns tasks to best-fit agents from `AgentRegistry`
- Issues DCT (Delegation Capability Token) per assignment
- Agent executes with role-specific system prompt
- Token scope enforces capability boundaries

### 2.6 Task Execution & Risk Routing

```
TaskExecutor.execute(subtask):
  │
  ├── RiskRouter.route(subtask) → RoutingDecision
  │     │
  │     ├── risk_level: LOW | MEDIUM | HIGH | CRITICAL
  │     ├── autonomy_profile: FREE | GUARDED | NONE
  │     │
  │     └── ROUTING MATRIX:
  │              FREE      GUARDED     NONE
  │     LOW     AUTO       AUTO        SANDBOX
  │     MED     AUTO       SANDBOX     HUMAN
  │     HIGH    SANDBOX    HUMAN       HUMAN
  │     CRIT    HUMAN      HUMAN       HUMAN  ← ALWAYS
  │
  │     + AutonomyProfile overrides (per-cell)
  │     + CRITICAL guard: hardcoded, non-overridable
  │
  ├── Route decision:
  │     AUTO_EXECUTE    → direct Claude API call
  │     SANDBOX_REVIEW  → execute + enhanced logging + review flag
  │     HUMAN_APPROVAL  → block, wait for /api/approve (timeout: 300s)
  │
  ├── Claude API (Sonnet) → task result
  │
  └── Optional: ProcessRewardModel (PRM)
        └── Step-level scoring: 0.0-1.0 per reasoning step
            Threshold: 0.6 (configurable)
            Below threshold → flag for review
```

**CRITICAL risk level is hardcoded to HUMAN_APPROVAL.** No configuration, no profile override, no cell-level override can change this. This is the absolute safety floor.

### 2.7 Audit Trail (Merkle Hash Chain)

```
GENESIS ("0" × 64)
     │
     ▼
Event₁: INTENT_RECEIVED
  hash₁ = SHA256(serialize(event₁) + GENESIS)
     │
     ▼
Event₂: DECOMPOSITION
  hash₂ = SHA256(serialize(event₂) + hash₁)
     │
     ▼
Event₃: CRITIC_PASS / CRITIC_REJECT
  hash₃ = SHA256(serialize(event₃) + hash₂)
     │
     ... (every event in pipeline)

ImmutableTraceLog:
  ├── append(event) → HashedTrace (event + hash + prev_hash)
  ├── verify_integrity() → bool (recompute all, check chain)
  ├── export(path) → JSON file (compliance-ready)
  └── subscribe(callback) → real-time event stream (for Watchdog)
```

**Append-only.** No delete, no modify. `verify_integrity()` recomputes the entire chain from genesis. Any break = tampering detected.

### 2.8 Watchdog

Independent safety monitor. Subscribes to `ImmutableTraceLog` events.

```
WatchdogAgent:
  │
  ├── NoExecutionAfterRejection
  │     └── Rejected task somehow executing? → KILL
  │
  ├── ExcessiveFailureRate
  │     └── > 50% tasks failed? → PAUSE
  │
  ├── UnexpectedEventSequence
  │     └── COMPLETE without START? → WARN
  │
  ├── AgentDriftTracker (if agents=True)
  │     ├── avg PRM < 0.2 + success < 30% → KILL
  │     ├── avg PRM < 0.35 OR success < 50% → PAUSE
  │     └── avg PRM < 0.5 → WARN
  │
  └── Graduated containment:
        WARN → PAUSE → KILL
        Direction: only escalate, NEVER de-escalate
        KILL is irreversible for the current run
```

### 2.9 Delegation Capability Tokens (DCT)

```
TokenAuthority:
  │
  ├── issue(agent, scope, ttl) → DelegationToken
  │     ├── HMAC-SHA256 signature
  │     ├── scope: {allowed_risk: [LOW], max_tasks: 1, max_depth: 1}
  │     ├── ttl: time-to-live (seconds)
  │     └── parent_token_id: for hierarchical delegation
  │
  ├── validate(token) → bool
  │     └── Check: signature + expiry + revocation list
  │
  └── revoke(token_id) → cascade to all child tokens

SCOPE NARROWING (invariant):
  Parent: {LOW, MEDIUM} → Child: max {LOW, MEDIUM}
  Parent: max_tasks=10 → Child: max_tasks ≤ 10
  Violation → ScopeViolationError (non-recoverable)
```

---

## 3. Data Models

### Core Models (Pydantic v2)

```python
# Intent
class IntentV2(BaseModel):          # AMR graph + speech act + semantic frame
class SubTask(BaseModel):           # Individual actionable unit
class TaskDependency(BaseModel):    # Edge in execution DAG

# Critics
class CriticResult(BaseModel):      # PASS/REJECT + reasoning
class ConstitutionalResult(BaseModel)  # Per-axiom results
class Axiom(BaseModel):             # Single constitutional axiom

# Execution
class ExecutionResult(BaseModel):   # Final output + traces + graph
class RoutingDecision(BaseModel):   # Risk level + route (AUTO/SANDBOX/HUMAN)
class WaveExecution(BaseModel):     # Tasks grouped by wave

# Agents
class Agent(BaseModel):             # Agent definition (role, capabilities)
class DelegationToken(BaseModel):   # DCT with scope + signature
class TokenScope(BaseModel):        # Allowed operations for agent

# Audit
class HashedTrace(BaseModel):       # Single event + hash + prev_hash
class TraceEvent(BaseModel):        # Event type + timestamp + data

# Risk
class AutonomyProfile(str, Enum):   # FREE | GUARDED | NONE
class RiskLevel(str, Enum):         # LOW | MEDIUM | HIGH | CRITICAL
class RouteAction(str, Enum):       # AUTO_EXECUTE | SANDBOX_REVIEW | HUMAN_APPROVAL
```

### Key Enums (13 total)

```python
RiskLevel:        LOW | MEDIUM | HIGH | CRITICAL
RouteAction:      AUTO_EXECUTE | SANDBOX_REVIEW | HUMAN_APPROVAL
AutonomyProfile:  FREE | GUARDED | NONE
SpeechAct:        DIRECTIVE | QUERY | COMMISSIVE | ASSERTIVE | EXPRESSIVE
TaskStatus:       PENDING | APPROVED | EXECUTING | COMPLETED | FAILED | REJECTED_BY_L0
CriticVerdict:    PASS | REJECT
WatchdogAction:   WARN | PAUSE | KILL
EventType:        INTENT_RECEIVED | DECOMPOSITION | CRITIC_PASS | CRITIC_REJECT |
                  EXECUTION_START | EXECUTION_COMPLETE | EXECUTION_FAILED |
                  HUMAN_APPROVAL_REQUESTED | HUMAN_APPROVED | HUMAN_REJECTED |
                  WATCHDOG_WARN | WATCHDOG_PAUSE | WATCHDOG_KILL
TraceIntegrity:   VALID | TAMPERED | EMPTY
TokenStatus:      ACTIVE | EXPIRED | REVOKED
TopologyType:     SEQUENTIAL | PARALLEL | PIPELINE
```

---

## 4. Storage & Persistence

### Current State (in-memory)

| Component | Storage | Limitation |
|---|---|---|
| Task execution | `asyncio` in-memory | Lost on crash |
| Trace log | `list[HashedTrace]` in-memory | Lost on crash |
| Event transport | Direct function calls | No replay |
| Database | SQLite (`kovrin.db`) | Single process |
| Hash chain | In-memory recompute | No persistence |
| Token store | `dict` in `TokenAuthority` | Lost on crash |

### Production Target (Phase 2+)

| Component | Target | Why |
|---|---|---|
| Task execution | Temporal | Durable execution, replay |
| Trace log | EventStoreDB | Append-only, event sourcing |
| Event transport | Kafka | Decoupled, replayable |
| Database | PostgreSQL | Multi-process, transactions |
| Hash chain | immudb | Tamper-proof by design |
| Token store | Redis + PostgreSQL | Fast validation + persistence |

**The main production gap is durability.** Everything works correctly but state is lost on crash. Temporal would give durable execution (same approach OpenAI uses for their agent infrastructure).

---

## 5. API Surface (Public)

### Primary Entry Point

```python
from kovrin import Kovrin, AutonomyProfile

engine = Kovrin(
    api_key: str,                              # Anthropic API key
    model: str = "claude-sonnet-4-20250514",   # Model to use
    autonomy: AutonomyProfile = AutonomyProfile.GUARDED,
    max_concurrent: int = 5,                   # Semaphore limit
    approval_timeout: int = 300,               # Seconds
    watchdog: bool = True,                     # Enable watchdog
    agents: bool = False,                      # Enable multi-agent
    explore: bool = False,                     # MCTS exploration
    prm: bool = False,                         # Process Reward Model
)

# Sync
result: ExecutionResult = engine.run(intent: str)

# Async
result: ExecutionResult = await engine.arun(intent: str)
```

### ExecutionResult

```python
result.output: str                    # Combined output
result.subtasks: list[SubTask]        # Decomposed tasks
result.traces: ImmutableTraceLog      # Full audit trail
result.graph: ExecutionGraph          # DAG structure
result.rejected: list[SubTask]        # Tasks that failed critics
result.metadata: ExecutionMetadata    # Timing, token usage, costs
```

### Constitution

```python
engine.constitution.add(constraint: str)          # Add custom constraint
engine.constitution.axioms: list[Axiom]            # View axioms (read-only)
engine.constitution.verify_integrity() -> bool     # SHA-256 check
```

### Audit

```python
result.traces.verify_integrity() -> bool           # Check chain
result.traces.export(path: str)                    # JSON export
result.traces.events: list[HashedTrace]            # All events
```

---

## 6. Security Model

### Threat Model

| Threat | Mitigation |
|---|---|
| Constitutional bypass | SHA-256 integrity, no runtime modification |
| Audit tampering | Merkle hash chain, append-only |
| Scope escalation (agents) | DCT with HMAC-SHA256, scope narrowing only |
| Rejected task execution | Watchdog `NoExecutionAfterRejection` → KILL |
| Agent drift | PRM scoring + drift tracker → graduated containment |
| API key exposure | Never logged, never in traces, env-only |
| Prompt injection via intent | Critic pipeline evaluates safety BEFORE execution |

### Trust Boundaries

```
UNTRUSTED:
  └── User input (natural language intent)
        └── Goes through: IntentParser → CriticPipeline → approval

TRUSTED (verified):
  ├── ConstitutionalCore (SHA-256 verified at startup)
  ├── RiskRouter (pure data, no external input)
  └── ImmutableTraceLog (Merkle chain, append-only)

SEMI-TRUSTED:
  ├── Claude API responses (validated by critic pipeline)
  ├── Agent outputs (scoped by DCT, monitored by watchdog)
  └── Human approvals (authenticated via API)
```

---

## 7. Dependency Map

```
kovrin (engine.py)
├── IntentParser ──────────→ Claude API (anthropic SDK)
│   └── IntentV2
│
├── CriticPipeline
│   ├── SafetyCritic ──────→ ConstitutionalCore (zero deps, pure)
│   ├── FeasibilityCritic ─→ Claude API
│   └── PolicyCritic ──────→ Claude API
│
├── RiskRouter ────────────→ Pure data (no deps)
│
├── TaskExecutor
│   ├──→ RiskRouter
│   ├──→ Claude API
│   └──→ ProcessRewardModel (optional) ──→ Claude API
│
├── GraphExecutor
│   └──→ TaskExecutor / AgentCoordinator
│
├── MCTSExplorer (optional)
│   ├──→ IntentParser
│   └──→ CriticBasedScorer ──→ CriticPipeline
│
├── BeamSearchExecutor (optional)
│   └──→ GraphExecutor
│
├── AgentCoordinator (optional)
│   ├──→ AgentRegistry ──→ Agent(s) ──→ Claude API
│   └──→ TokenAuthority
│
├── WatchdogAgent (optional, independent)
│   └──→ ImmutableTraceLog (read-only subscriber)
│
└── ImmutableTraceLog
    └── HashedTrace (SHA-256 chain, hashlib)
```

### External Dependencies (minimal)

```
anthropic          # Claude API SDK
pydantic >= 2.0    # Data validation
asyncio            # Concurrency (stdlib)
hashlib            # SHA-256 (stdlib)
hmac               # HMAC-SHA256 for DCT (stdlib)
sqlite3            # Local storage (stdlib)
```

Optional:
```
rich               # CLI output formatting
click              # CLI framework
opentelemetry-*    # Trace export (planned)
```

---

## 8. File Manifest

| File | Lines (est.) | Purpose |
|---|---|---|
| `engine.py` | ~300 | Main orchestrator, `Kovrin` class |
| `intent/parser.py` | ~150 | Intent decomposition via Claude |
| `intent/v2.py` | ~200 | IntentV2 data model + AMR graph |
| `intent/mcts.py` | ~250 | MCTS exploration + UCB1 |
| `critics/pipeline.py` | ~100 | Orchestrates 3 critics |
| `critics/safety.py` | ~80 | SafetyCritic → ConstitutionalCore |
| `critics/feasibility.py` | ~80 | FeasibilityCritic → Claude |
| `critics/policy.py` | ~80 | PolicyCritic → Claude |
| `constitution/core.py` | ~200 | 5 axioms, SHA-256, evaluation |
| `execution/graph.py` | ~200 | DAG, topo sort, waves |
| `execution/executor.py` | ~150 | GraphExecutor, semaphore |
| `execution/task.py` | ~180 | TaskExecutor, risk routing |
| `execution/beam.py` | ~150 | BeamSearchExecutor |
| `risk/router.py` | ~120 | RiskRouter, 4×3 matrix |
| `risk/profiles.py` | ~50 | AutonomyProfile enum + overrides |
| `agents/coordinator.py` | ~200 | Multi-agent orchestration |
| `agents/registry.py` | ~80 | Agent registration + lookup |
| `agents/agent.py` | ~100 | Agent class, role execution |
| `agents/tokens.py` | ~200 | TokenAuthority, DCT lifecycle |
| `audit/trace.py` | ~180 | ImmutableTraceLog, Merkle chain |
| `audit/export.py` | ~80 | JSON/compliance export |
| `watchdog/agent.py` | ~200 | WatchdogAgent, all monitors |
| `prm/model.py` | ~100 | ProcessRewardModel, step scoring |
| `models/*.py` | ~400 | 29 Pydantic models, 13 enums |

**Total**: ~3,900 lines (estimated)
