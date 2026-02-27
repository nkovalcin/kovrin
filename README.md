<p align="center">
  <h1 align="center">KOVRIN</h1>
  <p align="center"><strong>Provable safety for AI agents in production</strong></p>
  <p align="center">
    Constitutional constraints · Formal verification · Cryptographic audit trail
  </p>
</p>

<p align="center">
  <a href="https://github.com/nkovalcin/kovrin/blob/main/LICENSE"><img src="https://img.shields.io/badge/license-MIT-green?style=flat-square" alt="License" /></a>
  <a href="https://github.com/nkovalcin/kovrin"><img src="https://img.shields.io/github/stars/nkovalcin/kovrin?style=flat-square&color=10B981" alt="Stars" /></a>
</p>

---

**KOVRIN** is the only AI agent framework that combines **formal verification (TLA+)**, **constitutional safety constraints**, and a **cryptographic audit trail** into a single orchestration engine. Not guardrails — guarantees.

Most frameworks treat safety as an afterthought: prompt-level instructions that can be ignored, overridden, or hallucinated away. KOVRIN treats safety as infrastructure — mathematically verified invariants that hold before your agent touches production.

## Why KOVRIN?

| | KOVRIN | LangGraph | CrewAI | NeMo Guardrails |
|---|---|---|---|---|
| Formal verification (TLA+) | Yes | No | No | No |
| Constitutional constraints | Yes (5 axioms, SHA-256) | No | No | Partial |
| Cryptographic audit trail | Yes (Merkle hash chain) | No | No | No |
| Risk-based routing | Yes (4x3 matrix + overrides) | No | No | No |
| Human-in-the-loop | Yes (configurable per risk level) | Manual | No | No |
| Multi-agent coordination | Yes (DCT tokens, scope narrowing) | Yes | Yes | No |
| EU AI Act pre-mapped | Yes (Art. 9, 12, 14, 15) | No | No | No |

## Quick Start

```bash
pip install kovrin
export ANTHROPIC_API_KEY=sk-ant-...
```

```python
from kovrin import Kovrin

engine = Kovrin(tools=True)
result = engine.run_sync(
    intent="Search for Python 3.13 features and summarize them",
    constraints=["Be concise", "Focus on developer-relevant features"],
)

# Behind the scenes, KOVRIN:
# 1. Parsed intent into structured subtasks (IntentV2)
# 2. Ran every subtask through 3 critics (safety, feasibility, policy)
# 3. Verified constitutional constraints (5 axioms, SHA-256)
# 4. Built execution DAG with dependency resolution
# 5. Routed each task through risk matrix (AUTO/SANDBOX/HUMAN)
# 6. Executed with safety-gated tools (web search, code analysis, etc.)
# 7. Logged every event to Merkle hash chain

print(result.output)
print(result.traces)  # Full audit trail
```

Or async:

```python
result = await engine.run("Analyze costs and suggest savings")
```

## Architecture

```
User: "Search for Python 3.13 features"
     |
     v
+- IntentV2 -------------------------------------------+
|  AMR-inspired graph, speech act, semantic frame       |
|  Optional: MCTS exploration (5 variants, UCB1)        |
+------------------------+-----------------------------+
                         v
+- Critic Pipeline (per subtask) ----------------------+
|  SafetyCritic --> ConstitutionalCore (5 axioms)       |
|  FeasibilityCritic --> "Is this achievable?"          |
|  PolicyCritic --> "Does this violate constraints?"    |
|  All must PASS. Any REJECT = task blocked.            |
+------------------------+-----------------------------+
                         v
+- ExecutionGraph -------------------------------------+
|  DAG: nodes = approved tasks, edges = dependencies    |
|  Topological sort --> wave-based execution            |
|  Strategies: Graph / Beam Search / Multi-Agent        |
+------------------------+-----------------------------+
                         v
+- RiskRouter + TaskExecutor --------------------------+
|  Risk Matrix:                                         |
|          FREE      GUARDED     NONE                   |
|  LOW    AUTO       AUTO        SANDBOX                |
|  MED    AUTO       SANDBOX     HUMAN                  |
|  HIGH   SANDBOX    HUMAN       HUMAN                  |
|  CRIT   HUMAN      HUMAN       HUMAN  <- always      |
+------------------------+-----------------------------+
                         v
+- Output ---------------------------------------------+
|  ExecutionResult: output, traces, graph, rejected     |
|  Merkle hash chain: every event SHA-256 chained       |
+------------------------------------------------------+
```

## Core Concepts

### Layer 0 — Constitutional Core

5 immutable axioms verified **before every action** with SHA-256 integrity checks:

| Axiom | Guarantee |
|-------|-----------|
| Human Agency | No action removes human override ability |
| Harm Floor | Expected harm never exceeds threshold |
| Transparency | All decisions traceable to intent |
| Reversibility | Prefer reversible over irreversible |
| Scope Limit | Never exceed authorized boundary |

All-or-nothing: one axiom fails = entire task rejected. No exceptions.

### Risk-Based Routing

Every task is scored for risk and routed through a configurable matrix:

```python
from kovrin import Kovrin, AutonomySettings
from kovrin.core.models import AutonomyProfile  # or: from kovrin import AutonomyProfile

engine = Kovrin(
    autonomy_settings=AutonomySettings(profile=AutonomyProfile.CAUTIOUS)
)

# CRITICAL risk = always HUMAN_APPROVAL (hardcoded, non-overridable)
```

### Merkle Audit Trail

Every event is cryptographically chained. Tamper-evident, append-only:

```python
from kovrin import ImmutableTraceLog

log = ImmutableTraceLog()
# ... after execution ...
valid, message = log.verify_integrity()
assert valid  # True if no tampering
```

### Safety-Gated Tools

8 built-in tools with per-tool risk profiles, sandboxed execution, and Merkle-audited calls:

```python
engine = Kovrin(tools=True)

# Built-in: web_search, calculator, datetime, json_transform,
#           code_analysis, http_request, file_read, file_write
# Each tool has risk_level, requires_sandbox, allowed_domains
```

### Multi-Agent Coordination

Secure agent coordination with **Delegation Capability Tokens (DCT)**:

```python
engine = Kovrin(agents=True, enable_tokens=True)

# Agents receive scoped tokens:
# - Allowed risk levels (e.g., LOW only)
# - Max tasks, max depth, time-to-live
# - Parent token chain (hierarchical delegation)
# Scope can only NARROW, never widen.
```

### Watchdog

Independent safety monitor with temporal rules and graduated containment:

```python
engine = Kovrin(watchdog=True)

# Monitors for:
# - Execution after rejection -> KILL
# - >50% failure rate -> PAUSE
# - Unexpected event sequences -> WARN
# - Agent drift (PRM < 0.35) -> PAUSE
# Graduated: WARN -> PAUSE -> KILL (irreversible)
```

## EU AI Act Compliance

KOVRIN maps directly to EU AI Act requirements:

| EU AI Act Article | KOVRIN Feature |
|---|---|
| Article 9 (Risk management) | Constitutional constraints + watchdog |
| Article 12 (Record-keeping) | Merkle hash chain audit trail |
| Article 14 (Human oversight) | Risk-based routing + human-in-the-loop |
| Article 15 (Accuracy & robustness) | Formal verification (TLA+) + critic pipeline |

## TLA+ Formal Verification

8 TLA+ specification modules with 10 safety invariants, machine-checked:

```
specs/
  TaskStateMachine.tla    -- Task lifecycle state machine
  AxiomValidation.tla     -- Constitutional axiom verification
  RoutingMatrix.tla       -- Risk routing decisions
  GraphExecution.tla      -- DAG execution semantics
  WatchdogMonitor.tla     -- Temporal monitoring rules
  SpeculationModel.tla    -- Speculative execution tiers
  HashChain.tla           -- Merkle chain immutability
  KovrinSafety.tla        -- Top-level composition (10 invariants)
```

## Project Structure

```
src/kovrin/
  core/           # Pydantic models, Constitutional Core (Layer 0)
  intent/         # IntentV2 schema, HTN parser
  engine/         # Graph executor, risk router, MCTS, beam search, PRM, tokens
  safety/         # Critics pipeline, watchdog agent
  audit/          # Immutable trace logger (Merkle hash chain)
  agents/         # Agent coordinator, registry
  tools/          # 8 safety-gated tools (web search, code analysis, etc.)
  providers/      # Multi-model (Claude, OpenAI, Ollama) + circuit breaker
  api/            # FastAPI server (REST + WebSocket)
  schema/         # JSON Schema + TypeScript exporter
  storage/        # SQLite persistence

specs/            # TLA+ formal verification (8 modules)
dashboard/        # React/TypeScript dashboard (16 components)
tests/            # 1,100+ tests (unit + adversarial + E2E + integration)
```

## Testing

```bash
pip install -e ".[dev]"
pytest tests/ -v                       # All tests
pytest -m adversarial -v               # 42 adversarial attack tests
pytest -m "not integration"            # Without API calls
```

## Contributing

We welcome contributions!

```bash
git clone https://github.com/nkovalcin/kovrin.git
cd kovrin
pip install -e ".[dev]"
pytest
```

## License

MIT — see [LICENSE](LICENSE) for details.

## Links

- **Website**: [kovrin.dev](https://kovrin.dev)
- **Documentation**: [docs.kovrin.dev](https://docs.kovrin.dev/getting-started)
- **GitHub**: [github.com/nkovalcin/kovrin](https://github.com/nkovalcin/kovrin)

---

Built by [Norbert Kovalcin](https://nkovalcin.com) — DIGITAL SPECIALISTS s.r.o.

*"The question isn't whether we'll build AGI. The question is whether we'll build the safety infrastructure first."*
