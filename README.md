<p align="center">
  <h1 align="center">KOVRIN</h1>
  <p align="center"><strong>Provable safety for AI agents in production</strong></p>
  <p align="center">
    Constitutional constraints · Formal verification · Cryptographic audit trail
  </p>
</p>

<p align="center">
  <a href="https://pypi.org/project/kovrin/"><img src="https://img.shields.io/pypi/v/kovrin?style=flat-square&color=10B981" alt="PyPI" /></a>
  <a href="https://github.com/nkovalcin/kovrin/blob/main/LICENSE"><img src="https://img.shields.io/badge/license-MIT-green?style=flat-square" alt="License" /></a>
  <a href="https://github.com/nkovalcin/kovrin"><img src="https://img.shields.io/github/stars/nkovalcin/kovrin?style=flat-square&color=10B981" alt="Stars" /></a>
  <a href="https://docs.kovrin.dev"><img src="https://img.shields.io/badge/docs-kovrin.dev-3B82F6?style=flat-square" alt="Docs" /></a>
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
```

```python
from kovrin import Kovrin

engine = Kovrin()

result = await engine.run(
    intent="Analyze costs and suggest savings",
    constraints=["Do not suggest layoffs"],
    context={"budget": 15000}
)

# Behind the scenes, KOVRIN:
# 1. Parsed intent into structured subtasks (IntentV2)
# 2. Ran every subtask through 3 critics (safety, feasibility, policy)
# 3. Verified constitutional constraints (5 axioms, SHA-256)
# 4. Built execution DAG with dependency resolution
# 5. Routed each task through risk matrix (AUTO/SANDBOX/HUMAN)
# 6. Executed with concurrent semaphore (max 5)
# 7. Logged every event to Merkle hash chain

print(result.output)
print(result.traces)  # Full audit trail
```

Or synchronously:

```python
result = engine.run_sync("Analyze costs and suggest savings")
```

## Architecture

```
User: "Analyze costs and suggest savings"
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
from kovrin.core.models import AutonomyProfile

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
assert log.verify_integrity()  # True if no tampering
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

### MCTS + Beam Search

Explore multiple decomposition strategies before committing:

```python
engine = Kovrin(explore=True, mcts_iterations=5, beam_width=3)
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
  TaskStateMachine.tla    — Task lifecycle state machine
  AxiomValidation.tla     — Constitutional axiom verification
  RoutingMatrix.tla       — Risk routing decisions
  GraphExecution.tla      — DAG execution semantics
  WatchdogMonitor.tla     — Temporal monitoring rules
  SpeculationModel.tla    — Speculative execution tiers
  HashChain.tla           — Merkle chain immutability
  KovrinSafety.tla        — Top-level composition (10 invariants)
```

## Project Structure

```
src/kovrin/
  core/           # Pydantic models, Constitutional Core (Layer 0)
  intent/         # IntentV2 schema, HTN parser
  engine/         # Graph executor, risk router, MCTS, beam search, PRM, tokens
  safety/         # Critics pipeline, watchdog agent
  audit/          # Immutable trace logger (Merkle hash chain)
  agents/         # Agent coordinator, registry, tools
  api/            # FastAPI server (REST + WebSocket + SSE)
  schema/         # JSON Schema + TypeScript exporter
  storage/        # SQLite persistence

specs/            # TLA+ formal verification (8 modules)
dashboard/        # React/TypeScript dashboard (12 components)
tests/            # 480 tests (unit + adversarial + integration)
```

## Schema Export

Auto-generate TypeScript types from Pydantic models:

```bash
python -m kovrin.schema.exporter --list                    # List 29 models, 13 enums
python -m kovrin.schema.exporter --json-schema schemas/    # Export JSON Schema
python -m kovrin.schema.exporter --typescript types.ts     # Generate TypeScript
python -m kovrin.schema.exporter --validate existing.ts    # Detect drift
```

## Testing

```bash
pip install -e ".[dev]"
pytest tests/ -v              # All 480 tests
pytest -m adversarial -v      # 29 adversarial attack tests
pytest -m "not integration"   # Without Claude API calls
```

## Contributing

We welcome contributions! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

```bash
git clone https://github.com/nkovalcin/kovrin.git
cd kovrin
pip install -e ".[dev]"
pytest
```

## License

MIT — see [LICENSE](LICENSE) for details.

## Links

- **Website**: [kovrin.ai](https://kovrin.ai)
- **Documentation**: [docs.kovrin.dev](https://docs.kovrin.dev)
- **GitHub**: [github.com/nkovalcin/kovrin](https://github.com/nkovalcin/kovrin)
- **PyPI**: [pypi.org/project/kovrin](https://pypi.org/project/kovrin)

---

Built by [Norbert Kovalcin](https://nkovalcin.com) — DIGITAL SPECIALISTS s.r.o.

*"The question isn't whether we'll build AGI. The question is whether we'll build the safety infrastructure first."*
