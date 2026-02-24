<p align="center">
  <h1 align="center">◆ KOVRIN</h1>
  <p align="center"><strong>Provable safety for AI agents in production</strong></p>
  <p align="center">
    Constitutional constraints · Formal verification · Cryptographic audit trail
  </p>
</p>

<p align="center">
  <a href="https://pypi.org/project/kovrin/"><img src="https://img.shields.io/pypi/v/kovrin?style=flat-square&color=10B981" alt="PyPI" /></a>
  <a href="https://github.com/nkovalcin/kovrin/blob/main/LICENSE"><img src="https://img.shields.io/badge/license-MIT-green?style=flat-square" alt="License" /></a>
  <a href="https://github.com/nkovalcin/kovrin"><img src="https://img.shields.io/github/stars/nkovalcin/kovrin?style=flat-square&color=10B981" alt="Stars" /></a>
  <a href="https://kovrin.dev/docs/getting-started"><img src="https://img.shields.io/badge/docs-kovrin.dev-3B82F6?style=flat-square" alt="Docs" /></a>
</p>

---

**KOVRIN** is the only AI agent framework that combines **formal verification (TLA+)**, **constitutional safety constraints**, and a **cryptographic audit trail** into a single orchestration engine. Not guardrails — guarantees.

Most frameworks treat safety as an afterthought: prompt-level instructions that can be ignored, overridden, or hallucinated away. KOVRIN treats safety as infrastructure — mathematically verified invariants that hold before your agent touches production.

## Why KOVRIN?

| | KOVRIN | LangGraph | CrewAI | NeMo Guardrails |
|---|---|---|---|---|
| Formal verification (TLA+) | ✅ | ❌ | ❌ | ❌ |
| Constitutional constraints | ✅ (5 axioms, SHA-256 integrity) | ❌ | ❌ | Partial |
| Cryptographic audit trail | ✅ (Merkle hash chain) | ❌ | ❌ | ❌ |
| Risk-based routing | ✅ (4×3 matrix + overrides) | ❌ | ❌ | ❌ |
| Human-in-the-loop | ✅ (configurable per risk level) | Manual | ❌ | ❌ |
| Multi-agent coordination | ✅ (DCT tokens, scope narrowing) | ✅ | ✅ | ❌ |
| EU AI Act pre-mapped | ✅ (Art. 9, 12, 14, 15) | ❌ | ❌ | ❌ |

## Quick Start

```bash
pip install kovrin
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
User: "Analyze costs and suggest savings"
     │
     ▼
┌─ IntentV2 ─────────────────────────────────────────┐
│  AMR-inspired graph, speech act, semantic frame     │
│  Optional: MCTS exploration (5 variants, UCB1)      │
└────────────────────────┬────────────────────────────┘
                         ▼
┌─ Critic Pipeline (per subtask) ────────────────────┐
│  SafetyCritic ──→ ConstitutionalCore (5 axioms)    │
│  FeasibilityCritic ──→ "Is this achievable?"       │
│  PolicyCritic ──→ "Does this violate constraints?" │
│  All must PASS. Any REJECT → task blocked.         │
└────────────────────────┬────────────────────────────┘
                         ▼
┌─ ExecutionGraph ───────────────────────────────────┐
│  DAG: nodes = approved tasks, edges = dependencies  │
│  Topological sort → wave-based execution            │
│  Strategies: Graph / Beam Search / Multi-Agent      │
└────────────────────────┬────────────────────────────┘
                         ▼
┌─ RiskRouter + TaskExecutor ────────────────────────┐
│  Risk Matrix:                                       │
│          FREE      GUARDED     NONE                 │
│  LOW    AUTO       AUTO        SANDBOX              │
│  MED    AUTO       SANDBOX     HUMAN                │
│  HIGH   SANDBOX    HUMAN       HUMAN                │
│  CRIT   HUMAN      HUMAN       HUMAN  ← always     │
│                                                     │
│  + AutonomyProfile overrides                        │
│  + Watchdog (kill/pause/warn)                       │
└────────────────────────┬────────────────────────────┘
                         ▼
┌─ Output ───────────────────────────────────────────┐
│  ExecutionResult: output, traces, graph, rejected   │
│  Merkle hash chain: every event SHA-256 chained     │
│  Optional: confidence scores per task (PRM)         │
└─────────────────────────────────────────────────────┘
```

## Core Concepts

### Constitutional Constraints

KOVRIN enforces 5 axioms that **cannot be bypassed**. They are verified with SHA-256 integrity checks — if the axiom definitions are tampered with, the engine refuses to start.

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
    autonomy_settings=AutonomySettings(profile=AutonomyProfile.CAUTIOUS),
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
# - Execution after rejection → KILL
# - >50% failure rate → PAUSE
# - Unexpected event sequences → WARN
# - Agent drift (PRM < 0.35) → PAUSE
# Graduated: WARN → PAUSE → KILL (irreversible)
```

## Configuration

```python
from kovrin import Kovrin, AutonomySettings
from kovrin.core.models import AutonomyProfile

engine = Kovrin(
    api_key="sk-ant-...",             # Or set ANTHROPIC_API_KEY env var
    max_concurrent=5,                 # Semaphore limit
    watchdog=True,                    # Enable watchdog
    agents=True,                      # Enable multi-agent
    tools=True,                       # Enable safety-gated tools
    explore=False,                    # MCTS exploration
    enable_prm=False,                 # Process Reward Model
    enable_tokens=True,               # Delegation Capability Tokens
    autonomy_settings=AutonomySettings(profile=AutonomyProfile.CAUTIOUS),
)
```

## EU AI Act Compliance

KOVRIN maps directly to EU AI Act requirements:

| EU AI Act Article | KOVRIN Feature |
|---|---|
| Article 9 (Risk management) | Constitutional constraints + watchdog |
| Article 12 (Record-keeping) | Merkle hash chain audit trail |
| Article 14 (Human oversight) | Risk-based routing + human-in-the-loop |
| Article 15 (Accuracy & robustness) | Formal verification (TLA+) + critic pipeline |

## Documentation

- **[Getting Started](https://kovrin.dev/docs/getting-started)** — 5-minute quickstart
- **[Architecture](https://kovrin.dev/docs/architecture)** — Deep dive into internals
- **[API Reference](https://kovrin.dev/docs/api-reference)** — Full API documentation

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

- **Website**: [kovrin.dev](https://kovrin.dev)
- **Documentation**: [kovrin.dev/docs](https://kovrin.dev/docs/getting-started)
- **GitHub**: [github.com/nkovalcin/kovrin](https://github.com/nkovalcin/kovrin)
- **PyPI**: [pypi.org/project/kovrin](https://pypi.org/project/kovrin)

---

Built by [Norbert Kovalcin](https://nkovalcin.com) — DIGITAL SPECIALISTS s.r.o.

*"The question isn't whether we'll build AGI. The question is whether we'll build the safety infrastructure first."*
