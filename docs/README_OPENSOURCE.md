<p align="center">
  <h1 align="center">◆ KOVRIN</h1>
  <p align="center"><strong>Provable safety for AI agents in production</strong></p>
  <p align="center">
    Constitutional constraints · Formal verification · Cryptographic audit trail
  </p>
</p>

<p align="center">
  <a href="https://pypi.org/project/kovrin/"><img src="https://img.shields.io/pypi/v/kovrin?style=flat-square&color=10B981" alt="PyPI" /></a>
  <a href="https://github.com/digital-specialists/kovrin/blob/main/LICENSE"><img src="https://img.shields.io/badge/license-MIT-green?style=flat-square" alt="License" /></a>
  <a href="https://github.com/digital-specialists/kovrin"><img src="https://img.shields.io/github/stars/digital-specialists/kovrin?style=flat-square&color=10B981" alt="Stars" /></a>
  <a href="https://discord.gg/kovrin"><img src="https://img.shields.io/badge/Discord-join-5865F2?style=flat-square" alt="Discord" /></a>
  <a href="https://docs.kovrin.dev"><img src="https://img.shields.io/badge/docs-kovrin.dev-3B82F6?style=flat-square" alt="Docs" /></a>
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
| Human-in-the-loop | ✅ (configurable, SLA timers) | Manual | ❌ | ❌ |
| Multi-agent coordination | ✅ (DCT tokens, scope narrowing) | ✅ | ✅ | ❌ |
| EU AI Act pre-mapped | ✅ (Art. 12, 14) | ❌ | ❌ | ❌ |

## Quick Start

```bash
pip install kovrin
```

```python
from kovrin import Kovrin

engine = Kovrin(api_key="sk-ant-...")

result = engine.run("Analyze costs and suggest savings")

# That's it. Behind the scenes, KOVRIN:
# 1. Parsed intent into structured subtasks (IntentV2)
# 2. Ran every subtask through 3 critics (safety, feasibility, policy)
# 3. Verified constitutional constraints (5 axioms, SHA-256)
# 4. Built execution DAG with dependency resolution
# 5. Routed each task through risk matrix (AUTO/SANDBOX/HUMAN)
# 6. Executed with concurrent semaphore (max 5)
# 7. Logged every event to Merkle hash chain

print(result.output)
print(result.traces)  # Full audit trail, verifiable
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

```python
from kovrin import Kovrin

engine = Kovrin(api_key="sk-ant-...")

# Add custom constraints
engine.constitution.add("Never execute financial transactions over $10,000 without human approval")
engine.constitution.add("Never access production databases in exploration mode")
```

### Risk-Based Routing

Every task is scored for risk and routed through a configurable matrix:

```python
from kovrin import Kovrin, AutonomyProfile

engine = Kovrin(
    api_key="sk-ant-...",
    autonomy=AutonomyProfile.GUARDED,  # FREE | GUARDED | NONE
)

# HIGH risk + GUARDED profile → HUMAN_APPROVAL required
# The engine blocks and waits for approval via API or dashboard
```

### Merkle Audit Trail

Every event is cryptographically chained. You can verify the entire execution history was not tampered with:

```python
result = engine.run("Process quarterly report")

# Verify integrity of the entire chain
assert result.traces.verify_integrity()  # True if no tampering

# Export for compliance
result.traces.export("audit_q1_2026.json")
```

### Multi-Agent Coordination

KOVRIN uses **Delegation Capability Tokens (DCT)** for secure agent coordination:

```python
from kovrin import Kovrin

engine = Kovrin(api_key="sk-ant-...", agents=True)

# Agents receive scoped tokens:
# - Allowed risk levels (e.g., LOW only)
# - Max tasks, max depth
# - Time-to-live
# - Parent token chain (hierarchical delegation)
# Scope can only NARROW, never widen.
```

### Watchdog

Independent safety monitor that subscribes to the trace log:

```python
from kovrin import Kovrin

engine = Kovrin(api_key="sk-ant-...", watchdog=True)

# Watchdog monitors for:
# - Execution after rejection → KILL
# - >50% failure rate → PAUSE
# - Unexpected event sequences → WARN
# - Agent drift (PRM < 0.35) → PAUSE
# Graduated: WARN → PAUSE → KILL (irreversible)
```

## Configuration

```python
from kovrin import Kovrin, AutonomyProfile

engine = Kovrin(
    api_key="sk-ant-...",
    model="claude-sonnet-4-20250514",    # Default model
    autonomy=AutonomyProfile.GUARDED,     # FREE | GUARDED | NONE
    max_concurrent=5,                     # Semaphore limit
    approval_timeout=300,                 # Seconds before timeout
    watchdog=True,                        # Enable watchdog
    agents=True,                          # Enable multi-agent
    explore=False,                        # MCTS exploration
    prm=False,                            # Process Reward Model
)
```

## EU AI Act Compliance

KOVRIN maps directly to EU AI Act requirements:

| EU AI Act Article | KOVRIN Feature |
|---|---|
| Article 12 (Record-keeping) | Merkle hash chain audit trail |
| Article 14 (Human oversight) | Risk-based routing + human-in-the-loop |
| Article 15 (Accuracy & robustness) | Formal verification (TLA+) + critic pipeline |
| Article 9 (Risk management) | Constitutional constraints + watchdog |

## Documentation

- **[Getting Started](https://docs.kovrin.dev/getting-started)** — 5-minute quickstart
- **[Architecture](https://docs.kovrin.dev/concepts/architecture)** — Deep dive into internals
- **[API Reference](https://docs.kovrin.dev/api)** — Full API documentation
- **[Compliance Guide](https://docs.kovrin.dev/guides/compliance)** — EU AI Act mapping

## Contributing

We welcome contributions! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

```bash
git clone https://github.com/digital-specialists/kovrin.git
cd kovrin
pip install -e ".[dev]"
pytest
```

## License

MIT — see [LICENSE](LICENSE) for details.

## Links

- **Website**: [kovrin.ai](https://kovrin.ai)
- **Documentation**: [docs.kovrin.dev](https://docs.kovrin.dev)
- **GitHub**: [github.com/digital-specialists/kovrin](https://github.com/digital-specialists/kovrin)
- **Discord**: [discord.gg/kovrin](https://discord.gg/kovrin)
- **PyPI**: [pypi.org/project/kovrin](https://pypi.org/project/kovrin)
