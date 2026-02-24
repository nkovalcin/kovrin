# KOVRIN — Príkaz pre Claude Code (SuperWork build)

Spusti v projektovom priečinku: `cd ~/Desktop/projects/kovrin`

---

```
claude
```

Potom vlož tento prompt:

---

## PROMPT PRE CLAUDE CODE

```
Prečítaj CLAUDE.md a docs/SUPERWORK.md — tam máš kompletný kontext a architektúru.

Toto je KOVRIN — safety-first AI orchestration framework (480 testov, TLA+ verifikácia, constitutional safety). Teraz budujeme SuperWork vrstvu — supervisor platformu.

PRAVIDLÁ (NIKDY NEPORUŠIŤ):
1. Nemodifikuj src/kovrin/core/constitutional.py — to je Layer 0
2. Nemodifikuj specs/*.tla — TLA+ specs
3. Každý nový modul musí mať testy v tests/
4. Nič nemôže obísť CriticPipeline ani risk routing
5. Virtual env: .venv/bin/python

TASKY V TOMTO PORADÍ:

### TASK 1: TypeScript drift fix
Spusti: .venv/bin/python -m kovrin.schema.exporter --typescript dashboard/src/types/generated.ts
Potom nahraď dashboard/src/types/kovrin.ts obsahom generated.ts.
Over že všetky dashboard komponenty stále kompilujú.

### TASK 2: SuperWork skeleton
Vytvor adresár src/kovrin/superwork/ s týmito súbormi:
- __init__.py
- session_watcher.py — trieda SessionWatcher (watchdog knižnica, sleduje ~/.claude/projects/)
- context_injector.py — trieda ProjectContextDB (ChromaDB, sentence-transformers)
- orchestrator.py — trieda OrchestratorAgent (Opus API, analýza stavu, návrhy)
- metrics.py — trieda VelocityTracker (velocity, cost, predikcia)
- cli.py — Click CLI s príkazom `kovrin superwork --project <path>`

Každý súbor musí mať Google-style docstringy, type hints, a základné unit testy v tests/superwork/.

### TASK 3: Session Watcher (implementuj)
Implement src/kovrin/superwork/session_watcher.py:
- Sleduj ~/.claude/projects/<project-hash>/*.jsonl súbory
- Parsuj JSONL events (type: assistant/tool_use/tool_result)
- Detekuj task completion (keď Claude Code skončí — typicky posledný event je tool_result s exit_code)
- Emituj TaskCompletionEvent dataclass
- Testy: tests/superwork/test_session_watcher.py (mock fs events)

### TASK 4: Context Injector (implementuj)
Implement src/kovrin/superwork/context_injector.py:
- ChromaDB PersistentClient do .kovrin/context_db/ v project path
- index_project(path) — prechádzaj *.py, *.ts, *.md, *.tsx, chunk po funkciách/sekciách
- get_relevant_context(task, max_chunks=10) — vrať string s relevantnými chunks
- update_on_change(changed_files) — re-indexuj len zmenené súbory
- Embeddings: sentence-transformers/all-MiniLM-L6-v2 (malý, rýchly, lokálny)
- Testy: tests/superwork/test_context_injector.py

### TASK 5: Orchestrator Agent (implementuj)
Implement src/kovrin/superwork/orchestrator.py:
- OrchestratorAgent prijíma TaskCompletionEvent a analyzuje stav
- Používa claude-opus-4-20250514 pre hlbokú analýzu
- Vracia list[TaskProposal] — každý má: title, description, rationale, estimated_tokens, risk_level, auto_execute
- Výsledky serializuje do .kovrin/proposals.json pre dashboard
- Testy: tests/superwork/test_orchestrator.py (mock Claude API)

### TASK 6: FastAPI SuperWork routes
Vytvor src/kovrin/api/superwork_router.py:
- GET /api/status — stav agentov (z .kovrin/state.json)
- GET /api/proposals — čakajúce návrhy
- POST /api/proposals/{id}/approve — schváli + spustí cez Kovrin engine
- POST /api/proposals/{id}/skip — preskočiť
- POST /api/agents/{id}/pause — pauza
- WS /ws/live — WebSocket stream (emituje eventy z ImmutableTraceLog)
Zaregistruj router v src/kovrin/api/server.py.

### TASK 7: Dashboard SuperWork komponenty
V dashboard/src/components/ vytvor:
- AgentTree.tsx — stromový view orchestrator + executori s live statusom
- ProposalCard.tsx — karta návrhu s Approve/Skip tlačidlami
- MetricsBar.tsx — tasks/tokens/cost/velocity v jednom riadku
- PredictionBar.tsx — progress bar + "MVP ready in X days"
- LiveFeed.tsx — WebSocket hook + scrollovateľný event log
Použiť: Tailwind, shadcn/ui (0 border-radius), JetBrains Mono, dark mode (#0A0A0B bg, #10B981 primary)

### TASK 8: pyproject.toml update
Pridaj optional dependencies:
[project.optional-dependencies]
superwork = ["watchdog>=4.0", "chromadb>=0.5", "sentence-transformers>=3.0", "rich>=13.0", "click>=8.0"]
Uprav aj README.md — pridaj sekciu SuperWork quickstart.

### TASK 9: Všetky testy
Spusti: .venv/bin/python -m pytest tests/ -v
Všetky musia prejsť. Ak niečo padá, oprav to.
Potom spusti adversarial testy: .venv/bin/python -m pytest tests/ -m adversarial -v

### TASK 10: README update
Aktualizuj README.md:
- Pridaj SuperWork sekciu (čo to je, quickstart)
- Aktualizuj architektúrový diagram
- Pridaj CLI dokumentáciu
- Over že všetky príklady v README fungujú

Po každom tasku:
- Commitni: git add -A && git commit -m "feat: <čo si urobil>"
- Spusti testy
- Reportuj čo si urobil a čo bude ďalej
```

---

## Ako spustiť

```bash
# V termináli
cd ~/Desktop/projects/kovrin

# Ak nemáš Claude Code nainštalovaný:
npm install -g @anthropic-ai/claude-code

# Spusti
claude

# Vlož prompt vyššie
# Alebo pre jednotlivé tasky:
claude -p "Prečítaj CLAUDE.md. TASK 1: TypeScript drift fix. Spusti schema exporter a nahraď kovrin.ts."
```

## Poznámky

- Claude Code pracuje v `.venv` — vždy používa `.venv/bin/python`
- Session files sa ukladajú do `~/.claude/projects/<hash>/` — toto je základ Session Watchera
- `kovrin.db` je lokálna SQLite, neinkomitovať
- Pri problémoch s importmi: `pip install -e ".[dev,api,superwork]" --break-system-packages`
