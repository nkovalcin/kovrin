# Contributing to KOVRIN

Thank you for your interest in contributing to KOVRIN! This document provides guidelines for contributing to the project.

## Getting Started

```bash
git clone https://github.com/nkovalcin/kovrin.git
cd kovrin
python -m venv .venv
source .venv/bin/activate
pip install -e ".[dev,api]"
```

## Development Workflow

1. **Fork** the repository
2. **Create a branch** from `main`: `git checkout -b feat/your-feature`
3. **Make your changes**
4. **Run tests**: `pytest tests/ -v`
5. **Run linting**: `ruff check src/ tests/`
6. **Run formatting**: `ruff format src/ tests/`
7. **Submit a PR** against `main`

## Branch Naming

- `feat/description` — New features
- `fix/description` — Bug fixes
- `docs/description` — Documentation
- `test/description` — Test additions
- `refactor/description` — Code refactoring

## Commit Messages

We use [Conventional Commits](https://www.conventionalcommits.org/):

```
feat: add beam search pruning strategy
fix: merkle chain verification on empty log
docs: update quickstart guide
test: add adversarial tests for DCT scope escalation
refactor: extract critic pipeline into separate module
```

## Testing

```bash
# All tests
pytest tests/ -v

# Adversarial tests only
pytest -m adversarial -v

# Without Claude API calls
pytest -m "not integration" -v

# Single test file
pytest tests/test_risk_router.py -v
```

All PRs must pass the full test suite. New features must include tests.

## Code Style

- **Python 3.12+**
- **Formatter**: `ruff format` (line length 100)
- **Linter**: `ruff check`
- **Type hints**: Required on all public functions
- **Docstrings**: Google style on all public classes and methods

```python
def validate_task(
    self,
    task: SubTask,
    constraints: list[str],
) -> tuple[bool, list[ProofObligation]]:
    """Validate a task against constitutional constraints.

    Args:
        task: The subtask to validate.
        constraints: User-provided constraints.

    Returns:
        Tuple of (passed, proof_obligations).
    """
```

## Safety Invariants

These invariants **must never be violated**. Any PR that breaks them will be rejected:

1. **Constitutional Core is immutable at runtime.** SHA-256 integrity check on every critic pipeline run.
2. **CRITICAL risk level always routes to HUMAN_APPROVAL.** No override, no profile, no configuration changes this.
3. **Merkle chain is append-only.** `ImmutableTraceLog` never deletes, never modifies.
4. **Scope can only narrow, never widen.** DCT child tokens must have equal or narrower scope than parent.
5. **Watchdog containment is irreversible.** KILL cannot be downgraded. PAUSE cannot be downgraded.
6. **Rejected tasks are never executed.** If critic pipeline returns REJECT, the task must not reach TaskExecutor.

## PR Guidelines

- **Max 400 lines** (excluding tests). Larger changes should be split.
- **Include tests** for new functionality.
- **Update docstrings** if you change public API.
- **Do not commit**: `.env`, `kovrin.db`, `__pycache__/`, API keys.

## Architecture

Before making significant changes, please read:
- `docs/ARCHITECTURE.md` — Technical deep dive
- `CLAUDE.md` — Project conventions and component boundaries

## Questions?

Open a [GitHub Issue](https://github.com/nkovalcin/kovrin/issues) or start a [Discussion](https://github.com/nkovalcin/kovrin/discussions).
