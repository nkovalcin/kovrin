# Security Policy

## Reporting a Vulnerability

If you discover a security vulnerability in Kovrin, please report it responsibly.

**Email**: norbert@nkovalcin.com

Please include:
- Description of the vulnerability
- Steps to reproduce
- Potential impact
- Suggested fix (if any)

We will acknowledge your report within 48 hours and provide a detailed response within 7 days.

## Supported Versions

| Version | Supported |
|---------|-----------|
| 2.0.x   | Yes       |
| < 2.0   | No        |

## Security Model

Kovrin's security architecture is documented in [ARCHITECTURE.md](docs/ARCHITECTURE.md). Key security boundaries:

- **Constitutional Core**: SHA-256 integrity-checked axioms, immutable at runtime
- **Merkle Audit Trail**: Append-only, tamper-evident hash chain
- **Risk Routing**: CRITICAL risk level always requires human approval (hardcoded, no override)
- **DCT Tokens**: HMAC-SHA256 signed, scope can only narrow
- **Watchdog**: Independent observer with irreversible containment (KILL cannot be downgraded)

## Trust Boundaries

| Zone | Trust Level | Examples |
|------|------------|---------|
| Constitutional Core, Risk Router, Trace Log | Trusted | Immutable, verified components |
| Claude API responses, agent outputs | Semi-trusted | Validated through critic pipeline |
| User input, external data | Untrusted | Always processed through safety pipeline |

## Known Limitations

- Alpha release: review before deploying in regulated environments
- Constitutional Core axiom evaluation uses Claude API (inherits Anthropic's security model)
- SQLite storage is not suitable for production persistence (planned: EventStoreDB)
- API server does not include authentication (must be deployed behind a reverse proxy with auth)

## Disclosure Policy

We follow coordinated disclosure. Please do not file public GitHub issues for security vulnerabilities. Use the email above for private reporting.
