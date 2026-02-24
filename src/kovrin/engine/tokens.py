"""
Kovrin Delegation Capability Tokens (DCT)

Cryptographically signed tokens with minimum-privilege scoping
for multi-agent delegation. Each token:
- Is HMAC-SHA256 signed
- Has a bounded scope (risk levels, actions, capabilities)
- Can issue sub-tokens with equal or narrower scope
- Tracks execution count against max_tasks
- Can be revoked (cascading to children)
"""

import hashlib
import hmac
import os
from datetime import UTC, datetime, timedelta

from kovrin.core.models import (
    DelegationScope,
    DelegationToken,
    SubTask,
    Trace,
)


class ScopeViolationError(Exception):
    """Raised when a child token requests a wider scope than its parent."""


class TokenAuthority:
    """Issues, validates, and revokes delegation capability tokens."""

    def __init__(self, secret_key: str | None = None):
        """Initialize with a signing key.

        Args:
            secret_key: HMAC secret. If None, generated randomly (ephemeral).
        """
        self._secret = (secret_key or os.urandom(32).hex()).encode()
        self._tokens: dict[str, DelegationToken] = {}  # id -> token
        self._children: dict[str, list[str]] = {}  # parent_id -> [child_ids]

    @property
    def active_tokens(self) -> list[DelegationToken]:
        """Return all non-revoked, non-expired tokens."""
        now = datetime.now(UTC)
        return [t for t in self._tokens.values() if not t.revoked and t.expires_at > now]

    def issue(
        self,
        agent_id: str,
        scope: DelegationScope | None = None,
        ttl_seconds: int = 300,
        parent_token_id: str | None = None,
    ) -> DelegationToken:
        """Issue a new delegation token.

        Args:
            agent_id: The agent receiving the token.
            scope: The capability scope. If None, uses default.
            ttl_seconds: Time-to-live in seconds.
            parent_token_id: If set, the new token is a sub-delegation.

        Returns:
            A signed DelegationToken.

        Raises:
            ScopeViolationError: If child scope exceeds parent scope.
        """
        scope = scope or DelegationScope()
        now = datetime.now(UTC)

        # Enforce scope narrowing for sub-tokens
        if parent_token_id:
            parent = self._tokens.get(parent_token_id)
            if parent:
                self._enforce_scope_narrowing(parent.scope, scope)

        token = DelegationToken(
            agent_id=agent_id,
            scope=scope,
            issued_at=now,
            expires_at=now + timedelta(seconds=ttl_seconds),
            parent_token_id=parent_token_id,
        )

        # Sign
        token.signature = self._sign(token)

        # Store
        self._tokens[token.id] = token
        if parent_token_id:
            self._children.setdefault(parent_token_id, []).append(token.id)

        return token

    def validate(self, token: DelegationToken) -> tuple[bool, str]:
        """Validate a token's signature, expiry, and revocation status.

        Returns:
            (valid, reason) tuple.
        """
        # Check revocation
        if token.revoked:
            return False, "Token has been revoked"

        # Check expiry
        now = datetime.now(UTC)
        if token.expires_at <= now:
            return False, "Token has expired"

        # Check signature
        expected = self._sign(token)
        if not hmac.compare_digest(token.signature, expected):
            return False, "Invalid signature"

        # Check if stored (known token)
        stored = self._tokens.get(token.id)
        if stored and stored.revoked:
            return False, "Token revoked in authority registry"

        return True, "Valid"

    def check_scope(self, token: DelegationToken, subtask: SubTask) -> tuple[bool, str]:
        """Check if a token's scope allows executing the given task.

        Returns:
            (allowed, reason) tuple.
        """
        # Check risk level
        if subtask.risk_level not in token.scope.allowed_risk_levels:
            return False, f"Risk level {subtask.risk_level.value} not in token scope"

        # Check max_tasks
        if token.tasks_executed >= token.scope.max_tasks:
            return False, f"Max tasks exceeded ({token.tasks_executed}/{token.scope.max_tasks})"

        return True, "Scope check passed"

    def revoke(self, token_id: str) -> int:
        """Revoke a token and all its children (cascade).

        Returns:
            Number of tokens revoked.
        """
        count = 0
        token = self._tokens.get(token_id)
        if token and not token.revoked:
            token.revoked = True
            count += 1

        # Cascade to children
        for child_id in self._children.get(token_id, []):
            count += self.revoke(child_id)

        return count

    def record_execution(self, token: DelegationToken) -> None:
        """Increment the execution counter for a token."""
        token.tasks_executed += 1
        stored = self._tokens.get(token.id)
        if stored:
            stored.tasks_executed = token.tasks_executed

    def _sign(self, token: DelegationToken) -> str:
        """Compute HMAC-SHA256 signature for a token."""
        payload = f"{token.id}:{token.agent_id}:{token.issued_at.isoformat()}:{token.expires_at.isoformat()}"
        return hmac.new(self._secret, payload.encode(), hashlib.sha256).hexdigest()

    @staticmethod
    def _enforce_scope_narrowing(parent: DelegationScope, child: DelegationScope) -> None:
        """Ensure child scope is equal or narrower than parent scope.

        Raises:
            ScopeViolationError: If child scope exceeds parent.
        """
        # Risk levels must be subset
        parent_risks = set(parent.allowed_risk_levels)
        child_risks = set(child.allowed_risk_levels)
        if not child_risks.issubset(parent_risks):
            extra = child_risks - parent_risks
            raise ScopeViolationError(f"Child risk levels {extra} exceed parent scope")

        # Actions must be subset
        parent_actions = set(parent.allowed_actions)
        child_actions = set(child.allowed_actions)
        if not child_actions.issubset(parent_actions):
            extra = child_actions - parent_actions
            raise ScopeViolationError(f"Child actions {extra} exceed parent scope")

        # max_tasks must be <=
        if child.max_tasks > parent.max_tasks:
            raise ScopeViolationError(
                f"Child max_tasks ({child.max_tasks}) exceeds parent ({parent.max_tasks})"
            )

        # max_depth must be <=
        if child.max_depth > parent.max_depth:
            raise ScopeViolationError(
                f"Child max_depth ({child.max_depth}) exceeds parent ({parent.max_depth})"
            )

    @staticmethod
    def create_trace(token: DelegationToken, event: str, intent_id: str) -> Trace:
        """Create a TOKEN_* trace event."""
        return Trace(
            intent_id=intent_id,
            event_type=f"TOKEN_{event.upper()}",
            description=f"DCT {event}: agent={token.agent_id} scope={len(token.scope.allowed_risk_levels)} risk levels",
            details={
                "token_id": token.id,
                "agent_id": token.agent_id,
                "parent_token_id": token.parent_token_id,
                "expires_at": token.expires_at.isoformat(),
                "tasks_executed": token.tasks_executed,
                "max_tasks": token.scope.max_tasks,
                "revoked": token.revoked,
            },
        )
