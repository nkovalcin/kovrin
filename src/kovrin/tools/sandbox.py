"""
Kovrin Controlled Execution Environment

Provides advisory-gated execution for tool code:
- Timeout enforcement via asyncio.wait_for + process kill
- Code execution in subprocess with clean environment (stripped env vars)
- Output size limits (configurable max bytes)
- Advisory network domain allowlisting (pre-flight check, not enforced at OS level)
- Advisory filesystem path validation (pre-flight check, not chroot)

Note: This is NOT a true sandbox — the subprocess runs as the same user
with full filesystem and network access. The controls are advisory.
For true isolation, a future version should use setrlimit, Docker, or
seccomp-bpf. See: https://github.com/kovrin-dev/kovrin/issues/TBD
"""

from __future__ import annotations

import asyncio
import os
import tempfile
from pathlib import Path

from pydantic import BaseModel, Field


class SandboxConfig(BaseModel):
    """Configuration for sandboxed tool execution."""

    timeout_seconds: float = Field(default=30.0, ge=1.0, le=300.0)
    max_output_bytes: int = Field(default=65536, ge=1024, le=1048576)
    network_allowed: bool = False
    allowed_domains: list[str] = Field(default_factory=list)
    filesystem_root: str | None = None
    allow_imports: bool = True


# Default sandbox configs per risk level
SANDBOX_DEFAULTS = {
    "LOW": SandboxConfig(timeout_seconds=10.0, network_allowed=True),
    "MEDIUM": SandboxConfig(timeout_seconds=20.0, network_allowed=True),
    "HIGH": SandboxConfig(timeout_seconds=30.0, network_allowed=False),
    "CRITICAL": SandboxConfig(timeout_seconds=10.0, network_allowed=False),
}


class SandboxedExecutor:
    """Executes tools in a controlled environment with timeout enforcement.

    Provides: timeout (kill on exceed), clean env vars, output size caps,
    advisory path/domain validation. Does NOT provide: OS-level isolation,
    resource limits (memory/CPU), or network firewalling.
    """

    def __init__(self, config: SandboxConfig | None = None):
        self._config = config or SandboxConfig()

    async def execute_code(self, code: str, config: SandboxConfig | None = None) -> str:
        """Execute Python code in a sandboxed subprocess.

        The code runs in a separate process with:
        - Timeout enforcement
        - Output size limits
        - No access to parent process environment

        Returns the stdout output or error message.
        """
        cfg = config or self._config

        # Write code to temp file
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".py", delete=False, prefix="kovrin_sandbox_"
        ) as f:
            f.write(code)
            tmp_path = f.name

        try:
            # Build subprocess with clean environment
            env = {
                "PATH": "/usr/bin:/usr/local/bin:/bin",
                "HOME": tempfile.gettempdir(),
                "LANG": "en_US.UTF-8",
            }

            # If filesystem_root is set, change working directory
            cwd = cfg.filesystem_root if cfg.filesystem_root else tempfile.gettempdir()

            proc = await asyncio.create_subprocess_exec(
                "python3",
                tmp_path,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                env=env,
                cwd=cwd,
            )

            try:
                stdout, stderr = await asyncio.wait_for(
                    proc.communicate(),
                    timeout=cfg.timeout_seconds,
                )
            except TimeoutError:
                proc.kill()
                await proc.wait()
                return f"[TIMEOUT] Code execution exceeded {cfg.timeout_seconds}s limit"

            # Enforce output size limit
            output = stdout.decode("utf-8", errors="replace")
            if len(output) > cfg.max_output_bytes:
                output = (
                    output[: cfg.max_output_bytes]
                    + f"\n[TRUNCATED at {cfg.max_output_bytes} bytes]"
                )

            if proc.returncode != 0:
                error = stderr.decode("utf-8", errors="replace")
                if len(error) > cfg.max_output_bytes:
                    error = error[: cfg.max_output_bytes]
                return f"[ERROR exit={proc.returncode}]\n{error}"

            return output

        finally:
            # Clean up temp file
            try:
                os.unlink(tmp_path)
            except OSError:
                pass

    def validate_path(self, path: str, config: SandboxConfig | None = None) -> tuple[bool, str]:
        """Validate a filesystem path against sandbox restrictions.

        Returns (is_valid, reason).
        """
        cfg = config or self._config

        resolved = Path(path).resolve()

        # Block sensitive system paths
        blocked_prefixes = ["/etc", "/var", "/usr", "/bin", "/sbin", "/boot", "/proc", "/sys"]
        for prefix in blocked_prefixes:
            if str(resolved).startswith(prefix):
                return False, f"Access to {prefix} is blocked by sandbox policy"

        # If filesystem_root is set, enforce chroot-like restriction
        if cfg.filesystem_root:
            root = Path(cfg.filesystem_root).resolve()
            if not str(resolved).startswith(str(root)):
                return False, f"Path {resolved} is outside sandbox root {root}"

        return True, "Path is within allowed boundaries"

    def validate_domain(self, url: str, config: SandboxConfig | None = None) -> tuple[bool, str]:
        """Validate a URL against the domain allowlist.

        Returns (is_valid, reason).
        """
        cfg = config or self._config

        if not cfg.network_allowed:
            return False, "Network access is disabled in sandbox"

        if not cfg.allowed_domains:
            return True, "No domain restrictions — all domains allowed"

        from urllib.parse import urlparse

        try:
            parsed = urlparse(url)
            domain = parsed.hostname or ""
        except Exception:
            return False, f"Invalid URL: {url}"

        for allowed in cfg.allowed_domains:
            if domain == allowed or domain.endswith(f".{allowed}"):
                return True, f"Domain {domain} is in the allowlist"

        return False, f"Domain {domain} is not in the allowlist: {cfg.allowed_domains}"
