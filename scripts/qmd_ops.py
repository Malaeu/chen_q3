#!/usr/bin/env python3
from __future__ import annotations

import contextlib
import fcntl
import os
import shutil
import subprocess
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
Q3_ROOT = REPO_ROOT / "q3.lean.aristotle"
CACHE_ROOT = Q3_ROOT / ".qmd_cache"
LOCK_PATH = CACHE_ROOT / "qmd_ops.lock"
BUSY_MARKERS = (
    "SQLITE_BUSY",
    "SQLITE_BUSY_RECOVERY",
    "database is locked",
)
TRANSIENT_RUNTIME_MARKER_GROUPS = (
    ("Attempted to call a non-GC-safe function inside a NAPI finalizer", "Bun has crashed"),
)


def _busy_output(text: str) -> bool:
    return any(marker in text for marker in BUSY_MARKERS)


def _transient_runtime_output(text: str) -> bool:
    return any(
        all(marker in text for marker in marker_group)
        for marker_group in TRANSIENT_RUNTIME_MARKER_GROUPS
    )


@contextlib.contextmanager
def qmd_lock(label: str, timeout_s: float = 300.0, poll_s: float = 0.2):
    CACHE_ROOT.mkdir(parents=True, exist_ok=True)
    with LOCK_PATH.open("a+", encoding="utf-8") as handle:
        deadline = time.monotonic() + timeout_s
        while True:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    raise TimeoutError(
                        f"timed out waiting for qmd lock at {LOCK_PATH} for {label}"
                    )
                time.sleep(poll_s)

        handle.seek(0)
        handle.truncate()
        handle.write(
            f"pid={os.getpid()}\nlabel={label}\nacquired_at={time.strftime('%Y-%m-%dT%H:%M:%S%z')}\n"
        )
        handle.flush()
        os.fsync(handle.fileno())
        try:
            yield
        finally:
            handle.seek(0)
            handle.truncate()
            handle.flush()
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def run_qmd(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    retries: int = 4,
    base_delay_s: float = 0.5,
    timeout_s: float = 90.0,
) -> str:
    last_output = ""
    for attempt in range(retries + 1):
        try:
            proc = subprocess.run(
                cmd,
                cwd=cwd,
                capture_output=True,
                text=True,
                check=False,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired:
            last_output = (
                f"qmd command timed out after {timeout_s:.0f}s: {' '.join(cmd)}"
            )
            if attempt >= retries:
                raise RuntimeError(last_output)
            time.sleep(base_delay_s * (2**attempt))
            continue
        output = (proc.stderr or "").strip() or (proc.stdout or "").strip()
        if proc.returncode == 0:
            return proc.stdout
        last_output = output
        if not (_busy_output(output) or _transient_runtime_output(output)) or attempt >= retries:
            raise RuntimeError(output)
        time.sleep(base_delay_s * (2**attempt))
    raise RuntimeError(last_output)


def cleanup_stale_stage_dirs(
    cache_root: Path,
    *,
    prefix: str = "q3_docs_stage",
    max_age_s: float = 60 * 60,
) -> list[Path]:
    if not cache_root.exists():
        return []
    now = time.time()
    removed: list[Path] = []
    for path in cache_root.iterdir():
        if not path.is_dir() or not path.name.startswith(prefix):
            continue
        try:
            age_s = now - path.stat().st_mtime
        except FileNotFoundError:
            continue
        if age_s <= max_age_s:
            continue
        shutil.rmtree(path, ignore_errors=True)
        removed.append(path)
    return removed
