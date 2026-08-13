"""Shared lifecycle parsing for physical Route B goal files."""

from __future__ import annotations

import re
from pathlib import Path


STATUS_RE = re.compile(r"^STATUS:\s*([A-Z][A-Z0-9_]*)\s*$", re.MULTILINE)
PAUSED_STATUSES = frozenset({"PAUSED_RESTORABLE"})


def goal_status_text(text: str) -> str | None:
    """Return the first machine ``STATUS`` token in a goal payload."""
    match = STATUS_RE.search(text)
    return match.group(1) if match else None


def goal_status(path: Path) -> str | None:
    return goal_status_text(path.read_text(encoding="utf-8"))


def is_paused_goal(path: Path) -> bool:
    return goal_status(path) in PAUSED_STATUSES
