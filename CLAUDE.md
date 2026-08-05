# Q3 Claude executor bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`.

Read it completely, then enter through `SESSION_ENTRY.md`. This file is a thin
pointer only and contains no independent executor policy. If the canonical
control is unavailable, ambiguous, non-`ACTIVE`, or fails strict Spine
validation, stop with `CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`.
