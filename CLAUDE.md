# Q3 Claude executor bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`.

Read it completely, then enter through `SESSION_ENTRY.md`. This file is a thin
pointer only and contains no independent executor policy. If the canonical
control is unavailable, ambiguous, non-`ACTIVE`, or fails strict Spine
validation, stop with `CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`.

Linux-body hand-off and repository-map references:

- `docs/Codex/README.md`
- `docs/Codex/TASK_2026-08-06_07.md`
- `specs_docs/ENTRY_SPEC.md`
- `specs_docs/TOOLS_SPEC.md`

The linked documents carry the mechanics and current work order; this bootstrap
remains a pointer and does not duplicate them.
