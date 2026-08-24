# Codex current task pointer

```yaml
schema: q3_codex_current_task.v1
status: ACTIVE
task_file: docs/Codex/TASK_2026-08-24_selected_ferrers_abel_poisson_l2.md
source_commit: 1c31b8115aba2cb90c4cc5886a9621410b8dc12f
updated_at: 2026-08-24T08:38:05+02:00
updated_by: CODEX_ON_OWNER_INSTRUCTION
```

This is the single owner-controlled repository pointer for work that Codex must
discover after a pull without a long chat paste.

- `ACTIVE` requires a tracked `docs/Codex/TASK_*.md` path and the full source
  commit that introduced or last revised the instruction.
- `EMPTY` and `CLOSED` select no work.
- The pointer cannot override the owner's current instruction, physical task
  state, Route B boundaries, or `docs/CODEX_CONTROL.md`.
- Claude Code may prepare the task file as the independent observer, but the
  owner controls whether this pointer becomes `ACTIVE`.
