# Codex current task pointer

```yaml
schema: q3_codex_current_task.v1
status: ACTIVE
task_file: docs/Codex/TASK_2026-08-30_goal058_g3_rate_floor_source_rerank.md
source_commit: 0a0e57e12c5ce13df5583d08e013343fc3ce5d30
updated_at: 2026-08-30T13:15:31+02:00
updated_by: CODEX_G3_SATZ9_UNIFORM_ASYMPTOTIC_LIBRARY_WALL
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
