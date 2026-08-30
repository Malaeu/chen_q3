# Codex current task pointer

```yaml
schema: q3_codex_current_task.v1
status: CLOSED
task_file: docs/Codex/TASK_2026-08-30_goal058_g3_rate_floor_source_rerank.md
source_commit: 7b96eca0121087abdbc69f360d54c703c02fd0c8
updated_at: 2026-08-30T15:32:40+02:00
updated_by: CODEX_SELECTED_FERRERS_EVEN_SECTOR_FLOOR_SOURCE_DISCRIMINATOR
```

This is the single owner-controlled repository pointer for work that Codex must
discover after a pull without a long chat paste.

- `ACTIVE` requires a tracked `docs/Codex/TASK_*.md` path and the full source
  commit that introduced or last revised the instruction.
- `EMPTY` and `CLOSED` select no work.  The completed task file records the
  exact closeout and the next dependency root without authorizing execution.
- The pointer cannot override the owner's current instruction, physical task
  state, Route B boundaries, or `docs/CODEX_CONTROL.md`.
- Claude Code may prepare the task file as the independent observer, but the
  owner controls whether this pointer becomes `ACTIVE`.
