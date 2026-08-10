# docs/Codex — startup prompts for the Mac body

Owner-visible task handoffs for the Mac Codex body. `CURRENT.md` is the only
startup-readable pointer; the dated prompt files remain optional shortcuts for
the owner's hands.

## Automatic pointer

`CURRENT.md` is read and validated at every Codex startup. `status: ACTIVE`
requires a tracked `docs/Codex/TASK_*.md` plus its full `source_commit`.
`EMPTY` and `CLOSED` select nothing. The pointer carries an assignment across a
pull; it never overrides the owner's current instruction or physical task state.

## Naming

```
PROMPT_<YYYY-MM-DD>[_<slot>].md      e.g. PROMPT_2026-08-05_evening.md
```

Date first so the directory sorts chronologically; `slot` only when there is more than one
prompt in a day (`morning` / `evening` / a short topic like `g2fork`).

Do **not** let the filename come from the first line of the text — the first file here was born
as `Прочитай docsCODEX_TASK_2026-08-05_EVENING.md`, which git has to escape and GitHub turns
into a `%D0%9F%D1%80…` URL.

## What belongs in a prompt file

A pasted prompt is an optional **pointer**, not the work order:

- one line naming the task file to read (`docs/Codex/TASK_<date>_<slot>.md`);
- which task to start with, and why that one first;
- a reminder that the standing constraints still apply;
- the active goal scope and any operational boundary not covered by it.

The actual assignments — the numbered tasks, the prohibitions, the deliverables — live in
`docs/Codex/TASK_<date>_<slot>.md`. Keeping them apart means the long text can be revised without
re-copying anything into the chat, and the chat message stays short enough to read.

## Why a pointer rather than the full text

The heads read the repository directly. Pasting a long brief into chat duplicates it: the chat
copy then drifts from the repo copy, and nobody knows which one the executor actually followed.
Same reason the arsenal deck and Proshka's mandates are fetched from the repo instead of being
pasted (thin UI, fat repo).

## Related

- `docs/Codex/CURRENT.md` — the single startup-readable task pointer
- `docs/Codex/TASK_*.md` — the assignments themselves
- `docs/CODEX_HOME_HANDOFF_2026-08-05.md` — the earlier owner→Codex handoff
- `docs/CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md` — how the Codex loop actually runs
  (§5 still holds the five Mac-only GAPS)
- `AGENTS.md` — Codex's standing rules; `CLAUDE.md` — the Linux body's
