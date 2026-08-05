# docs/Codex — startup prompts for the Mac body

Ready-to-paste prompts the owner drops into Codex at the start of a session. Nothing here is
executed automatically; a prompt is a shortcut for the owner's hands, not a channel contract.

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

A prompt is a **pointer**, not the work order:

- one line naming the task file to read (`docs/CODEX_TASK_<date>*.md`);
- which task to start with, and why that one first;
- a reminder that the standing constraints still apply;
- the per-action rule: show the owner what will be written before writing it.

The actual assignments — the numbered tasks, the prohibitions, the deliverables — live in
`docs/CODEX_TASK_<date>*.md`. Keeping them apart means the long text can be revised without
re-copying anything into the chat, and the chat message stays short enough to read.

## Why a pointer rather than the full text

The heads read the repository directly. Pasting a long brief into chat duplicates it: the chat
copy then drifts from the repo copy, and nobody knows which one the executor actually followed.
Same reason the arsenal deck and Proshka's mandates are fetched from the repo instead of being
pasted (thin UI, fat repo).

## Related

- `docs/CODEX_TASK_*.md` — the assignments themselves
- `docs/CODEX_HOME_HANDOFF_2026-08-05.md` — the earlier owner→Codex handoff
- `docs/CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md` — how the Codex loop actually runs
  (§5 still holds the five Mac-only GAPS)
- `AGENTS.md` — Codex's standing rules; `CLAUDE.md` — the Linux body's
