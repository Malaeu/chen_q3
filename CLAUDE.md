# Q3 Claude executor bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`.

Read it completely, then enter through `SESSION_ENTRY.md`. This file is a thin
pointer only and contains no independent executor policy. If the canonical
control is unavailable, ambiguous, non-`ACTIVE`, or fails strict Spine
validation, stop with `CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`.

## Ask the shelf first

Before saying "we do not have this", before an external search, and before creating
anything new: **`./ask.sh <term>`**. One entry point over every store we keep —
`knowledge.db`, the literature review, Lean declarations, the specs. It prints
`НЕ НАЙДЕНО НИГДЕ` with the list of stores it checked when the thing genuinely is not here,
so "we do not have it" becomes a checked statement rather than a guess.

This exists because on 6–7 August the same failure repeated three times in two days: the
instrument existed, the knowledge sat inside it, nobody looked. `H2aPenaltyCoercivity.lean`
was absent from the map; `kb_migrate_verdicts.py` was written and never triggered; a paper
was fetched, filed and flagged in the litreview while we went to search for it on the web.
The cause is not forgetfulness — it is four stores with four different commands, where
asking one and finding nothing reads as "nowhere".

Linux-body hand-off and repository-map references:

- `docs/Codex/README.md`
- `docs/Codex/TASK_2026-08-06_07.md`
- `specs_docs/ENTRY_SPEC.md`
- `specs_docs/TOOLS_SPEC.md`

The linked documents carry the mechanics and current work order; this bootstrap
remains a pointer and does not duplicate them.
