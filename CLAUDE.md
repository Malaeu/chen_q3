# Q3 Claude executor bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`.

Read it completely, then enter through `SESSION_ENTRY.md`. This file is a thin
pointer only and contains no independent executor policy. If the canonical
control is unavailable, ambiguous, non-`ACTIVE`, or fails strict Spine
validation, stop with `CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`.

---

## Linux body — working rules (not executor policy)

Addressed to Claude Code on Linux. Behaviour policy stays in `docs/CODEX_CONTROL.md`;
these are hand-off mechanics, kept here because they concern this body only.

**Codex hand-off: ONE file per evening.** When work must run through Codex at home, do not
scatter instructions across chat messages. Collect **every** task into a single file:

```
docs/Codex/TASK_<YYYY-MM-DD>_<slot>.md      the work order, executed step by step
docs/Codex/PROMPT_<YYYY-MM-DD>_<slot>.md    the one-line prompt pointing at it
```

Each task in that file carries: what to do, **why** (which pain point it closes), and a link
to the documentation that explains the tool or the decision. A task without a stated pain
point does not go into the file.

Rationale: the owner is at the machine in the evening with limited time; reconstructing the
task list from chat costs more than the task. Naming and the pointer-not-payload convention:
`docs/Codex/README.md`.

**Where the repo's own map lives:** `specs_docs/` — entry order (`ENTRY_SPEC.md`), tool
specs and the operational catalogue (`TOOLS_SPEC.md`), contour consolidation, what was
deliberately not migrated.
