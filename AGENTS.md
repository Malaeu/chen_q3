# Q3 Codex bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`. Entry: `SESSION_ENTRY.md`
(one command, `python3 orchestrator/workflow_runtime.py plan`; the control is
consulted by section when its gate fires, not re-read in full).

If the control is missing, unreadable, non-`ACTIVE`, or duplicated, stop with:

`CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`

This file is a thin bootstrap pointer. It contains no independent executor
policy, and machine-local configuration cannot override the canonical control.
Runtime validation is performed only by the canonical front door named in
`SESSION_ENTRY.md`.
