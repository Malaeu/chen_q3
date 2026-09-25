# Q3 Codex bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`. Plain mode (owner instruction
2026-09-25, ranks above the control per its §1): `git pull` → `docs/Codex/NEXT.md` →
work; `plan` is optional advice, never a gate.

If the control is missing, unreadable, non-`ACTIVE`, or duplicated, stop with:

`CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`

This file is a thin bootstrap pointer. It contains no independent executor
policy, and machine-local configuration cannot override the canonical control; the Owner's explicit instruction can.
Runtime validation (`plan`, optional in plain mode) is described in `SESSION_ENTRY.md`.


# Codex project instructions

For complex coding tasks, use the `astra-orchestrator` skill when its trigger conditions match.

The root agent owns architecture, decomposition, integration, and final verification.
Prefer specialized subagents for bounded exploration, implementation, testing, review, and technical research.

Do not delegate trivial work merely for parallelism.
Do not let multiple implementation agents edit the same files without explicit ownership boundaries.
User instructions always take precedence over this orchestration policy.
