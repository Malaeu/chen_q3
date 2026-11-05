# Q3 Codex bootstrap

Canonical executor behavior: `docs/CODEX_CONTROL.md`. Plain mode (owner instruction
2026-09-25, ranks above the control per its §1): `git pull` → `docs/Codex/NEXT.md` →
work; `plan` is optional advice, never a gate. Working rules in NEXT.md «Правила работы»
override `~/.codex/AGENTS.md` §§3, 5, 6, 9 for this repository (owner, 2026-09-28).

If the control is missing, unreadable, non-`ACTIVE`, or duplicated, stop with:

`CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS`

This file is a thin bootstrap pointer. It contains no independent executor
policy except the owner rule «Сохранность результатов» below; machine-local configuration cannot override the control, the Owner's explicit instruction can.

## Сохранность результатов (владелец, 2026-11-05)

Любой результат — код, данные, вердикт, лог счёта — коммитится и пушится в
https://github.com/Malaeu/chen_q3: в ветку `rh_clean` или в ветку `codex/<имя>`.
Ничего не оставлять только в облачном воркспейсе. Задача не выполнена, пока в ответе
нет hash запушенного коммита. Если у среды нет доступа на запись в chen_q3 — сказать
об этом первой строкой ответа, а не работать в другом репо.

# Codex project instructions

For complex coding tasks, use the `astra-orchestrator` skill when its trigger conditions match.

The root agent owns architecture, decomposition, integration, and final verification.
Prefer specialized subagents for bounded exploration, implementation, testing, review, and technical research.

Do not delegate trivial work merely for parallelism.
Do not let multiple implementation agents edit the same files without explicit ownership boundaries.
User instructions always take precedence over this orchestration policy.
