# Sprint Monitor

status: ACTIVE
sprint: Q_zeta_core_short_circuit
started: 2026-03-15
mode: two-lane
mainline: T0-pd -> H-bridge -> H4 -> RH
lane_A: H1 defect calculus
lane_B: PSD-pd finite certificates
current_day: 5
current_lane: B
current_step_id: B1
current_step_title: PSD-pd smallest-block step
current_owner: local-agent
current_artifact: docs/insights/psd_pd_smallest_block_step_2026_03_16.md
last_completed_step_id: A4
last_completed_step_title: H1 proof-obligation table
last_completed_commit: pending current sprint commit
next_deliverable: freeze one explicit admissible finite dictionary J_min and one exact certificate checklist for PSD-pd
next_verify: rg -n -e "J_\\{\\\\min\\}|finite symbol|Poisson|error budget|certificate" q3.lean.aristotle/docs/insights/psd_pd_smallest_block_step_2026_03_16.md
proshka_prompt: q3.lean.aristotle/docs/insights/proshka_q_zeta_core_adapter_prompt_2026_03_15.md
proshka_context: tmp/proshka_q_zeta_core_adapter_context_2026_03_15.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_q_zeta_a2_plus_minus_2026_03_15/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_q_zeta_a2_plus_minus_2026_03_15/report.md

Этот файл — оперативный single source of truth для спринта.

Правило старта новой сессии:

1. открыть `SESSION_ENTRY.md`;
2. сразу открыть `ACTIVE/SPRINT_MONITOR.md`;
3. если `status: ACTIVE`, открыть только `current_artifact`;
4. не читать `PROJECT_ORCHESTRATOR.md`, `IMPLEMENTATION_PLAN.md`,
   `docs/INSIGHTS.md` заново, если `current_artifact` не даёт blocker;
5. продолжать ровно `current_step_id`;
6. не перепридумывать frontier, пока `SPRINT_MONITOR.md` не переведён в
   `DONE`, `BLOCKED` или `ABORTED`.

## Startup response contract

Первое сообщение новой сессии должно быть коротким и operational.

Оно должно содержать только:

1. подтверждение активного спринта;
2. `current_step_id` и `current_step_title`;
3. какой файл открывается сейчас;
4. какой exact output будет добиваться текущим ходом.

Оно не должно:

- пересказывать весь frontier;
- заново перечислять старые route decisions;
- описывать длинный self-sync по 5-10 файлам;
- читать extra docs без blocker.

Template:

```text
Спринт активен: <sprint>, текущий шаг <current_step_id> — <current_step_title>.
Сейчас открываю <current_artifact> и добиваю <next_deliverable>; если blocker
не появится, другие control docs не перечитываю.
```

## Sprint contract

- public route не меняется:
  `T0-pd -> H-bridge -> H4 -> RH`;
- `Q_\zeta`-core не является третьей RH-веткой;
- lane A = `H1` defect calculus;
- lane B = `PSD-pd` finite certificates;
- structural math отдаём Прошке;
- deterministic formula / bookkeeping / obligation work держим локально.

## Hard invariants

Нельзя:

- возвращаться к rank/basis hunt как theorem content;
- оживлять raw identity `w_{rs}(a)=\kappa(a)q_{rs}`;
- идти в augmented cap positivity до symbolic defect classification;
- открывать новую RH-архитектуру вне `H-bridge` и `PSD-pd`;
- терять asymmetry:
  `(+,-)` = first adapter target,
  `(++)` = hard same-sign block.

## Current board

| Step | Lane | Status | Deliverable |
| --- | --- | --- | --- |
| `A1` | `A` | `done` | `docs/insights/plus_minus_adapter_ledger_2026_03_15.md` |
| `A2` | `A` | `done` | `docs/insights/plus_minus_cancellation_ledger_2026_03_15.md` |
| `A3` | `A` | `done` | `docs/insights/plus_plus_boundary_inventory_2026_03_15.md` |
| `A4` | `A` | `done` | `docs/insights/h1_proof_obligation_table_2026_03_16.md` |
| `B1` | `B` | `active (draft started)` | `docs/insights/psd_pd_smallest_block_step_2026_03_16.md` |
| `P1` | `P` | `completed (ingested)` | `ACTIVE/requests/proshka_q_zeta_a2_plus_minus_2026_03_15/node.md` -> `report.md` |

## Current step

### `B1` — PSD-pd smallest-block step

Goal:

- keep lane `B` alive with one smallest explicit finite certificate step;
- freeze one admissible finite dictionary and one exact symbol target;
- avoid letting the fallback route explode into a second free-form project.

Required output:

- one explicit admissible dictionary `J_min`;
- one exact symbol `S_{J_{\min}}(\theta)`;
- one certificate checklist;
- one explicit error-budget route;
- one binary viability verdict.

Exact success criterion:

- after reading the new note, the next theorem attempt is unambiguously
  one explicit finite certificate task rather than “continue PSD-pd somehow”.

## Next after current step

If `B1` lands:

- keep both lane outputs frozen;
- move to the sprint binary decision phase:
  adapter theorem viable versus route needs narrowing.

If `B1` fails:

- do not open a new route;
- mark `B1` as `blocked`;
- write the exact obstruction in `docs/INSIGHTS.md`;
- reduce the target to a weaker corrected theorem or to a named unresolved term.

## Update protocol

After every meaningful sprint move:

1. update this file first:
   `current_day`, `current_step_id`, `last_completed_step_id`,
   `last_completed_commit`, `next_deliverable`;
2. update `IMPLEMENTATION_PLAN.md` only if the active task definition changes;
3. add one short synthesis line to `docs/INSIGHTS.md`;
4. commit;
5. leave the worktree clean.

## Exit states

- `DONE`: sprint outputs all four success criteria from the sprint note.
- `BLOCKED`: one exact obstruction is written and no clean reduced step exists.
- `ABORTED`: architecture changed by explicit control-plane decision.
