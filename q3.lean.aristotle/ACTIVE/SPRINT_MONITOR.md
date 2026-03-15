# Sprint Monitor

status: ACTIVE
sprint: Q_zeta_core_short_circuit
started: 2026-03-15
mode: two-lane
mainline: T0-pd -> H-bridge -> H4 -> RH
lane_A: H1 defect calculus
lane_B: PSD-pd finite certificates
current_day: 2
current_lane: A
current_step_id: A2
current_step_title: plus-minus cancellation ledger
current_owner: local-agent
current_artifact: docs/insights/plus_minus_cancellation_ledger_2026_03_15.md
last_completed_step_id: A1
last_completed_step_title: plus-minus adapter ledger
last_completed_commit: 10d23998
next_deliverable: refine the exact vanishing/surviving table inside docs/insights/plus_minus_cancellation_ledger_2026_03_15.md
next_verify: rg -n -e "\\(\\+,-\\).*cancellation" -e "vanish|survive|cap|boundary" q3.lean.aristotle/docs/insights/plus_minus_cancellation_ledger_2026_03_15.md
proshka_prompt: q3.lean.aristotle/docs/insights/proshka_q_zeta_core_adapter_prompt_2026_03_15.md
proshka_context: tmp/proshka_q_zeta_core_adapter_context_2026_03_15.md

Этот файл — оперативный single source of truth для спринта.

Правило старта новой сессии:

1. открыть `SESSION_ENTRY.md`;
2. сразу открыть `ACTIVE/SPRINT_MONITOR.md`;
3. если `status: ACTIVE`, продолжать ровно `current_step_id`;
4. не перепридумывать frontier, пока `SPRINT_MONITOR.md` не переведён в
   `DONE`, `BLOCKED` или `ABORTED`.

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
| `A2` | `A` | `active (draft started)` | `docs/insights/plus_minus_cancellation_ledger_2026_03_15.md` |
| `A3` | `A` | `queued` | `(++)` boundary inventory |
| `A4` | `A` | `queued` | proof-obligation table `H1^\infty -> H1^\partial -> H1^f` |
| `B1` | `B` | `queued` | smallest admissible finite-block `PSD-pd` step |
| `P1` | `P` | `sent` | Proshka adapter theorem-shape / blockwise cancellation request |

## Current step

### `A2` — plus-minus cancellation ledger

Goal:

- turn the Day 1 formula ledger into a cancellation ledger;
- separate what must vanish in `(+,-)` from what can only survive in `(++)`;
- make the first exact/corrected theorem target explicit.

Required output:

- named bulk term;
- named boundary term;
- named cap term;
- named compression term;
- expected vanishing / surviving table.

Exact success criterion:

- after reading the new note, the next theorem attempt is unambiguously
  `M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_a^{+-}`,
  with a clear statement of which pieces of `E_a^{+-}` are expected to vanish.

## Next after current step

If `A2` lands:

- switch `current_step_id` to `A3`;
- build `(++)` boundary inventory;
- keep lane B alive but secondary.

If `A2` fails:

- do not open a new route;
- mark `A2` as `blocked`;
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
