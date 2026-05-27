# Step33 Bootstrap Request

Date: 2026-05-27

## Objective

Operate the current PSD-pd Step33 bootstrap loop until one new Step33 theorem
compiles, or until `report.md` names the exact missing scalar replay
lemma/blocker.

This request supersedes the active-use role of:

```text
q3.lean.aristotle/ACTIVE/requests/step32_next_gate/node.md
```

The old Step32 request/report remain as historical context.  New PSD Step33
work should update this request's `report.md`.

## Route Boundary

This is not the H1/PO3 monitor.  While
`q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md` has `status: ACTIVE`, continue
the finite PSD-pd certificate backend:

```text
Step32 closed -> Step33A -> Step33B -> Step33C -> Step34 -> Step35
```

Do not route to `ACTIVE/PHASE_MONITOR.md` unless the user explicitly asks for
H1, PO3, H-bridge, or route-kill work.

## Current State

Step32 is closed:

- `centeredBSplineCoeffBasisExpansion_synth_eq_sum`
- `centeredBSplineCoeffWeilForm_eq_matrixSub_quadForm`
- `centeredBSplineBoundaryRows_identify_Q`

The current Step33A.1 prime-side `P` chain has compiled receivers down to
truncated-power summand hboxes:

- log/exp prime-weight receivers;
- weighted R-pair term receivers;
- cardinal numerator to `centeredBSplineR` receivers;
- summand hboxes to cardinal numerator receivers.

## Exact Live Gate

Target files:

```text
Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean
Q3/Proofs/PSD_CenteredBSplineRBoundsImport.lean
Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

Target declaration chain:

```lean
primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_summand_hboxes
primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_cardinal_hboxes
primaryK11AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes
```

The expected missing generated proof surface is scalar midpoint/radius hboxes
for the `positivePartPower` / polynomial-segment summands of the degree-23
primary cardinal numerator.

Control `k=9` follows the same pattern after primary is wired.

## Smallest Acceptable Deliverable

Choose one:

1. Add a Lean-checked receiver proving one smaller scalar replay layer below
   `centeredCardinalBSplineSummand`.
2. Integrate generated primary `k=11` summand hboxes into the compiled
   receiver chain without weakening theorem statements.
3. Write a precise blocker report naming the exact missing scalar enclosure
   engine, generated table, theorem, or file.

## Validation

From `q3.lean.aristotle`:

```bash
lake env lean Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean
lake env lean Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

From the repo root:

```bash
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

Every integrated Lean file must be scanned for `sorry`, `exact?`, and `admit`.
Do not edit `Q3.Main`.

## Pro / Louise Escalation

Do not assume automatic access to the ChatGPT Pro/Louise thread.  Use pasted or
attached chat/appshot context only when the user supplies it.  Otherwise, if the
route choice or generated payload shape is unclear, append this block to
`report.md`:

```md
## PRO_REVIEW_REQUEST

Route:
Current step:
Current theorem:
File:
Lean error / blocker:
Options:
A.
B.
C.
Codex recommendation:
Question for Louise:
```

## Stop Condition

Stop only when one new Step33 theorem compiles, or when `report.md` contains a
precise blocker report with the missing declaration and next requested action.
