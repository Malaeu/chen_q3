---
name: q3-step32-lean
description: "Q3 PSD-pd Step32 Lean workflow: close the next B-spline matrix-identification/certified-block gate using the obstruction atlas, request/report discipline, and direct Lean validation."
metadata:
  short-description: Q3 Step32 Lean gate workflow
---

# Q3 Step32 Lean Skill

Use this skill when the task mentions Q3, PSD-pd, Step32, B-spline,
WeilForm, FinitePenaltyCert, CertifiedCenteredBSplineCoeffBlock, packet
matrices, boundary rows, or entry hbox certificates.

## Required Reads

Read these files before choosing a proof target:

1. `AGENTS.md`
2. `Q3_OBSTRUCTION_ATLAS.md`
3. `SESSION_ENTRY.md`
4. `q3.lean.aristotle/PROJECT_WORKFLOW.md`
5. `q3.lean.aristotle/ACTIVE/requests/step32_next_gate/node.md`
6. The latest Step32 entries in `q3.lean.aristotle/docs/INSIGHTS.md`

## Current Live Gate

The current Step32 gate is the generated entry-hbox layer in:

`q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean`

The target certificate chain is:

- `PrimaryK11BaseEntryHboxCert`
- `ControlK9BaseEntryHboxCert`
- `ActiveCenteredCoeffEntryHboxCert`
- `primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert`
- `controlK9CertifiedCoeffBlock_of_activeEntryHboxCert`

The concrete missing proof shape is expected around the `matrixEntrywiseAbsLe`
fields for `A`, `P`, and `P0` on the primary k=11 and control k=9 blocks.

## Closed Gates

Do not reopen these unless current files show a regression:

- `centeredBSplineArchIntegrand_translatedPacketSum_integrable`
- `centeredBSplineCoeffBasisExpansion_synth_eq_sum`
- `centeredBSplineCoeffWeilForm_eq_matrixSub_quadForm`
- `centeredBSplineBoundaryRows_identify_Q`
- Q-row hbox import
- Boundary Gram radius import
- Penalty radius dominance import
- Base matrix hbox receiver
- Analytic P0 receiver
- Prime dictionary bounds
- Centered B-spline R nonnegativity

## Workflow

1. Search the repo for the exact declaration and its upstream wrappers.
2. Pick the smallest theorem target that advances the active request.
3. Keep edits inside Step32-local modules unless the request explicitly says
   otherwise.
4. Do not edit `Q3.Main` for a Step32 local gate.
5. Run `lake env lean <touched Lean file>` from `q3.lean.aristotle`.
6. Run `scripts/q3_check.sh <touched Lean file>` from the repo root.
7. Update `q3.lean.aristotle/ACTIVE/requests/step32_next_gate/report.md`
   with the exact theorem, files touched, validation commands, and status.

## Guardrails

- No `sorry`, `admit`, or `exact?`.
- No fake axioms or trusted generated payloads.
- No numerical PSD table as proof.
- No raw-coordinate PSD proof when the Gram-corrected coefficient model is
  required.
- No theorem weakening to make a gate compile.
- Keep A3_FLOOR and old RKHS proof strategies separated.
- Aristotle and Oracle outputs are advisory until Lean accepts hole-free code.
