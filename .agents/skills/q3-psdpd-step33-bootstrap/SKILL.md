---
name: q3-psdpd-step33-bootstrap
description: "Q3 PSD-pd Step33 bootstrap workflow: continue the finite certified B-spline packet backend from closed Step32 into Step33A entry-hbox certificates, using PSD_STEP33_MONITOR, step33_bootstrap request/report discipline, and direct Lean validation."
metadata:
  short-description: Q3 PSD Step33 bootstrap workflow
---

# Q3 PSD Step33 Bootstrap Skill

Use this skill when the task mentions Q3, PSD-pd, Step32, Step33, B-spline,
entry hboxes, `ActiveCenteredCoeffEntryHboxCert`, `matrixEntrywiseAbsLe`,
`FinitePenaltyCert`, `CertifiedCenteredBSplineCoeffBlock`, WeilForm, A/P/P0,
or centered-cardinal B-spline scalar replay.

## Required Reads

Read these before choosing a target:

1. `AGENTS.md`
2. `Q3_OBSTRUCTION_ATLAS.md`
3. `SESSION_ENTRY.md`
4. `q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md`
5. `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md`
6. The latest Step33 entries in `q3.lean.aristotle/docs/INSIGHTS.md`

Do not use `q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md` as the current frontier
for PSD/Step33 work.  It is the parked H1/PO3 route monitor unless the user
explicitly asks for H1, PO3, H-bridge, or route-kill work.

## Current Live Gate

Step32 is closed.  The live PSD gate is Step33A.1:

- primary/control analytic `A/P/P0` entry hbox lemmas;
- then Step33A.2 consumes `hA/hP/hP0` through `matrixEntrywiseAbsLe`;
- then Step33A.3 packages `CertifiedCenteredBSplineCoeffBlock`;
- then Step33B/Step33C consume certified blocks/families.

The current practical source proof is the primary prime-side `P` entry hbox.
Recent compiled receiver chain:

- `primaryK11AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes`
- `primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_cardinal_hboxes`
- `primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_summand_hboxes`

The next generated replay layer is scalar `positivePartPower` /
polynomial-segment hboxes for degree-23 primary summands.  Control `k=9`
follows the same shape after primary.

## Workflow

1. Read the PSD monitor and `step33_bootstrap` request/report.
2. Search for the exact declaration and upstream wrappers.
3. Pick the smallest theorem target that advances Step33A.1.
4. Keep edits inside PSD Step33-local modules unless the request says
   otherwise.
5. Do not edit `Q3.Main` before Step35.
6. Run `lake env lean <touched Lean file>` from `q3.lean.aristotle`.
7. Run `scripts/q3_check.sh <touched Lean file>` from the repo root.
8. If route choice or generated payload shape is unclear, append a
   `PRO_REVIEW_REQUEST` to
   `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/report.md`.
9. Update `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/report.md` with
   theorem, files touched, validation commands, and status.
10. Add a short synthesis to `q3.lean.aristotle/docs/INSIGHTS.md`.

## Guardrails

- No `sorry`, `admit`, or `exact?`.
- No fake axioms or trusted generated payloads.
- No numerical PSD table as proof.
- No raw-coordinate PSD proof when the Gram-corrected coefficient model is
  required.
- No theorem weakening to make a gate compile.
- Do not call untracked files foreign or disposable; they are simply not
  tracked by Git unless the task says otherwise.
- Do not assume automatic access to the Pro/Louise chat.  Use pasted or
  appshot context only when supplied; otherwise write `PRO_REVIEW_REQUEST`.
