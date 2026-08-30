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

Do not model Step33 as a long list of row, entry, shift, or scalar-table proof
goals.  The mathematical Step33 contract has exactly three gates:

- 33A: construct `ActiveCenteredCoeffEntryHboxCert`;
- 33B: derive finite analytic Weil positivity from certified centered coeff
  blocks;
- 33C: package the singleton `DirectedCertFamily` handoff.

The current thin aggregator theorem is:

- `psd_step33_closed_from_deltaLiveTightSumChecksWithCenterError`.
- `psd_step33_closed_from_namedDeltaLiveTightSumChecksWithCenterError`.

The older exact midpoint-equality aggregator
`psd_step33_closed_from_deltaLiveTightSumChecks` remains a stricter compiled
compatibility surface.  The active generated-payload contract follows the
1024-bit/36-decimal audit:

```text
abs(live_mid_sum - imported_P_mid) + live_rad_sum <= imported_P_radius
```

The active generated payload facts are named:

- `primaryK11TightLiveCenterErrorSumCheck`;
- `controlK9TightLiveCenterErrorSumCheck`.

If blocked, classify the blocker only as:

- A. missing generated live tight-sum fact;
- B. missing `ActiveCenteredCoeffEntryHboxCert` receiver;
- C. missing `CertifiedCenteredBSplineCoeffBlock` receiver;
- D. missing finite analytic Weil positivity receiver;
- E. missing `DirectedFamily`/singleton handoff receiver.

The current practical source proof is the primary prime-side `P` entry hbox.
Recent compiled receiver chain:

- `primaryK11AnalyticP_entry_hbox_of_log_exp_weight_and_R_pair_hboxes`
- `primaryK11CenteredBSplineR11PrimeShiftPair_hbox_of_cardinal_hboxes`
- `primaryK11CenteredCardinalBSpline23PrimeShiftPair_hbox_of_summand_hboxes`

The `(0,0)` direct-profile certificate is only a pilot.  Do not continue
manual row-by-row or entry-by-entry scalar replay.  The next replay layer should
first add structural compression:

- packet center delta compression;
- compact-support live prime-shift filtering;
- live/segment hbox receiver for centered cardinal B-splines;
- generated scalar payloads only for live terms.

Control `k=9` follows the same shape after primary.

## Workflow

1. Read the PSD monitor and `step33_bootstrap` request/report.
2. Search for the exact declaration and upstream wrappers.
3. Pick the smallest theorem target that advances Step33A.1.
4. Keep edits inside PSD Step33-local modules unless the request says
   otherwise.
5. Do not edit `Q3.Main` before Step35.
6. Run `lake env lean <touched Lean file>` from `q3.lean.aristotle`.
7. Run `scripts/q3_check.sh <touched Lean file>` from the repo root.
8. If route choice or generated payload shape reaches an eligible registered
   review gate, create the source-locked request in the canonical queue and run
   `orchestrator/workflow_runtime.py review-plan` with its exact attachment,
   request commit, request ID, boundary ID, and SHA-256. Only
   `REVIEW_DISPATCH_READY` permits the current Codex body to send the single
   byte-exact UTF-8 `.txt` through the same living Proshka chat and observe the
   delivery receipt. Otherwise record the exact HOLD; do not create an ad-hoc
   review marker or a new chat.
9. Update `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/report.md` with
   theorem, files touched, validation commands, and status.
10. Add a short synthesis to `q3.lean.aristotle/docs/INSIGHTS.md`.

## Guardrails

- No `sorry`, `admit`, or `exact?`.
- No fake axioms or trusted generated payloads.
- No numerical PSD table as proof.
- No raw-coordinate PSD proof when the Gram-corrected coefficient model is
  required.
- No silent theorem weakening merely to make a gate compile. A strictly weaker
  theorem is allowed only when the unchanged downstream consumer is named and
  an exact proved implication from the weaker interface to that consumer is
  part of the contract.
- Do not call untracked files foreign or disposable; they are simply not
  tracked by Git unless the task says otherwise.
- Proshka transport uses only the registered same-living-chat lifecycle in
  `docs/CODEX_CONTROL.md`: canonical queue, source-locked attachment,
  `review-plan`, and an observed natural-reasoning receipt. Pasted/appshot
  context is evidence only and never substitutes for dispatch or receipt.
