# Step32 Next Gate

Date: 2026-05-26

## Status

Superseded for active execution by:

```text
q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md
q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md
```

This request is retained as historical Step32/early-Step33 context.  New PSD
Step33 work should append to:

```text
q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/report.md
```

## Objective

Operate the current Q3 Step32 proof loop until one new Step32 theorem compiles
or `report.md` names the exact missing lemma/blocker.

This request supersedes stale Step32 prompts that target
`centeredBSplineArchIntegrand_translatedPacketSum_integrable`; that gate is
already closed in the current repo.

## Current State

The centered B-spline matrix-identification bridge is closed:

- `centeredBSplineCoeffBasisExpansion_synth_eq_sum`
- `centeredBSplineCoeffWeilForm_eq_matrixSub_quadForm`
- `centeredBSplineBoundaryRows_identify_Q`

The following certificate receivers are also already wired or scaffolded:

- Q-row hbox import.
- Boundary Gram radius import.
- Penalty radius dominance import.
- Base matrix hbox receiver.
- Analytic P0 receiver.
- Entry hbox bundle scaffold.
- Prime dictionary bounds.
- Centered B-spline R nonnegativity.

## Exact Live Gate

Target file:

`Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean`

Target declarations:

- `PrimaryK11BaseEntryHboxCert`
- `ControlK9BaseEntryHboxCert`
- `ActiveCenteredCoeffEntryHboxCert`
- `primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert`
- `controlK9CertifiedCoeffBlock_of_activeEntryHboxCert`

The expected missing proof surface is the generated `matrixEntrywiseAbsLe`
entry bounds for:

- `primaryK11AnalyticA`
- `primaryK11AnalyticP`
- `primaryK11AnalyticP0`
- `controlK9AnalyticA`
- `controlK9AnalyticP`
- `controlK9AnalyticP0`

## Smallest Acceptable Deliverable

Choose one:

1. Add or integrate a generated certificate module proving one missing hbox
   field for the active entry certificate.
2. Package already-proven generated hboxes into
   `ActiveCenteredCoeffEntryHboxCert` without weakening theorem statements.
3. Write a precise blocker report naming the exact scalar enclosure engine,
   imported table, theorem, or file that is missing.

## Files To Inspect

- `Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean`
- `Q3/Proofs/PSD_CenteredCoeffAnalyticP0Import.lean`
- `Q3/Proofs/PSD_CenteredCoeffBaseHboxImport.lean`
- `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `Q3/Proofs/PSD_CenteredCoeffQRowImport.lean`
- `Q3/Proofs/PSD_CenteredCoeffPrimeDictionaryBoundsImport.lean`
- `Q3/Proofs/PSD_CenteredBSplineRBoundsImport.lean`
- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`

## Validation

From `q3.lean.aristotle`:

```bash
lake env lean Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

From the repo root:

```bash
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

Every integrated Lean file must be scanned for `sorry`, `exact?`, and `admit`.
Do not edit `Q3.Main`.

## Stop Condition

Stop only when one new Step32 theorem compiles, or when `report.md` contains a
precise blocker report with the missing declaration and the next requested
action.
