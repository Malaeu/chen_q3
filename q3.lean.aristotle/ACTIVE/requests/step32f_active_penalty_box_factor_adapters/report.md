# Step32F active penalty-box factor adapters report

## Status

Closed.

## Request

Specialize the generic penalty-matrix hbox factor receiver to the active
primary and control coefficient blocks.

## Declarations added

In `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`:

- `primaryK11DPenaltyBox_of_matrix_and_boundaryGram`
- `primaryK11RPenaltyBox_of_matrix_and_boundaryGram`
- `controlK9DPenaltyBox_of_matrix_and_boundaryGram`
- `controlK9RPenaltyBox_of_matrix_and_boundaryGram`

Each adapter proves:

```text
base matrix hbox
+ boundary Gram hbox
+ composed radius <= imported penalty radius
=> exact active penalty-box hypothesis
```

for the corresponding D/R penalty wrapper.

## Files touched

- `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_active_penalty_box_factor_adapters/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `lake build Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport`
- focused hole scan on the edited Lean file and report
- `git diff --check`
- `lake build Q3.Main`
- `./scripts/check_axioms.sh`

## Compile status

Closed. The edited active adapter file compiles, `Q3.Main` builds, and the
axiom gate passes with the expected profile: 3 standard Lean axioms and 2
documented project axioms.

## Remaining blocker

The analytic base-matrix hboxes, boundary-Gram hboxes, and pointwise radius
dominance lemmas are still open. This node closes the active-block adapter
layer consuming those future facts.

## Next smallest theorem

Prove the shared boundary-Gram hbox for the active boundary rows, starting with
`primaryK11`: compare `boundaryGramMatrix primaryK11AnalyticQ` against
`boundaryGramMatrix primaryK11Q` with a generated or analytic radius matrix.
