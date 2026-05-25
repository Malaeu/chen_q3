# Step32F penalty-box cert wrappers report

## Status

Closed.

## Commit

Recorded in the session final summary after commit creation.

## Request

Package the generated radius-floor D/R lower-bound adapters into active finite
penalty certificates, parameterized by the future analytic penalty-box hbox
hypotheses.

## Declarations added

The generator now emits these wrappers in
`Q3.Proofs.PSD_CenteredCoeffRadiusFloorImport`:

- `primaryK11PenaltyLowerBoundCert_of_penalty_boxes`
- `primaryK11FinitePenaltyCert_of_penalty_boxes`
- `controlK9PenaltyLowerBoundCert_of_penalty_boxes`
- `controlK9FinitePenaltyCert_of_penalty_boxes`

Each wrapper accepts:

- an analytic candidate `D` matrix;
- an analytic candidate `R` matrix;
- an analytic candidate boundary matrix `Q`;
- a D-side entrywise penalty-box hypothesis;
- an R-side entrywise penalty-box hypothesis.

The lower-bound wrappers return `Q3.Proofs.FinitePenaltyLowerBoundCert`; the
strict wrappers return `Q3.Proofs.FinitePenaltyCert`.

## Files touched

- `scripts/q3_psdpd_step32f_radius_floor_lean_data.py`
- `Q3/Proofs/PSD_CenteredCoeffRadiusFloorImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_penalty_box_cert_wrappers/report.md`

## Commands run

- `python3 -m py_compile scripts/q3_psdpd_step32f_radius_floor_lean_data.py`
- `python3 scripts/q3_psdpd_step32f_radius_floor_lean_data.py`
- `lake env lean Q3/Proofs/PSD_CenteredCoeffRadiusFloorImport.lean`
- `lake build Q3.Proofs.PSD_CenteredCoeffRadiusFloorImport`
- `lake build Q3.Main`
- focused hole scan over the generator, generated Lean file, and this report
- `git diff --check`
- `./scripts/check_axioms.sh`

## Compile status

Closed. The generated import file, focused module build, and `Q3.Main` all
compiled. The focused hole scan found no holes in the touched proof/generator
files or this report. `git diff --check` passed. The axiom profile check passed
with the expected five axioms: three standard Lean axioms and two documented
project axioms.

## Remaining blocker

The four analytic hbox hypotheses are still future obligations:

- primary `k=11` D penalty box;
- primary `k=11` R penalty box;
- control `k=9` D penalty box;
- control `k=9` R penalty box.

## Next smallest theorem

Build the analytic hbox bridge from concrete B-spline/contract entries to the
imported midpoint/radius penalty boxes.
