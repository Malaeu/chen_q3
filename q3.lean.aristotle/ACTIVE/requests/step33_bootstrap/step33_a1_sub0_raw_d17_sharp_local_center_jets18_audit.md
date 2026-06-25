# Step33A.1-A Raw-D17 Sharp Local Center-Jets18 Audit

schema: `q3_psdpd_step33_a1_sub0_raw_d17_sharp_local_center_jets18.v1`
route: `raw_d17_sharp_local_center_jets18`
proofStatus: `fail_closed_sharp_two_segment_budget_constant_fail`

## Verdict

- targetLeanExists: `True`
- sharpRowsPresent: `True`
- sharpBudgetFailPresent: `True`
- sharpBudgetKillFileExists: `True`
- sharpBudgetKillPresent: `True`
- coarseTwoSegmentBudgetFailPresent: `True`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_CONSTANT_FAIL`
- nextFailureIfSharpBudgetFalse: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_CONSTANT_FAIL`

## Required Sharp Theorems

### `primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_sharp_interval_generated`

- status: `present`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean`
- line: `539`
- purpose: proof-grade sharp lower/upper rows for normalized OmegaActual center jets through j < 18 at local centers 1/40 and 3/40

### `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_sharp_interval_generated`

- status: `present`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean`
- line: `563`
- purpose: proof-grade sharp lower/upper rows for normalized ShapeSqActual center jets through j < 18 at local centers 1/40 and 3/40

### `primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_sharp_interval`

- status: `present`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean`
- line: `649`
- purpose: two-segment OmegaActual derivative rows derived from sharp local center jets and centeredTaylorDerivMajorant18

### `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_sharp_interval`

- status: `present`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean`
- line: `707`
- purpose: two-segment ShapeSqActual derivative rows derived from sharp local center jets and centeredTaylorDerivMajorant18

### `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_valid`

- status: `present`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean`
- line: `1048`
- purpose: raw-D17 signed-factor segment/family receiver fed by sharp rows

## Sharp Budget Kill File

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SharpTwoSegmentBudgetKill.lean`
- exists: `True`

### `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_fail_rat`

- present: `True`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SharpTwoSegmentBudgetKill.lean`
- line: `31`

### `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_not_spendable`

- present: `True`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SharpTwoSegmentBudgetKill.lean`
- line: `41`

## Sharp Budget Theorems

### `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_budget_fail_rat`

- present: `True`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean`
- line: `1180`

### `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_budget_not_spendable`

- present: `True`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean`
- line: `1188`

## Candidate Source Surfaces

### `scripts/generate_step33_a1_sub0_omega_prime_taylor_payload.py`

- exists: `True`
- sha256: `7fe0761bb92e82851651dafeb11aca77834c32f15cac2258b7599b7f2afb091c`

- `build_center_jet_prefix_tail_rows`: present=`True`, line=`408`
- `centerJetPrefixTailRowsProofGrade`: present=`True`, line=`955`
- `centerJetPrefixTailBridgeTheorem`: present=`True`, line=`939`

### `scripts/generate_step33_a1_sub0_component_taylor_residual_payload.py`

- exists: `True`
- sha256: `01f0486d49e7a6f3e80e025a9c0d1dbab4bc460fe1e999b3dab54ea85dd63e34`

- `SHAPESQ_DERIV_TAYLOR_COARSE_CENTER`: present=`True`, line=`350`
- `SHAPESQ_DERIV_TAYLOR_COARSE_REMAINDER`: present=`True`, line=`351`
- `omegaTaylorCenterAnchorSource`: present=`True`, line=`2380`

### `scripts/q3_psdpd_step33_a_refined_subchunk_endpoint_rational_lean.py`

- exists: `True`
- sha256: `e8af9db5f0a358975ace698edd2b045c8412b3611f66da483f1fd36871c432f2`

- `shifted_digamma_series_prefix_tail_interval`: present=`True`, line=`589`
- `EndpointIntervalCert_of_shifted_digamma_series`: present=`True`, line=`592`

## Boundary

- This is not Step33A.1-A closure.
- This audit does not emit the sharp Lean payload.
- The previous full-cell absolute majorants are not sharp local rows.
- The coarse two-segment budget fail remains local to the coarse row class.
- If `sharpBudgetFailPresent = true`, this sharp two-segment class is Lean-killed by the exact budget comparison.
- If `sharpBudgetKillPresent = true`, the route-facing kill alias is available for monitor and downstream ledger references.

## Next Implementable Patch

Pivot to the direct whole-expression row-source route and keep `CollapsedExpression` intact through interval widening.  Do not continue factorwise two-segment sharpening.
