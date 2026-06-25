# Step33A.1-A Raw-D17 Signed-Factor Two-Segment Rows Audit

schema: `q3_psdpd_step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_two_segment_rows_audit.v3`
route: `collapsed_degree0_raw_d17_signed_factor_two_segment_rows_audit`
proofStatus: `fail_closed_two_segment_budget_constant_fail`

## Verdict

- shouldEmitTwoSegmentLeanPayload: `False`
- twoSegmentPayloadExists: `True`
- proofGradeLocalRowsPresent: `True`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_CONSTANT_FAIL`
- firstFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_CONSTANT_FAIL`
- nextFailureCodeIfRowsCloseButBudgetFails: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_CONSTANT_FAIL`

## Segments

- `left`: cellL=`0`, cellU=`1/20`
- `right`: cellL=`1/20`, cellU=`1/10`

## Missing Proof-Grade Row Theorems

### Order-18 generic Taylor bridge

- status: `present`
- failureCodeIfMissing: `STEP33_A1_SUB0_CENTERED_TAYLOR_DERIVATIVE_MAJORANT18_BRIDGE_GAP`

### Uniform order-18 source rows

- status: `present`

### Local center-jet payload interfaces

#### `primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_twoSegment_interval`

- status: `present`
- purpose: proof-grade lower/upper rows for normalized OmegaActual center jets through j < 18 at local centers 1/40 and 3/40

```lean
theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_twoSegment_interval
    (i : Fin 2) (j : Fin 18) :
    let center : Real := if i.1 = 0 then (1/40 : Real) else (3/40 : Real)
    (omegaCenterJetLower i j : Real) <=
        iteratedDeriv j.1 step22OmegaArchWeight center /
          (Nat.factorial j.1 : Real)
    /\
        iteratedDeriv j.1 step22OmegaArchWeight center /
          (Nat.factorial j.1 : Real)
      <= (omegaCenterJetUpper i j : Real)
```

#### `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_twoSegment_interval`

- status: `present`
- purpose: proof-grade lower/upper rows for normalized ShapeSqActual center jets through j < 18 at local centers 1/40 and 3/40

```lean
theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_twoSegment_interval
    (i : Fin 2) (j : Fin 18) :
    let center : Real := if i.1 = 0 then (1/40 : Real) else (3/40 : Real)
    (shapeSqCenterJetLower i j : Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSq center /
          (Nat.factorial j.1 : Real)
    /\
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSq center /
          (Nat.factorial j.1 : Real)
      <= (shapeSqCenterJetUpper i j : Real)
```

### Derived local derivative interval interfaces

#### `primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_interval`

- status: `present`
- purpose: uniform local lower/upper rows for OmegaActual derivatives on each of the two subsegments, derived from local center jets and centeredTaylorDerivMajorant18

```lean
theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_interval
    (i : Fin 2) (k : Fin 19) :
    forall eta in Set.Icc (cellL i : Real) (cellU i : Real),
      (omegaLower i k : Real) <=
          iteratedDeriv k.1 step22OmegaArchWeight eta
      /\
          iteratedDeriv k.1 step22OmegaArchWeight eta
        <= (omegaUpper i k : Real)
```

#### `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_interval`

- status: `present`
- purpose: uniform local lower/upper rows for ShapeSqActual derivatives on each of the two subsegments, derived from local center jets and centeredTaylorDerivMajorant18

```lean
theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_interval
    (i : Fin 2) (k : Fin 19) :
    forall eta in Set.Icc (cellL i : Real) (cellU i : Real),
      (shapeSqLower i k : Real) <=
          iteratedDeriv k.1
            primaryFiniteRow0Parent0Split100Sub0ShapeSq eta
      /\
          iteratedDeriv k.1
            primaryFiniteRow0Parent0Split100Sub0ShapeSq eta
        <= (shapeSqUpper i k : Real)
```

## Target Payload Theorems

- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_valid`: present=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean`, line=`366`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_valid`: present=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean`, line=`373`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_family_valid`: present=`False`, file=`None`, line=`None`

## Budget Fail Theorems

- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_budget_fail_rat`: present=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean`, line=`456`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_budget_not_spendable`: present=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean`, line=`464`

## Checked Supporting Surfaces

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeMajorant18.lean`

- exists: `True`
- sha256: `54da6c8ce5cacc7c5de63ef256fd81a878f96fd3f356d6d32c1ca70fab84bcaa`
- allSymbolsPresent: `True`

- `centeredTaylorDerivMajorant18`: present=`True`, line=`168`
- `centeredTaylorDerivMajorant18Range`: present=`True`, line=`185`
- `centeredTaylorDerivMajorant18_last`: present=`True`, line=`395`
- `iteratedDeriv_norm_le_centeredTaylorDerivMajorant18_last`: present=`True`, line=`419`
- `iteratedDeriv_norm_le_centeredTaylorDerivMajorant18`: present=`True`, line=`202`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Source.lean`

- exists: `True`
- sha256: `a5c3f5968ec55f259c292e18135ceb785a979b6e776b5a4638342c45dc425c68`
- allSymbolsPresent: `True`

- `primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18`: present=`True`, line=`83`
- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18`: present=`True`, line=`115`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqOrder18Payload.lean`

- exists: `True`
- sha256: `e16cc19cae3870a7e442b6cad4ac01f8e9ab335a05f656b299a258693f5caa86`
- allSymbolsPresent: `True`

- `primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18`: present=`True`, line=`322`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18`: present=`True`, line=`333`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17LocalCenterJets18Payload.lean`

- exists: `True`
- sha256: `9d7f97e213eb9419239cfbd47c9d0c05766f755b5122d0e8f003c8b824ce96dd`
- allSymbolsPresent: `True`

- `primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter`: present=`True`, line=`28`
- `primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetLower`: present=`True`, line=`142`
- `primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetUpper`: present=`True`, line=`147`
- `primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetLower`: present=`True`, line=`159`
- `primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetUpper`: present=`True`, line=`164`
- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet_interval_generated`: present=`True`, line=`188`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet_interval_generated`: present=`True`, line=`227`
- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_interval`: present=`True`, line=`497`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_interval`: present=`True`, line=`555`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean`

- exists: `True`
- sha256: `9658b8145980ecb70c319d7f1b90c7ef19fddc92c935fc52cc99b504c2e0b5f8`
- allSymbolsPresent: `True`

- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_valid`: present=`True`, line=`366`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_valid`: present=`True`, line=`373`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_budget_not_spendable`: present=`True`, line=`464`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean`

- exists: `True`
- sha256: `61b77b223ee3531a22ab06b5a5a82ca661e5462c13c574aa4a80da64ba6b4c34`
- allSymbolsPresent: `True`

- `Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert`: present=`True`, line=`116`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_interval_of_signed_factor_segment`: present=`True`, line=`368`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment`: present=`True`, line=`383`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorPayload.lean`

- exists: `True`
- sha256: `275365f66124a94ea0b89d65bd0fe834568d8bdd049d0beacee6c7fdba29f9cb`
- allSymbolsPresent: `True`

- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_valid`: present=`True`, line=`267`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_rawPoly_segment0_valid`: present=`True`, line=`359`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_not_spendable`: present=`True`, line=`403`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload.lean`

- exists: `True`
- sha256: `b738f63142f35c9679158af0ebe30acd2a60d37eeb5012c4a80207ee12feec46`
- allSymbolsPresent: `True`

- `Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert`: present=`True`, line=`556`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_raw_poly_segment_family_cert`: present=`True`, line=`635`

## Boundary

- This audit is not a proof of Step33A.1-A.
- This audit is not a Lean payload and does not create a Lean payload.
- The order-18 generic Taylor bridge is only an analytic transport layer.
- Local center-jet payload rows remain separate proof objects.
- The checked full-cell smoke segment remains non-spendable.
- The global symmetric full-cell rows must not be reused as local segment rows.
- A two-segment rows gap does not kill the direct whole-expression route.

## Next Implementable Patch

Build proof-grade local center-jet rows through `j < 18` for `OmegaActual` and `ShapeSqActual` at centers `1/40` and `3/40`; reuse the checked full-cell order-18 source bounds; derive local derivative interval rows through `k = 18` with `centeredTaylorDerivMajorant18`; then emit the two raw-D17 signed-factor segment certs and the raw/poly family cert.
