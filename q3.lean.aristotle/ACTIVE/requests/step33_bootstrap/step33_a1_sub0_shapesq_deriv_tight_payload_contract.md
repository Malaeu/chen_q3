# Step33A.1-A Sub0 ShapeSqDeriv Tight Payload Contract

Status: fail-closed contract only.  This file is not Lean proof data and does
not close Step33A.1-A.

## Current State

The coarse `coarseTwo` realSinc-to-ShapeSqDeriv chain is proof-grade as an
interface test, but it is not spendable for the live residual route:

```lean
Step33Sub0RealSincDerivativeMajorantCert.coarseTwoBaseAbs_providesAnalyticMajorant
primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_coarseTwo
primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo_rational
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_coarseTwo
```

Killed route:

```text
STEP33_A1_SUB0_COARSE_SHAPESQ_TAYLOR_PRIMARY_RESIDUAL_CROSSWALK_FAIL
```

Reason: the coarse payload uses zero ShapeSqDeriv coefficients and a huge
uniform budget.  It does not define the same coefficient stream consumed by
`primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual`.

## Target Theorem

The next proof-producing target is:

```lean
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid :
    (ShapeSqDerivTaylorIntervalCert.singleAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs).Valid := by
  ...
```

The names above are contract names.  Do not emit this theorem until the
coefficient objects are generated in the same convention as the active
component payload.

## Existing Receivers

Already present locally:

```lean
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_interval
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shapeSq_derivative_abs
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff_abs_of_shapeSq_succ_abs
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_order16_abs_of_shapeSq_order17_abs
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shape_derivative_abs
```

Closed coefficient rows:

```lean
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff0_interval_generated
primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff1_interval_generated
```

## Required Generated Objects

The tight payload must provide:

```lean
primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff :
  Fin 16 -> Rat

primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs :
  Fin 16 -> Rat

primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs :
  Rat
```

and proof-grade evidence for:

```text
rows 2..15:
  power-series coefficient interval or same-strength derivative-absolute data

order16:
  uniform ShapeSqDeriv order-16 bound, equivalently shape-square order-17 bound

bookkeeping:
  coeffErrorAbs nonnegative
  generated lower/upper rows lie inside coeff +/- coeffErrorAbs
```

## Same-Coefficient Guard

Before any Lean theorem named `shapeSqDeriv_tight_valid` is emitted, the
generator must prove or record the exact source of the tight coefficient stream:

```text
ShapeSqDerivTightCoeff / ShapeSqDerivTightCoeffErrorAbs
  -> active component Taylor payload convention
  -> primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
```

If this source cannot be identified, stop before Lean emission with:

```text
STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_COEFF_STREAM_GAP
```

## Current First Failure

```text
STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP
```

Route-level failure remains:

```text
STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP
```

## Do Not

- Do not set all coefficients to zero.
- Do not spend the coarse `coarseTwo` payload as final residual evidence.
- Do not add another receiver before a concrete missing receiver is identified.
- Do not attack the final residual interval theorem before the tight source
  and coefficient-stream crosswalk exist.
- Do not edit `Q3.Main`.

