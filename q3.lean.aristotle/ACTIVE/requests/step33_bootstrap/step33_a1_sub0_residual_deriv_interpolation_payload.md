# Step33A.1-A Sub0 Residual-Derivative Interpolation Payload

Fail-closed skeleton.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_residual_deriv_interpolation_payload.v2`
- status: `blocked_missing_exact_interpolation_inputs`
- cert: `primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert`
- receiver: `RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound`
- sub0 landing receiver: `RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_deriv_interpolation_error_bound`
- cell: `Set.Icc (0 : Real) ((1 : Real) / 10)`
- derivSlope: `1866608532757/500000000000000000000000000000`
- proof-safe closed fields: `0`
- Lean emitted: `False`

## Exact Budget

- relation: `interpolationError + modelBound <= derivSlope`
- lhs: `None`
- rhs: `1866608532757/500000000000000000000000000000`
- margin: `None`
- passes: `None`

## Missing Inputs

- `STEP33_A1_SUB0_MODEL_DERIV_EXACT_NORM_GAP`
- `STEP33_A1_SUB0_INTERPOLATION_ERROR_EXACT_REMAINDER_GAP`

## Receiver Shape

`modelDeriv : Real -> Real, hModel : forall eta in cell, ||modelDeriv eta|| <= modelBound, hError : forall eta in cell, ||deriv cert.residual eta - modelDeriv eta|| <= interpolationError, hBudget : interpolationError + modelBound <= data.derivSlope`

## Sub0 Landing Shape

`modelDeriv : Real -> Real, hModel : forall eta in Set.Icc 0 (1/10), ||modelDeriv eta|| <= modelBound, hError : forall eta in Set.Icc 0 (1/10), ||deriv cert.residual eta - modelDeriv eta|| <= interpolationError, hBudget : interpolationError + modelBound <= 1866608532757/500000000000000000000000000000`

## Guard

- not Lean proof data
- does not import or trust sampled derivative JSON
- does not emit a Lean payload theorem
- sub0 landing receiver is checked separately in Lean
- modelBound must be derived by exact rational interval operations
- interpolationError must bound ||deriv residual - modelDeriv|| uniformly on [0, 1/10]
- a positive exact budget margin is required before Lean emission is enabled
