# Step33A.1-A ActiveActual Order-16 Degree-0 Preflight

schema: `q3_psdpd_step33_a1_sub0_active_actual_order16_degree0_payload.v1`
route: `active_actual_order16_degree0_preflight`

## Verdict

- proofStatus: `blocked_missing_d16_center_d17_uniform_source`
- proofGrade: `False`
- receiverReady: `True`
- outLeanWritten: `False`
- budgetPassed: `None`
- firstFailure: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`

## Target

- target: `ActiveScaleCoeff * D^16(ComponentProductActual)`
- cell: `Set.Icc 0 (1/10)`
- center: `1/20`
- degree: `0`
- receiverTheorem: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17`

## Fields

- `d16CenterLower`: `None`
- `d16CenterUpper`: `None`
- `coeff0`: `None`
- `coeffErrorAbs`: `None`
- `order17Abs`: `None`
- `activeScaleAbs`: `95492965855137201461330258024/1000000000000000000000000000000`
- `polyErrorAbs`: `None`

## Budget Audit

- formula: `coeffErrorAbs + activeScaleAbs * order17Abs / 20 <= polyErrorAbs`
- `available`: `False`
- `missing`: `['coeffErrorAbs', 'order17Abs', 'polyErrorAbs']`
- `lhs`: `None`
- `rhs`: `None`
- `passed`: `None`
- `failureIfFalse`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_REMAINDER_BUDGET_CONSTANT_FAIL`

## Proof Flags

- `d16CenterProofGrade`: `False`
- `order17UniformProofGrade`: `False`
- `activeScaleProofGrade`: `True`

## Active Scale Source

- `status`: `checked`
- `kind`: `Lean`
- `path`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean`
- `theorem`: `primaryFiniteRow0Parent0Split100Sub0_activeScale_abs_bound`
- `line`: `111`
- `statement`: `|primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <= (primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound : Real)`
- `exactBoundPath`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean`
- `exactBoundDef`: `primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound`
- `exactBoundLine`: `490`
- `exactRat`: `95492965855137201461330258024/1000000000000000000000000000000`

## Failure Codes

- `missingD16OrD17`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`
- `missingD17AfterArithmeticPass`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D17_UNIFORM_SOURCE_GAP`
- `exactBudgetFalse`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_REMAINDER_BUDGET_CONSTANT_FAIL`

## Check Order

- D16 center interval
- midpoint/error
- uniform D17 bound
- active-scale multiplication
- coeffErrorAbs + activeScaleAbs * order17Abs / 20
- exact Rat comparison with polyErrorAbs

## Do Not Proceed To

- D18
- higher degree
- D46
- Lean payload emission
