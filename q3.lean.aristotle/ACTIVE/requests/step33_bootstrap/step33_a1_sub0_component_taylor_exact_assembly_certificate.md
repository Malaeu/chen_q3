# Step33A.1-A sub0 exact assembly coefficient certificate

- schema: `q3_psdpd_step33_a1_sub0_component_taylor_exact_assembly_certificate.v1`
- status: `algebraic_assembly_payload_checked_remainder_source_open`
- firstFailure: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- proofGrade: `LEAN_LIST_EQ_CHECKED_FOR_ALGEBRAIC_COEFFICIENT_ARRAYS_ONLY`

## Lean Payload

- path: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`
- assembledPayloadDef: `primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeffPayload`
- residualPayloadDef: `primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffPayload`
- assembledEqTheorem: `primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_payload_eq`
- residualEqTheorem: `primaryFiniteRow0Parent0Split100Sub0_residualTaylorCoeff_payload_eq`
- validationStatus: `direct_lean_checked`
- q3CheckStatus: `hung_after_internal_lean_command_interrupted`

## Checks

- `assembledLength`: `46`
- `residualLength`: `46`
- `algebraicAssemblyCrosswalkPassed`: `True`
- `exactCoefficientAssemblyPassed`: `False`
- `componentTaylorProofsPresent`: `False`
- `residualTaylorRemainderAbsPresent`: `False`
- `componentTaylorOverallProofSafe`: `False`

## Boundary

- do not set exactCoefficientAssemblyPassed=true
- do not treat coefficient arrays as an analytic approximation proof
- do not invent residualTaylorRemainderAbs from the final product budget
- do not hide the open ShapeSqDeriv rows 2..15/order16 blocker
