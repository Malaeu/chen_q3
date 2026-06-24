# Step33A.1-A ActiveActual Order-16 Degree-0 Preflight

schema: `q3_psdpd_step33_a1_sub0_active_actual_order16_degree0_payload.v5`
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
- `order17Abs`: `1024379792916537436656292891459584/152587890625`
- `activeScaleAbs`: `95492965855137201461330258024/1000000000000000000000000000000`
- `polyErrorAbs`: `None`

## Budget Audit

- formula: `coeffErrorAbs + activeScaleAbs * order17Abs / 20 <= polyErrorAbs`
- `available`: `False`
- `missing`: `['coeffErrorAbs', 'polyErrorAbs']`
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

## Order17 Uniform Route

- `selectedRoute`: `B_rawProduct18`
- `selectedBy`: `Browser/Computer Use Proshka review`
- `bridge`: `{'status': 'checked', 'kind': 'Lean', 'path': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Payload.lean', 'equalityTheorem': 'primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18', 'absTransferTheorem': 'primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_abs', 'meaning': 'D^17(ComponentProductActual) is reduced to D^18(RawProductActual)', 'stillMissing': 'proof-grade uniform source for D^18(RawProductActual) on Set.Icc 0 (1/10)', 'failureIfMissing': 'STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_RAW_PRODUCT18_UNIFORM_SOURCE_GAP'}`
- `majorantReceiver`: `{'status': 'checked', 'kind': 'Lean', 'path': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18MajorantReceiver.lean', 'majorantDef': 'primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant', 'rawProductTheorem': 'primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs', 'componentTransferTheorem': 'primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_factor_derivative_abs', 'meaning': 'conditional Leibniz receiver from Omega/ShapeSq derivative bounds 0..18 to the D18(RawProductActual) majorant', 'stillMissing': [], 'failureIfMissing': 'STEP33_A1_SUB0_RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP'}`
- `omegaPrimeOrder17AnalyticSource`: `{'status': 'checked', 'kind': 'Lean', 'path': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17Payload.lean', 'theorem': 'Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_tsum', 'analyticMajorantDef': 'Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TsumAbs', 'meaning': 'proof-grade analytic order-17 OmegaPrime domination by a tsum majorant; not yet a rational/interval uniform budget', 'stillMissing': ['STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP'], 'failureIfMissing': 'STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP'}`
- `omegaPrimeOrder17RationalSource`: `{'status': 'checked', 'path': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17RationalPayload.lean', 'payload': 'ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_order17_payload.json', 'order17Abs': '1024379792916537436656292891459584/152587890625', 'failureIfMissing': 'STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP'}`
- `shapeSqOrder18Source`: `{'status': 'checked', 'kind': 'Lean', 'realSincOrder18Path': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaARealSincDerivativeOrder18Payload.lean', 'realSincFin19SupportPath': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaARealSincDerivativeCert19.lean', 'path': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqOrder18Payload.lean', 'realSincOrder18Theorem': 'primaryFiniteRow0Parent0Split100Sub0_realSinc_iteratedDeriv18_norm_le_two', 'realSincThrough18Theorem': 'primaryFiniteRow0Parent0Split100Sub0_realSinc_derivative_abs_through18', 'shapeSqOrder18Theorem': 'primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_abs_of_sharp', 'shapeSqThrough18Theorem': 'primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18', 'meaning': 'proof-grade ShapeSqActual derivative source through k <= 18 for the RawProduct18 Leibniz receiver', 'stillMissing': [], 'failureIfMissing': 'STEP33_A1_SUB0_SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP'}`
- `requiredUniformSource`: `forall eta in Set.Icc 0 (1/10), |D^18(RawProductActual)(eta)| <= order17Abs`
- `remainingFactorSources`: `[]`
- `notClosedByBridgeAlone`: `True`

## Failure Codes

- `missingD16OrD17`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`
- `missingD17AfterArithmeticPass`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D17_UNIFORM_SOURCE_GAP`
- `missingRawProduct18UniformSource`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_RAW_PRODUCT18_UNIFORM_SOURCE_GAP`
- `missingRawProduct18LeibnizReceiver`: `STEP33_A1_SUB0_RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP`
- `missingOmegaPrimeOrder17Source`: `STEP33_A1_SUB0_OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP`
- `missingOmegaPrimeOrder17RationalTailPayload`: `STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP`
- `missingShapeSqOrder18Source`: `STEP33_A1_SUB0_SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP`
- `exactBudgetFalse`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_REMAINDER_BUDGET_CONSTANT_FAIL`

## Check Order

- D16 center interval
- midpoint/error
- uniform D17 bound
- active-scale multiplication
- coeffErrorAbs + activeScaleAbs * order17Abs / 20
- exact Rat comparison with polyErrorAbs

## Do Not Proceed To

- higher degree beyond the selected RawProduct18 D17-uniform route
- higher degree
- D46
- Lean payload emission
