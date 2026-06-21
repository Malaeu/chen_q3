# Step33A.1-A Sub0 OmegaPrime Taylor Payload

Fail-closed payload surface. This is not Lean proof data and does
not close Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_omega_prime_taylor_payload.v10`
- route: `STEP33_A1_SUB0_OMEGA_PRIME_TAYLOR_PAYLOAD`
- status: `fail_closed_tail_bound_checked_missing_prefix_exact_lean_proof`
- first failure: `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PREFIX_EXACT_LEAN_PROOF_GAP`
- receiver schema current: `True`
- function: `step22OmegaArchWeightDerivClosedForm`
- center: `1/20`
- radius: `1/20`
- degree: `15`
- center-jet prefixN: `128`
- proof-safe closed fields: `0`
- rational prefix/tail rows generated: `16`
- Lean emitted: `False`

## Target Lean Surface

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean`
- structure: `Step33Sub0OmegaPrimeTaylorRemainderCert`
- valid predicate: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid`
- bound theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound`
- centered bridge theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound`
- left bridge theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_left_of_order16_bound`
- right bridge theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_right_of_order16_bound`
- valid constructor: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound`
- OmegaPrime smoothness theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_contDiff16`
- checked-smooth valid constructor: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound_checked_smooth`
- active payload receiver: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_integer_budget_checked_deriv`
- receiver checked: `True`
- old receiver rejected for new payloads: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound_checked_smooth`
- reflected derivative theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_reflected_iteratedDeriv`
- Taylor exact-poly theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.taylorWithinEval_eq_exactTaylorPoly`
- reflected Taylor exact-poly theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.reflectedTaylorWithinEval_eq_exactTaylorPoly`
- trigamma-series prefix-tail theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries_iteratedDeriv_sub_prefix_norm_le_shifted_tsum_majorant_of_le16`
- OmegaPrime closed-form prefix-tail theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_iteratedDeriv_sub_prefix_norm_le_half_shifted_tsum_majorant_of_le16`
- center-jet prefix-tail theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_centerJet_invFactorial_sub_prefix_norm_le_shifted_tsum_majorant_of_le16`
- center-jet prefix-tail checked: `True`
- shifted-tail generated-bound theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeCenterJet_shifted_tsum_budget_le_generated_bound_of_le15`
- shifted-tail generated-bound checked: `True`
- status: `receiver_checked_deriv_tail_bound_checked_missing_prefix_exact_lean_proof`

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound {data : Step33Sub0OmegaPrimeTaylorRemainderCert} (h : data.Valid) : forall eta in Set.Icc 0 (1/10), norm (step22OmegaArchWeightDerivClosedForm eta - data.poly eta) <= data.remainderAbs
```

Next constructor surface:

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_integer_budget_checked_deriv (data : Step33Sub0OmegaPrimeTaylorRemainderCert) (hCoeffErrorNonneg : forall j, 0 <= data.coeffErrorAbs j) (hCenterJet : center coefficient enclosures) (hIntegerBudget : omegaPrimeOrder16CondensedFactorBudgetBound <= data.order16Abs) (hRemainderBudget : coefficient plus Lagrange budget <= data.remainderAbs) : data.Valid
```

Normalization note:

`rawOmegaATaylorPolynomial expects a Rat center and a Fin (degree + 1) -> Rat coefficient function.`

## Required Fields

- `coeff[0..15]`
- `coeffErrorAbs[0..15]`
- `centerJet[0..15].{coeff,coeffErrorAbs,lower,upper,prefixN,prefixExactRational,shiftedTailUpperRational,prefixLeanChecked,tailBoundLeanChecked,centerJetMargin,sourceLeanTheorem,sourceLeanChecked,lowerCheckPassed,upperCheckPassed,enclosurePassed}`
- `centerJetPrefixTailRows[0..15].{jetIndex,prefixN,prefixExactRational,shiftedTailUpperRational,coeff,coeffErrorAbs,prefixLeanChecked,tailBoundLeanChecked,centerJetMargin,sourceLeanTheorem,proofGrade}`
- `order16Abs`
- `order16.{condensedFactorBudgetBoundExact,order16Abs,marginExact,integerBudgetPassed,sourceLeanTheorems,sourceLeanChecked}`
- `remainder.{coeffErrorContributionExact,lagrangeContributionExact,requiredTotalExact,remainderAbs,marginExact,budgetPassed}`
- `remainderAbs`
- `centerJetSource[0..15]`
- `integerBudgetSource`
- `exactRationalChecksPassed`
- `sourceDefinitionHashes`
- `allCenterJetsProved`
- `allPayloadObligationsPassed`
- `leanOutputPath`
- `leanValidationStatus`
- `proofSafeClosedFields`
- `outLeanWritten`
- `failureCodes[]`

## Generated Center-Jet Prefix/Tail Rows

Full exact rationals are in the JSON artifact.  This table keeps the
Markdown readable while preserving proof status.

| j | prefixN | coeff digits | coeffErrorAbs | tail checked | margin | proofGrade |
| --- | --- | --- | --- | --- | --- | --- |
| `0` | `128` | `2866` | `2/509` | `True` | `0` | `False` |
| `1` | `128` | `4306` | `4/259081` | `True` | `0` | `False` |
| `2` | `128` | `5732` | `8/131872229` | `True` | `0` | `False` |
| `3` | `128` | `7176` | `16/67122964561` | `True` | `0` | `False` |
| `4` | `128` | `8600` | `32/34165588961549` | `True` | `0` | `False` |
| `5` | `128` | `10045` | `64/17390284781428441` | `True` | `0` | `False` |
| `6` | `128` | `11474` | `128/8851654953747076469` | `True` | `0` | `False` |
| `7` | `128` | `12915` | `256/4505492371457261922721` | `True` | `0` | `False` |
| `8` | `128` | `14346` | `512/2293295617071746318664989` | `True` | `0` | `False` |
| `9` | `128` | `15783` | `1024/1167287469089518876200479401` | `True` | `0` | `False` |
| `10` | `128` | `17212` | `2048/594149321766565107986044015109` | `True` | `0` | `False` |
| `11` | `128` | `18650` | `4096/302422004779181639964896403690481` | `True` | `0` | `False` |
| `12` | `128` | `20082` | `8192/153932800432603454742132269478454829` | `True` | `0` | `False` |
| `13` | `128` | `21521` | `16384/78351795420195158463745325164533507961` | `True` | `0` | `False` |
| `14` | `128` | `22949` | `32768/39881063868879335658046370508747555552149` | `True` | `0` | `False` |
| `15` | `128` | `24391` | `65536/20299461509259581849945602588952505776043841` | `True` | `0` | `False` |

Row proof boundary:

- `prefixExactRational` and `shiftedTailUpperRational` are exact
  rational generator output.
- `tailBoundLeanChecked = True` means the shifted-tail formula is
  now backed by a checked Lean theorem.
- `prefixLeanChecked = False`, so these rows are not proof-grade
  center-jet enclosures yet.

## Required Proofs

- already proved locally: the full centered Taylor bridge centerTaylorBridge_of_order16_bound from a uniform order-16 bound on [0, 1/10]
- already proved locally: the left reflected Lagrange bridge centerTaylorBridge_left_of_order16_bound and the reflected Taylor polynomial normalization
- already proved locally: the right-half Lagrange bridge centerTaylorBridge_right_of_order16_bound with the sharp 16! denominator on eta in [1/20, 1/10]
- already proved locally: taylorWithinEval agrees with exactTaylorPoly under UniqueDiffOn and global ContDiff 16
- already proved locally: reflected iterated derivative identity iteratedDeriv n (fun x => f (1/10 - x)) x = (-1)^n * iteratedDeriv n f (1/10 - x)
- already proved locally: trigamma is analytic in the right half-plane and step22OmegaArchWeightDerivClosedForm is ContDiff Real 16
- already proved locally: Valid.of_order16_integer_budget_checked_deriv uses omegaPrimeClosedForm_iteratedDeriv16_eq, so generated payloads no longer need to supply hSmooth or hDerivEq
- already proved locally: the OmegaPrime center-jet prefix-tail bridge reduces each j < 16 center-jet enclosure to an exact finite prefix plus a shifted-tail rational upper bound
- already proved locally: for m < 16, the shifted-tail majorant budget is bounded by the generated denominator-form coeffErrorAbs formula
- for each j < 16, prove the exact finite prefix rational equality for the generated prefixExactRational / coeff[j]
- for each j < 16, prove 0 <= coeffErrorAbs[j] and close centerJetMargin with the prefix-tail bridge plus checked tail bound
- prove omegaPrimeOrder16CondensedFactorBudgetBound <= order16Abs
- prove sum_j coeffErrorAbs[j] * radius^j + order16Abs * radius^16 / 16! <= remainderAbs

## Local Source Scan


### Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean

| symbol | line | status |
| --- | --- | --- |
| `rawOmegaATaylorPolynomial` | `30` | `found` |
| `digamma_analyticAt_of_re_pos` | `6446` | `found` |
| `trigamma_differentiableAt_of_re_pos` | `6470` | `found` |
| `trigamma_analyticAt_of_re_pos` | `6484` | `found` |
| `step22OmegaArchWeightDerivClosedForm` | `6440` | `found` |
| `step22OmegaArchWeightDerivClosedForm_differentiableAt` | `6499` | `found` |
| `step22OmegaArchWeightDerivClosedForm_contDiff16` | `6532` | `found` |
| `step22OmegaArchWeight_deriv_eq_closedForm` | `8493` | `found` |
| `Step22OmegaClosedFormEndpointBoundsCert` | `8623` | `found` |
| `ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound` | `12252` | `found` |

### Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean

| symbol | line | status |
| --- | --- | --- |
| `step33_shift16_digamma_m6_integral_remainder_bound` | `842` | `found` |
| `Q3.digammaM6IntegralRemainderBound` | `843` | `found` |

## Target Symbol Scan

| symbol | line | status |
| --- | --- | --- |
| `Step33Sub0OmegaPrimeTaylorRemainderCert` | `9634` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid` | `10069` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound` | `12032` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound` | `10051` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_left_of_order16_bound` | `9911` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_right_of_order16_bound` | `9810` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound` | `10098` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_contDiff16` | `9647` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound_checked_smooth` | `10132` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_integer_budget_checked_deriv` | `11939` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_reflected_iteratedDeriv` | `9654` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.taylorWithinEval_eq_exactTaylorPoly` | `9683` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.reflectedTaylorWithinEval_eq_exactTaylorPoly` | `9759` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaSeries_iteratedDeriv_sub_prefix_norm_le_shifted_tsum_majorant_of_le16` | `10859` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_iteratedDeriv_sub_prefix_norm_le_half_shifted_tsum_majorant_of_le16` | `10914` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_centerJet_invFactorial_sub_prefix_norm_le_shifted_tsum_majorant_of_le16` | `10949` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeCenterJet_shifted_tsum_budget_le_generated_bound_of_le15` | `11288` | `found` |
| `STEP33_A1_SUB0_OMEGAPRIME_STALE_RECEIVER_SCHEMA_FAIL` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SHIFTED_TAIL_RATIONAL_PAYLOAD_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PREFIX_EXACT_LEAN_PROOF_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_CENTERED_TAYLOR_LAGRANGE_SPLIT_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_LEFT_REFLECTED_LAGRANGE_BRIDGE_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_TAYLOR_WITHINEVAL_EXACT_POLY_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_RIGHT_LAGRANGE_BRIDGE_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP` | `None` | `gap` |

## Proof Status

- componentTaylorBoundsProved: `False`
- centeredTaylorBridgeProved: `True`
- centeredTaylorRightBridgeProved: `True`
- centeredTaylorLeftReflectedBridgeProved: `True`
- validOfOrder16ConstructorProved: `True`
- taylorWithinEvalExactPolyBridgeProved: `True`
- reflectedTaylorWithinEvalExactPolyBridgeProved: `True`
- reflectedIteratedDerivBridgeProved: `True`
- omegaPrimeAnalyticSmoothnessProved: `True`
- validCheckedSmoothConstructorProved: `True`
- omegaPrimeHDerivEqProved: `True`
- validIntegerBudgetCheckedDerivConstructorProved: `True`
- omegaPrimeOrder16AnalyticBoundReducedToIntegerBudget: `True`
- omegaPrimeCenterJetPrefixTailBridgeProved: `True`
- omegaPrimeCenterJetShiftedTailGeneratedBoundProved: `True`
- omegaPrimeCenterJetBoundsProved: `False`
- omegaPrimeOrder16BoundProved: `False`
- omegaPrimeOrder16IntegerBudgetProved: `False`
- omegaPrimeRemainderBudgetPassed: `False`
- exactRationalChecksPassed: `True`
- allCenterJetsProved: `False`
- allPayloadObligationsPassed: `False`
- leanValidationStatus: `not_run`
- proofSafeClosedFields: `0`
- rationalPrefixTailRowsGenerated: `16`
- outLeanWritten: `False`

## Failure Codes

- `STEP33_A1_SUB0_OMEGAPRIME_STALE_RECEIVER_SCHEMA_FAIL`
- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PREFIX_EXACT_LEAN_PROOF_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP`

## Parent Failure Codes

- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SHIFTED_TAIL_RATIONAL_PAYLOAD_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_GAP`

## Closed Historical Failures

- `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP`
- `STEP33_A1_SUB0_CENTERED_TAYLOR_LAGRANGE_SPLIT_GAP`
- `STEP33_A1_SUB0_LEFT_REFLECTED_LAGRANGE_BRIDGE_GAP`
- `STEP33_A1_SUB0_TAYLOR_WITHINEVAL_EXACT_POLY_GAP`
- `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP`
- `STEP33_A1_SUB0_RIGHT_LAGRANGE_BRIDGE_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SHIFTED_TAIL_LEAN_PROOF_GAP`

## Decision

The checked-deriv receiver and the center-jet prefix-tail bridge
are now the active Lean surface:
`Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_integer_budget_checked_deriv`.
`Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_centerJet_invFactorial_sub_prefix_norm_le_shifted_tsum_majorant_of_le16`.
The old order-16 polygamma failure is historical, and the broad
`CENTER_JET_PAYLOAD_GAP` is now only the parent blocker. The next
proof-producing step is a concrete
`Step33Sub0OmegaPrimeTaylorRemainderCert` payload with per-jet
`prefixN`, exact finite-prefix rationals, shifted-tail rational
upper bounds, center-jet margins, the integer order-16 budget,
and the exact rational Taylor remainder budget.

Until those payload fields exist locally, the correct fail code is:

```text
STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PREFIX_EXACT_LEAN_PROOF_GAP
```
