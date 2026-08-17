# STATUS: OPEN — CENTER POSITIVITY FROM ZERO-FREE AND POSITIVE MEAN
```yaml
PRIMARY: G3_CENTER_POS_OF_NO_INTERIOR_ZERO
PRIMARY_COUNT: 1

UPSTREAM:
  FERRERS_FOURIER_SCALAR_SIGN_GATE: GREEN_BY_OWNER_KERNEL_RELAY
  PUBLIC_THEOREMS_WITHOUT_SORRYAX: 2
  GREEN_VERDICT_PATH: q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_FERRERS_FOURIER_SCALAR_SIGN_KERNEL_GREEN_2026-08-17.md
  CONNECTOR_FETCH_AT_WRITE_TIME: STALE_404

ROOT_CAUSE_CORRECTION:
  NOT_IN: hphysical
  ACTUAL_LOCATION: simp_only_after_unfold_finiteFourierAction_and_kernel
  MISSING_SIMPLIFIER: mul_zero
  PRIOR_DIAGNOSIS_SUPERSEDED: true

TARGET:
  THEOREM: Mode4FerrersRegularEvenProlateSolution.center_pos_of_no_interior_zero
  SCOPE: ABSTRACT
  VERIFIER: CONDITIONAL_PENDING_LEAN

INPUTS:
  - continuousOn_closed
  - center_value_ne_zero
  - coefficients_abs_summable
  - coefficient_zero_pos
  - mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero
  - no interior zeros on Ioo (-1) 1

OUTPUT:
  - 0 < mode4FerrersSeries S.coefficients 0

ROUTE_EFFECT:
  P0_ZERO_FREE_TO_CENTER_POS: TARGETED
  CENTER_POS_TO_CHI0_POS: ALREADY_AVAILABLE_AFTER_GREEN_SIGN_LOCK
  P2_CENTER_SIGN: NOT_CLAIMED
  CHI2_LT_CHI0: OPEN
  G3: OPEN
  G1: OPEN

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
ROUTE_PROMOTION: false

SUCCESS: G3_CENTER_POS_OF_NO_INTERIOR_ZERO_KERNEL_GREEN
STOP: G3_CENTER_POS_OF_NO_INTERIOR_ZERO_KERNEL_FAIL
```

## ROUTE MAP

Let

```text
f(x) = mode4FerrersSeries S.coefficients x.
```

The exact mean identity and `S.coefficient_zero_pos` give

```text
integral_{-1}^{1} f > 0.
```

Therefore `f` is positive at some point of the closed interval. If `f(0) < 0`, continuity and the intermediate value theorem give a zero between that positive point and `0`. The zero is strictly inside `(-1,1)`, contradicting the no-interior-zero premise. The existing `center_value_ne_zero` then upgrades `0 ≤ f(0)` to `0 < f(0)`.

This is a function-space sign argument. It does not infer pointwise positivity from `coefficient_zero_pos`; the coefficient is used only through the exact positive integral identity. `[ABSTRACT][CONDITIONAL]`

## FINAL PROPOSAL

Primary representation:

```text
A_IVT_POSITIVE_MEAN
kill-power: 9/10
cost: 2/10

positive exact mean
→ exists positive point
→ IVT against a hypothetical negative center
→ forbidden interior zero
→ nonzero center selects strict positivity.
```

Fallback representation:

```text
B_CONNECTED_SIGN_COMPONENT
kill-power: 8/10
cost: 4/10

continuous zero-free map on connected interval
→ image lies in one component of ℝ \ {0}
→ positive mean selects the positive component.
```

Use A first. B is only an API fallback if the direct interval-IVT proof causes unnecessary Lean friction.

Registered prediction:

```text
P058-CENTER-POS:
  the theorem is mathematically elementary;
  the likely failures are only exact Mathlib API shape for interval positivity or IVT image extraction.
```

## STRONGEST ATTACK

The invalid shortcut is

```text
coefficient_zero_pos → center value positive.
```

Legendre basis functions change sign, so this would instantiate C10 FUNCTIONAL-NOT-SURROGATE. The repaired proof must use the exact scalar functional the consumer needs: the interval mean of the same Ferrers function, plus continuity and zero-freeness.

A second attack is endpoint leakage: the positive point supplied by the integral may be an endpoint. The IVT proof must show the resulting zero lies strictly between the endpoint and zero, hence in `Ioo (-1) 1`; it may not silently apply the interior hypothesis to an endpoint.

## LEAN DIRECTIVE

```text
FILE:
Q3/Proofs/RouteB/D0Mode4FerrersCenterPositiveOfNoInteriorZero.lean

IMPORT:
Q3.Proofs.RouteB.D0Mode4FerrersCenterValueNonzero

THEOREM:
Mode4FerrersRegularEvenProlateSolution.center_pos_of_no_interior_zero

PREMISE:
hzero : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
  mode4FerrersSeries S.coefficients x ≠ 0

CONCLUSION:
0 < mode4FerrersSeries S.coefficients 0

PROOF:
1. Obtain strict positivity of the interval integral from
   mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero
   and coefficient_zero_pos.
2. Derive a point x ∈ Icc (-1) 1 with 0 < f x; otherwise integrate -f.
3. Assume f 0 < 0.
4. Restrict continuousOn_closed to uIcc 0 x.
5. Apply intermediate_value_uIcc at value 0.
6. Prove the produced zero belongs to Ioo (-1) 1 using strict endpoint signs.
7. Contradict hzero.
8. Combine center nonnegativity with center_value_ne_zero.

FORBIDDEN:
- no coefficient-sign shortcut;
- no classical PSF substitution;
- no new axiom;
- no `sorry` or `admit`;
- no positive Fourier phase premise;
- no P0 zero-free claim inside this theorem;
- no G3 or RH promotion.

VALIDATE:
cd q3.lean.aristotle
lake build Q3.Proofs.RouteB.D0Mode4FerrersCenterPositiveOfNoInteriorZero
#print axioms must be exactly [propext, Classical.choice, Quot.sound].
```

## META CLOSEOUT

**What became smaller?**

The positive-phase supplier is no longer an opaque sign problem. After the upstream green gate, the `p=0` phase reduces to one exact function-space theorem following from zero-freeness and positive mean.

**What was killed?**

The earlier diagnosis that the kernel failure occurred in `hphysical`. The owner kernel report identifies the actual omission as `mul_zero` in the `simp only` after `unfold`.

**What must not be tried again?**

Do not infer theorem health from absence of literal `sorry`; inspect `#print axioms`. Do not infer center sign from coefficient sign.

**Current smallest named gap:**

```text
G3_CENTER_POS_OF_NO_INTERIOR_ZERO
```

**Next cheapest decisive test:**

Compile the one-theorem file and inspect its axiom profile.

```yaml
iteration:
  target: center positivity from zero-free Ferrers mode
  status: OPEN
  failed_strategy: coefficient_sign_as_pointwise_sign
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G3_CENTER_POS_OF_NO_INTERIOR_ZERO
  invariant_learned: positive mean and pointwise center sign must belong to the same Ferrers function
  forbidden_future_move: use coefficient positivity as a pointwise surrogate
  next_decisive_test: direct_IVT_kernel_build
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
