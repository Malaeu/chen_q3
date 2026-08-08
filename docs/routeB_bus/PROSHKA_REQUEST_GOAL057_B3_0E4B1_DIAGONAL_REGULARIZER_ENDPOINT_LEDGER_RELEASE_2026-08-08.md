# PROSHKA REQUEST — Goal 057 B3.0E4B1 diagonal regularizer endpoint ledger release

Date: 2026-08-08  
Route: Route B / Goal 057 / B3.0E4B1  
Review class: DELEGATED_STRATEGIC_REVIEW  
Requested operative class: TRY_ / KILL_ / RUN_ only

## 0. Decision requested

Adjudicate the exact compiling no-`sorry` discriminator for:

`GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER`

If the theorem, proof architecture, dependency surface and plants are
source-faithful, authorize exactly one production child. Otherwise give the
smallest exact mathematical or Lean stop code and a repaired discriminator.

Do not authorize B3.0E4B2, an all-mode crosswalk, a source Weil form, an
associated operator graph, a coarse-checkpoint decrement, H4a1b, promotion,
PX or RH.

## 1. Source lock

```yaml
repo: Malaeu/chen_q3
branch: rh_clean
expected_head: 2b57a33f04ee09a865fa4186064afa48645b211d
expected_origin_head: 2b57a33f04ee09a865fa4186064afa48645b211d
source: arXiv:2511.22755v1
source_equation: CCM equation (4.4)
parent_closed:
  - B3.0E1 source regularized hyperbolic kernel
  - B3.0E2 joint L1/Fubini carrier
  - B3.0E3 zero-extended mode correlation / CCM Q-kernel
  - B3.0E4A off-diagonal source pairing = negative CCM-WR entry
parent_open:
  - B3.0E
  - B3.0
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
```

The primary source states

```text
W_R(V_n,V_m)
  = omega(0)/2 *
      (gamma + log(4*pi*(exp(L)-1)/(exp(L)+1)))
    + integral_0^L
      (exp(x/2)*omega(x)-omega(0))/(exp(x)-exp(-x)) dx.
```

B3.0E4A used the off-diagonal case `omega(0)=0`. The present atom
isolates the scalar cancellation that survives on the diagonal. It does not
yet contain the mode-dependent diagonal correlation.

## 2. Exact theorem under review

```lean
theorem sourceArchimedeanDiagonalRegularizer_endpointLedger
    (L : ℝ) (hL : 0 < L) :
    -Real.log Real.pi -
        (∫ x in Set.Ioc 0 L,
          2 * (1 - Real.exp (-x)) /
            (Real.exp x - Real.exp (-x))) +
        (∫ x in Set.Ioi L,
          2 * Real.exp (-x) /
            (Real.exp x - Real.exp (-x))) =
      -Real.log
        (4 * Real.pi *
          ((Real.exp L - 1) / (Real.exp L + 1)))
```

The finite-region numerator must remain paired. Splitting the two terms near
zero is forbidden because that replaces a removable cancellation by
separately divergent expressions.

## 3. Compiling harness

```yaml
path: q3.lean.aristotle/Goal057B3_0E4B1_Scratch.lean
bytes: 6852
lines: 174
sha256: a7bdb27c58288d64b239d877b14de291719b394c8688850d5ad493755aea0a4c
direct_lean: PASS
forbidden_tokens:
  sorry: 0
  admit: 0
  exact_question: 0
  unsafe: 0
  axiom_declarations: 0
axioms:
  - propext
  - Classical.choice
  - Quot.sound
imports:
  - Mathlib.MeasureTheory.Integral.IntegralEqImproper
public_surface:
  definitions: 0
  theorems: 1
private_surface:
  definitions: 2
  theorems: 5
  total: 7
```

A temporary dependency audit deleted the former Route-B parent import. The
harness still compiled with the same theorem and exact standard axiom triple.
Thus the proof is scalar and does not conceal a transitive Route-B theorem.

## 4. Proof architecture

1. On `Ioc 0 L`, prove the cancellation-preserving identity
   `2*(1-exp(-x))/(exp(x)-exp(-x)) = 2/(exp(x)+1)`.
2. Use the global primitive
   `F(x)=2*x-2*log(exp(x)+1)` and interval FTC.
3. For the tail use
   `G(x)=log(1-exp(-2*x))`.
4. On `Ici L`, prove
   `G'(x)=2*exp(-x)/(exp(x)-exp(-x)) >= 0`.
5. Prove `G(x) -> 0` at `atTop` and use
   `integral_Ioi_of_hasDerivAt_of_nonneg'`.
6. Combine only source-locked positive log arguments and the exact
   `4*pi*(exp(L)-1)/(exp(L)+1)` orientation.

No desired integral identity is assumed as a premise.

## 5. Mandatory plants already executed

All mutations were made only in temporary copies. No mutation artifact entered
the repository.

```yaml
plants:
  - id: P057_E4B1_1_TAIL_SIGN
    mutation: plus_tail_to_minus_tail
    required_stop: SOURCE_DIAGONAL_ENDPOINT_TAIL_SIGN_MISMATCH
    result: FIRED
  - id: P057_E4B1_2_TAIL_FACTOR_TWO
    mutation: tail_factor_2_to_1
    required_stop: SOURCE_DIAGONAL_ENDPOINT_TAIL_FACTOR_MISMATCH
    result: FIRED
  - id: P057_E4B1_3_PAIRED_REGULARIZER
    mutation: one_minus_exp_neg_to_one_plus_exp_neg
    required_stop: SOURCE_DIAGONAL_REGULARIZATION_CANCELLATION_DROPPED
    result: FIRED
  - id: P057_E4B1_4_COMMON_BOUNDARY
    mutation: tail_Ioi_L_to_Ioi_L_plus_one
    required_stop: SOURCE_DIAGONAL_ENDPOINT_SPLIT_BOUNDARY_MISMATCH
    result: FIRED
  - id: P057_E4B1_5_LOG_RATIO
    mutation: exp_minus_over_exp_plus_to_reciprocal
    required_stop: SOURCE_DIAGONAL_ENDPOINT_LOG_RATIO_ORIENTATION_MISMATCH
    result: FIRED
  - id: P057_E4B1_6_ENDPOINT_SCALE
    mutation: four_pi_to_two_pi
    required_stop: SOURCE_DIAGONAL_ENDPOINT_SCALE_MISMATCH
    result: FIRED
  - id: P057_E4B1_7_POSITIVE_LENGTH
    mutation: positive_L_to_negative_L
    required_stop: SOURCE_DIAGONAL_ENDPOINT_LOG_DOMAIN_MISSING
    result: FIRED
changed_source_lines_per_plant: 1
diff_lines_per_plant: 2
unexpected_passes: 0
```

## 6. Proposed production contract

```yaml
create_only:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchDiagonalRegularizerEndpointLedger.lean
exact_imports_proposed:
  - Mathlib.MeasureTheory.Integral.IntegralEqImproper
public_surface_exact:
  - sourceArchimedeanDiagonalRegularizer_endpointLedger
private_ceiling:
  definitions: 2
  theorems: 5
  total: 7
production_must_equal_harness_minus:
  - print_axioms_command
semantic_change: forbidden
new_premise: forbidden
source_object_change: forbidden
aristotle_submission: none
```

If a Route-B import is required only for namespace or discoverability, say so
explicitly; do not silently widen dependencies.

## 7. Questions for adversarial review

1. Is the displayed scalar identity exactly the cancellation needed to pass
   from the B3.0E1 regularized representation to the logarithmic endpoint in
   CCM (4.4), including both signs and the factor `4*pi`?
2. Does the proof accidentally totalize or cross a bad log domain despite
   `0 < L`?
3. Is the `Ioc 0 L` / `Ioi L` split source-faithful, including the missing
   singleton at `L`?
4. Is one Mathlib import an honest production dependency surface?
5. Do the seven plants attack every load-bearing premise, or must one be
   replaced?
6. If released and validated, is the next smallest atom exactly
   `GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY`?
7. Give the strongest argument that B3.0E4B1 is packaging rather than genuine
   progress, and decide whether that attack changes the verdict.

## 8. Allowed outcomes

```yaml
success:
  operative_class: TRY_GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER
  success_code: GOAL057_B3_0E4B1_DIAGONAL_REGULARIZER_ENDPOINT_LEDGER_PROVED
wall:
  operative_class: KILL_GOAL057_B3_0E4B1_AS_STATED
  stop_code: exact_new_stop_required
repair:
  operative_class: RUN_GOAL057_B3_0E4B1_REPAIRED_PREFLIGHT
  production_authorized: false
```

## 9. Immutable boundary

```yaml
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
aristotle_submission: NONE
b3_0e4b2: NOT_AUTHORIZED
source_weil_form: OPEN
associated_operator_graph: OPEN
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
h4a1b: OPEN
route_promotion: false
px_rh_claim: NOT_MADE
owner_action_required: false
sole_owner_gate: PX_RH_CLAIM
same_living_chat: true
answer_now_must_not_be_clicked: true
```
