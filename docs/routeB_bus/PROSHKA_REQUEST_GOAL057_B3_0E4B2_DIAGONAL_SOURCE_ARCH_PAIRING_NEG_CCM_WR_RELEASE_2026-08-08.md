# PROSHKA REQUEST — Goal 057 B3.0E4B2 diagonal source-archimedean pairing / CCM-WR release

Date: 2026-08-08  
Route: Route B / Goal 057 / B3.0E4B2  
Review class: DELEGATED_STRATEGIC_REVIEW  
Requested operative class: TRY_ / KILL_ / RUN_ only

## 0. Decision requested

Adjudicate the exact compiling no-`sorry` discriminator for:

`GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY`

If the theorem, source normalization, Fubini architecture, endpoint assembly,
dependency surface and plants are source-faithful, authorize exactly one
production child. Otherwise give the smallest exact mathematical or Lean stop
code and a repaired discriminator.

Do not authorize an all-mode theorem in this transaction, a source Weil form,
an associated operator graph, a coarse-checkpoint decrement, H4a1b, route
promotion, PX or RH.

## 1. Source lock

```yaml
repo: Malaeu/chen_q3
branch: rh_clean
expected_head: 4d92a827ce50538866a287705747d918becb2ca5
expected_origin_head: 4d92a827ce50538866a287705747d918becb2ca5
source: arXiv:2511.22755v1
source_equations:
  - CCM equations (2.7)--(2.10)
  - CCM equation (4.4)
parent_closed:
  - B3.0D source archimedean mode-pairing kernel
  - B3.0E1 source regularized hyperbolic kernel
  - B3.0E2 joint L1/Fubini carrier
  - B3.0E3 zero-extended mode correlation / CCM Q-kernel
  - B3.0E4A off-diagonal source pairing = negative CCM-WR entry
  - B3.0E4B1 diagonal scalar endpoint ledger
parent_open:
  - B3.0E
  - B3.0
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
```

The source pairing is antilinear in the first slot.  On the diagonal the
compact-support correlation has exact value

```text
q_nn(x) = 2 * (L-x)/L * cos(2*pi*n*x/L),
q_nn(0) = 2.
```

CCM equation (4.4) is

```text
W_R(V_n,V_n)
  = gamma + log(4*pi*(exp(L)-1)/(exp(L)+1))
    + integral_0^L
      (exp(x/2)*q_nn(x)-2)/(exp(x)-exp(-x)) dx.
```

The exact source multiplier and the preceding Fourier convention therefore
predict the negative of this entry.

## 2. Exact theorem under review

```lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag
    (i : PairIndex) (n : ℤ) :
    sourceArchimedeanModePairing i n n =
      -(Q3.RouteB.ccmWREntry (L_m i) n n : ℂ)
```

This theorem is diagonal only.  It neither restates nor silently subsumes the
already-proved off-diagonal theorem.

## 3. Compiling harness

```yaml
path: q3.lean.aristotle/Goal057B3_0E4B2_Scratch.lean
bytes: 19477
lines: 469
sha256: 02dfe2fcc0166c833ff04104fcafe64db513d8f8a4219117c1665ab20fe367d4
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
imports_exact:
  - Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
  - Q3.Proofs.RouteB.D0PstarSourceArchDiagonalRegularizerEndpointLedger
public_surface:
  definitions: 0
  theorems: 1
private_surface:
  definitions: 5
  theorems: 13
  total: 18
controls:
  examples: 4
  print_axioms: 1
```

A dependency audit removed an explicit
`Mathlib.MeasureTheory.Integral.Prod` import; the harness still compiles with
the same theorem and exact standard axiom triple.  Product integration enters
honestly through the closed E4A parent.

## 4. Proof architecture

1. Reconstruct the already-used fixed-mode `L2 × L2 -> L1` carrier locally;
   this is needed because E4A helpers are private, not because a new analytic
   premise is introduced.
2. Derive the bare diagonal mass `integral conj(F_n)*F_n = 1` from the public
   E3 control theorem whose exact statement is twice that integral equals two.
3. For every `x > 0`, integrate the E1 regularized kernel over frequency.
   The public E3 theorem supplies the exact cosine correlation on
   `0 <= x <= L`, and zero beyond `L`.
4. Preserve the exact piecewise fiber ledger:

```text
2 * fiber(x)
  = ccmWRIntegrand(L,n,n,x)
      + 2*(1-exp(-x))/(exp(x)-exp(-x))       when 0 < x <= L,
  = -2*exp(-x)/(exp(x)-exp(-x))             when x > L.
```

5. Use only the public E2 joint absolute-integrability theorem to justify the
   Fubini swap and integrability of the outer ledger.
6. Split `Ioi 0` as `Ioc 0 L` union `Ioi L`.  The singleton `L` belongs to the
   finite side, matching the `x <= L` source support.
7. Apply the already-proved E4B1 scalar identity to combine `-log(pi)`, the
   paired finite regularizer and the positive tail into the exact
   `-log(4*pi*(exp(L)-1)/(exp(L)+1))` endpoint.
8. The remaining `-EulerGamma` and negative CCM-WR integral close the target
   by algebra only.

No desired pairing value, CCM-WR equality, diagonal integral, or new source
normalization is assumed as a premise.

## 5. Mandatory controls already compiled

```yaml
controls:
  - id: C057_E4B2_1_CENTRAL_DIAGONAL
    object: n=0 final pairing theorem
    result: PASS
  - id: C057_E4B2_2_NONCENTRAL_DIAGONAL
    object: n=1 final pairing theorem
    result: PASS
  - id: C057_E4B2_3_SUPPORT_BOUNDARY
    object: x=L exact finite-side fiber ledger
    result: PASS
  - id: C057_E4B2_4_OUTSIDE_SUPPORT
    object: x=L+1 exact negative-tail fiber ledger
    result: PASS
```

## 6. Mandatory plants already executed

Each plant was streamed through Lean via stdin.  No mutation file or generated
artifact was written to the repository.

```yaml
plants:
  - id: P057_E4B2_1_FINAL_WR_SIGN
    mutation: negative_ccm_wr_to_positive_ccm_wr
    required_stop: SOURCE_ARCH_DIAGONAL_WR_SIGN_MISMATCH
    result: FIRED
  - id: P057_E4B2_2_BARE_MODE_MASS
    mutation: diagonal_mass_one_to_zero
    required_stop: SOURCE_ARCH_DIAGONAL_MODE_NORMALIZATION_MISMATCH
    result: FIRED
  - id: P057_E4B2_3_FIBER_FACTOR_TWO
    mutation: twice_fiber_to_single_fiber
    required_stop: SOURCE_ARCH_DIAGONAL_CORRELATION_FACTOR_MISMATCH
    result: FIRED
  - id: P057_E4B2_4_FINITE_REGULARIZER_SIGN
    mutation: finite_regularizer_plus_to_minus
    required_stop: SOURCE_ARCH_DIAGONAL_FINITE_REGULARIZER_SIGN_MISMATCH
    result: FIRED
  - id: P057_E4B2_5_TAIL_SIGN
    mutation: negative_fiber_tail_to_positive
    required_stop: SOURCE_ARCH_DIAGONAL_TAIL_SIGN_MISMATCH
    result: FIRED
  - id: P057_E4B2_6_SPLIT_BOUNDARY
    mutation: tail_Ioi_L_to_Ioi_L_plus_one
    required_stop: SOURCE_ARCH_DIAGONAL_SPLIT_BOUNDARY_MISMATCH
    result: FIRED
  - id: P057_E4B2_7_EULER_GAMMA
    mutation: drop_euler_gamma_from_pairing_constant
    required_stop: SOURCE_ARCH_DIAGONAL_GAMMA_MISSING
    result: FIRED
  - id: P057_E4B2_8_DIAGONAL_INDEX
    mutation: pairing_second_index_n_to_n_plus_one
    required_stop: SOURCE_ARCH_DIAGONAL_INDEX_MISMATCH
    result: FIRED
changed_source_lines_per_plant: 1
unexpected_passes: 0
```

## 7. Proposed production contract

```yaml
create_only:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchDiagonalCCMWRCrosswalk.lean
exact_imports_proposed:
  - Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
  - Q3.Proofs.RouteB.D0PstarSourceArchDiagonalRegularizerEndpointLedger
public_surface_exact:
  - sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag
private_ceiling:
  definitions: 5
  theorems: 13
  total: 18
production_must_equal_harness_minus:
  - four_control_examples
  - print_axioms_command
semantic_change: forbidden
new_premise: forbidden
source_object_change: forbidden
parent_refactor: forbidden
aristotle_submission: none
```

If the private ceiling should be reduced before production, name the exact
helper or existing public theorem that replaces it.  Do not authorize a vague
refactor of the closed parents.

## 8. Questions for adversarial review

1. Does the displayed piecewise fiber ledger have the exact finite and tail
   signs, including the outer factor two?
2. Is deriving diagonal mass one from the public E3 `2*integral=2` theorem
   source-faithful, or does it conceal a Fourier normalization mismatch?
3. Is the E2 joint integrability theorem sufficient for both Fubini directions
   used here, with the exact `volume.prod (volume.restrict (Ioi 0))` measure?
4. Is assigning `x=L` to `Ioc 0 L` and the strict tail to `Ioi L` exact?
5. Does E4B1 combine precisely the extra finite regularizer and tail produced
   by the diagonal fiber, without double-counting the CCM-WR integrand?
6. Are the two Route-B imports an honest minimal dependency surface?
7. Do the eight plants and four controls attack every load-bearing premise?
8. If released and validated, is the next smallest atom an all-mode assembly
   theorem combining E4A and E4B2, or must another source-locked supplier come
   first?  Do not authorize that next atom in this verdict.
9. Give the strongest argument that E4B2 is only packaging, then decide
   whether that attack changes the production verdict.

## 9. Allowed outcomes

```yaml
success:
  operative_class: TRY_GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
  success_code: GOAL057_B3_0E4B2_DIAGONAL_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED
wall:
  operative_class: KILL_GOAL057_B3_0E4B2_AS_STATED
  stop_code: exact_new_stop_required
repair:
  operative_class: RUN_GOAL057_B3_0E4B2_REPAIRED_PREFLIGHT
  production_authorized: false
```

## 10. Immutable boundary

```yaml
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
aristotle_submission: NONE
all_mode_crosswalk: NOT_AUTHORIZED
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
