# PROSHKA REQUEST — Goal 057 B3.0F finite archimedean sesquilinear matrix-form lift release

Date: 2026-08-08
Route: Route B / Goal 057 / B3.0F
Review class: DELEGATED_STRATEGIC_REVIEW
Requested operative class: TRY_ / KILL_ / RUN_ only

## 0. Decision requested

Adjudicate the exact compiling no-`sorry` discriminator for:

`GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT`

If the theorem is the source-faithful, dependency-minimal finite coefficient
lift of the already-closed all-mode B3.0E4C theorem, authorize exactly one
production child. Otherwise give the smallest exact mathematical or Lean stop
code and one repaired discriminator.

Do not authorize W02 or prime source pairings, the complete source Weil form,
an associated operator graph, a coarse-checkpoint decrement, H4a1b, route
promotion, PX or RH.

## 1. Source lock

```yaml
repo: Malaeu/chen_q3
branch: rh_clean
expected_head: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
expected_origin_head: c22a4a9ca4e00f1f0443ef3509705bb9eda91082
source: arXiv:2511.22755v1
source_equations:
  - Hilbert pairing convention before equation (2.1)
  - polarization formula (3.9)
  - Weil-form ledger (3.10)
  - source matrix definition (4.1)
  - archimedean entry (4.4)
  - finite restriction and matrix (5.1)--(5.2)
parent_closed:
  - B3.0E4C all-mode source-archimedean pairing = negative CCM-WR entry
  - B3.0E source-archimedean / CCM-WR crosswalk
parent_open:
  - B3.0
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
```

The official source fixes the Hilbert pairing as antilinear in the first
argument and linear in the second. It obtains the Weil form by polarization
and represents the finite restriction by the source matrix on the ordered
mode basis. Therefore the coefficient form must be `star (c j) * A j k * d k`.

## 2. Exact theorem under review

```lean
theorem sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourceArchimedeanModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      -(∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWREntry
            (L_m i)
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) : ℂ) *
          d k) := by
  classical
  simp [sourceArchimedeanModePairing_eq_neg_ccmWREntry]
```

Only parenthesization changes are admissible. The carrier, ordered mode map,
coefficient slots, conjugation and global sign are part of the theorem.

## 3. Compiling harness

```yaml
path: q3.lean.aristotle/Goal057B3_0F_Scratch.lean
bytes: 2678
lines: 106
sha256: b1060045cf6cf22939ef04b45f324d7ab0af380fe920cb275bcc3f6623b56e95
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
  - Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
public_surface:
  definitions: 0
  theorems: 1
private_surface:
  definitions: 0
  theorems: 0
controls:
  examples: 4
  print_axioms: 1
```

The first compile attempt intentionally exposed that E4C does not re-export
the finite carrier. The direct source-matrix import is therefore load-bearing,
not decorative.

## 4. Proof architecture

1. Quantify over exactly `c d : CCMModeFinite i.N → ℂ`.
2. Use the literal ordered map `ccmModeFinite i.N j = j - i.N` in both slots.
3. Keep `star (c j)` in the first slot and `d k` linear in the second.
4. Rewrite only by the closed E4C theorem at each `(j,k)` entry.
5. Pull the common negative sign through the two finite sums.
6. Add no source-form definition, matrix symmetry argument, real projection,
   new premise, W02 term, prime term or operator wrapper.

This is a finite sesquilinear packaging theorem, not a new analytic result.

## 5. Mandatory controls already compiled

```yaml
controls:
  - id: C057_F_1_EXACT_CONTRACT
    object: arbitrary i,c,d; exact theorem statement reapplied
    result: PASS
  - id: C057_F_2_FIRST_SLOT_ANTILINEAR
    object: c -> a • c
    expected: form(a • c,d) = star(a) * form(c,d)
    result: PASS
  - id: C057_F_3_SECOND_SLOT_LINEAR
    object: d -> a • d
    expected: form(c,a • d) = a * form(c,d)
    result: PASS
  - id: C057_F_4_MODE_MAP_LITERAL
    object: arbitrary N,j
    expected: ccmModeFinite N j = (j.1 : ℤ) - N
    result: PASS
```

The scaling controls are algebraic convention checks. The exact-contract
control is intentionally retained when a theorem-statement mutation is run,
so an equally mutated left/right pair cannot pass unnoticed.

## 6. Proposed adversarial plants

Please audit, repair or expand this exact set before release:

```yaml
plants:
  - id: P057_F_1_GLOBAL_WR_SIGN
    mutation: outer_negative_removed
    required_stop: SOURCE_ARCH_FINITE_FORM_GLOBAL_SIGN_MISMATCH
  - id: P057_F_2_FIRST_SLOT_STAR
    mutation: star_c_j_to_c_j_in_theorem_only
    required_stop: SOURCE_ARCH_FINITE_FORM_FIRST_SLOT_ANTILINEARITY_MISMATCH
  - id: P057_F_3_SECOND_SLOT_STAR
    mutation: star_c_j_to_star_d_k_and_d_k_to_c_j_in_theorem_only
    required_stop: SOURCE_ARCH_FINITE_FORM_SLOT_CONJUGATION_MISMATCH
  - id: P057_F_4_SOURCE_MODE_ORDER
    mutation: source_pairing_second_mode_k_to_j_in_theorem_only
    required_stop: SOURCE_ARCH_FINITE_FORM_MODE_ORDER_MISMATCH
  - id: P057_F_5_FINITE_CARRIER
    mutation: coefficient_carrier_i_N_to_i_N_plus_one
    required_stop: SOURCE_ARCH_FINITE_FORM_CARRIER_MISMATCH
  - id: P057_F_6_PARENT_PROVENANCE
    mutation: replace_E4C_consumption_by_all_form_hypothesis
    required_stop: SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
  - id: P057_F_7_REAL_PROJECTION
    mutation: complex_form_to_real_part_form
    required_stop: SOURCE_ARCH_FINITE_FORM_COMPLEX_CARRIER_LOST
  - id: P057_F_8_DEPENDENCY
    mutation: inject_direct_Aristotle_or_generated_PSD_import
    required_stop: ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK
changed_source_lines_per_plant: minimal
```

Candidate plant `swap j and k everywhere` is probably symmetry-blind because
`ccmWREntry` is real symmetric and the double sum can be reindexed. Do not
count it merely because it looks like an orientation attack. Kill it or name
one exact observable replacement.

## 7. Proposed production contract

```yaml
create_only:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchFiniteFormCCMWRCrosswalk.lean
exact_imports_proposed:
  - Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
  - Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
public_surface_exact:
  - sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
private_surface_exact:
  definitions: 0
  theorems: 0
production_must_equal_harness_minus:
  - four_control_examples
  - print_axioms_command
semantic_change: forbidden
new_premise: forbidden
source_object_change: forbidden
parent_refactor: forbidden
aristotle_submission: none
```

If the production filename should change, name one exact source-aligned
replacement. Do not authorize a vague refactor of E4C or the finite source
matrix module.

## 8. Questions for adversarial review

1. Does the theorem preserve the source's antilinear-first convention exactly?
2. Is `CCMModeFinite i.N` with `ccmModeFinite i.N j = j-N` the correct finite
   restriction for this source object?
3. Is rewriting by E4C under both finite sums sufficient and dependency-minimal?
4. Does the global negative sign sit outside the complete double sum with no
   hidden sign change in coefficient multiplication?
5. Is the direct finite-source-matrix import honest and necessary?
6. Are the four controls and eight proposed plants independent and observable?
7. Must the global `j <-> k` plant be killed as symmetry-blind, or can it be
   repaired without enlarging the theorem?
8. Give the strongest argument that this theorem is vacuous duplicate API,
   then decide whether it is nevertheless the necessary source-locked bridge
   for the next complete Weil-form assembly.
9. If released and validated, name exactly one next smallest discriminator.
   Do not authorize it in this verdict.

## 9. Allowed outcomes

```yaml
success:
  operative_class: TRY_GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT
  success_code: GOAL057_B3_0F_FINITE_ARCHIMEDEAN_SESQUILINEAR_FORM_MATRIX_LIFT_PROVED
wall:
  operative_class: KILL_GOAL057_B3_0F_AS_STATED
  stop_code: exact_new_stop_required
repair:
  operative_class: RUN_GOAL057_B3_0F_REPAIRED_PREFLIGHT
  production_authorized: false
```

## 10. Immutable boundary

```yaml
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
aristotle_submission: NONE
w02_source_pairing: OPEN
prime_source_pairing: OPEN
complete_source_weil_form: OPEN
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
