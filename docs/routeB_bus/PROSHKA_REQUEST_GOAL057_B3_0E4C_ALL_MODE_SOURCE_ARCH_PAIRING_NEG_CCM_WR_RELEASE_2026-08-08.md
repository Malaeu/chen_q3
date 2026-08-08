# PROSHKA REQUEST — Goal 057 B3.0E4C all-mode source-archimedean pairing / CCM-WR release

Date: 2026-08-08
Route: Route B / Goal 057 / B3.0E4C
Review class: DELEGATED_STRATEGIC_REVIEW
Requested operative class: TRY_ / KILL_ / RUN_ only

## 0. Decision requested

Adjudicate the exact compiling no-`sorry` discriminator for:

`GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY`

If the theorem is a source-faithful, dependency-minimal two-case assembly of
the two already-closed parents, authorize exactly one production child.
Otherwise give the smallest exact mathematical or Lean stop code and a
repaired discriminator.

Do not authorize a complete source Weil form, an associated operator graph,
a coarse-checkpoint decrement, H4a1b, route promotion, PX or RH.

## 1. Source lock

```yaml
repo: Malaeu/chen_q3
branch: rh_clean
expected_head: 90fd2a3b6aca65e5dd9638a1ff203b0e8736c524
expected_origin_head: 90fd2a3b6aca65e5dd9638a1ff203b0e8736c524
source: arXiv:2511.22755v1
source_equations:
  - CCM equations (2.7)--(2.10)
  - CCM equation (4.4)
parent_closed:
  - B3.0E4A off-diagonal source pairing = negative CCM-WR entry
  - B3.0E4B2 diagonal source pairing = negative CCM-WR entry
parent_open:
  - B3.0E
  - B3.0
coarse_checkpoints_closed: 0
coarse_checkpoints_remaining: 10
```

The official source separates `n != r` and `n = r` in equations
(2.9)--(2.10), while equation (4.4) supplies the common archimedean entry.
The proposed theorem adds no analytic fact: it only packages those two
source-locked cases into one total statement.

## 2. Exact theorem under review

```lean
theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ) := by
  by_cases h : n = r
  · subst r
    exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag i n
  · exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne i h
```

The source pairing remains antilinear in the first slot. The theorem does not
swap the ordered indices and preserves the final negative sign in both cases.

## 3. Compiling harness

```yaml
path: q3.lean.aristotle/Goal057B3_0E4C_Scratch.lean
bytes: 1278
lines: 37
sha256: 10c6238544c172d7f9f90851eca28b8dee86271de36bb84eccebb8e8d60dfd66
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
  - Q3.Proofs.RouteB.D0PstarSourceArchDiagonalCCMWRCrosswalk
public_surface:
  definitions: 0
  theorems: 1
private_surface:
  definitions: 0
  theorems: 0
controls:
  examples: 3
  print_axioms: 1
```

## 4. Proof architecture

1. Split only on the exact source discriminator `h : n = r`.
2. In the diagonal branch, substitute `r` and apply only the closed B3.0E4B2
   theorem.
3. In the off-diagonal branch, apply only the closed B3.0E4A theorem to `h`.
4. Add no helper, definition, integral manipulation, normalization premise,
   source premise, simplification lemma or coercion bridge.

This is representation packaging, not a new source calculation.

## 5. Mandatory controls already compiled

```yaml
controls:
  - id: C057_E4C_1_CENTRAL_DIAGONAL
    object: n=0, r=0
    result: PASS
  - id: C057_E4C_2_FORWARD_OFFDIAGONAL
    object: n=0, r=1
    result: PASS
  - id: C057_E4C_3_REVERSE_OFFDIAGONAL
    object: n=1, r=0
    result: PASS
```

The two ordered off-diagonal controls are intentional because the pairing is
antilinear in its first slot. They are smoke checks, not new source evidence.

## 6. Proposed adversarial plants

Please audit, repair or expand this exact small plant set before release:

```yaml
plants:
  - id: P057_E4C_1_FINAL_WR_SIGN
    mutation: negative_ccm_wr_to_positive_ccm_wr
    required_stop: SOURCE_ARCH_ALL_MODE_WR_SIGN_MISMATCH
  - id: P057_E4C_2_DIAGONAL_BRANCH
    mutation: diagonal_parent_to_offdiagonal_parent
    required_stop: SOURCE_ARCH_ALL_MODE_DIAGONAL_BRANCH_MISSING
  - id: P057_E4C_3_OFFDIAGONAL_BRANCH
    mutation: offdiagonal_parent_to_diagonal_parent
    required_stop: SOURCE_ARCH_ALL_MODE_OFFDIAGONAL_BRANCH_MISSING
  - id: P057_E4C_4_MODE_ORDER
    mutation: ccm_entry_n_r_to_r_n
    required_stop: SOURCE_ARCH_ALL_MODE_ORDER_MISMATCH
  - id: P057_E4C_5_CASE_DISCRIMINATOR
    mutation: n_eq_r_to_n_eq_neg_r
    required_stop: SOURCE_ARCH_ALL_MODE_CASE_SPLIT_MISMATCH
changed_source_lines_per_plant: 1
```

If any plant is redundant or does not isolate the advertised error class,
replace it with the smallest exact mutation. Do not enlarge the mathematical
scope to manufacture a plant.

## 7. Proposed production contract

```yaml
create_only:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceArchAllModeCCMWRCrosswalk.lean
exact_imports_proposed:
  - Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
  - Q3.Proofs.RouteB.D0PstarSourceArchDiagonalCCMWRCrosswalk
public_surface_exact:
  - sourceArchimedeanModePairing_eq_neg_ccmWREntry
private_surface_exact:
  definitions: 0
  theorems: 0
production_must_equal_harness_minus:
  - three_control_examples
  - print_axioms_command
semantic_change: forbidden
new_premise: forbidden
source_object_change: forbidden
parent_refactor: forbidden
aristotle_submission: none
```

If the production filename should change, name one exact source-aligned
replacement. Do not authorize a vague refactor of either closed parent.

## 8. Questions for adversarial review

1. Is the exact `n = r` split source-faithful to equations (2.9)--(2.10)?
2. Does `subst r` preserve the ordered antilinear-first-slot convention?
3. Does the off-diagonal parent receive precisely the required `n != r`
   witness, without an implicit symmetry assumption?
4. Are the negative sign and ordered indices preserved in both branches?
5. Are both explicit imports honest and minimal, or should the transitive E4A
   import be removed from production?
6. Do the three controls and five proposed plants attack every load-bearing
   choice in this packaging theorem?
7. If released and validated, is the next smallest atom the complete source
   Weil form, or must a smaller finite-sum/form-carrier supplier come first?
   Name exactly one next discriminator; do not authorize it in this verdict.
8. Give the strongest argument that E4C is vacuous duplicate API, then decide
   whether that attack changes the production verdict.

## 9. Allowed outcomes

```yaml
success:
  operative_class: TRY_GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY
  success_code: GOAL057_B3_0E4C_ALL_MODE_SOURCE_ARCH_PAIRING_EQ_NEG_CCM_WR_ENTRY_PROVED
wall:
  operative_class: KILL_GOAL057_B3_0E4C_AS_STATED
  stop_code: exact_new_stop_required
repair:
  operative_class: RUN_GOAL057_B3_0E4C_REPAIRED_PREFLIGHT
  production_authorized: false
```

## 10. Immutable boundary

```yaml
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
g2_ccm: FROZEN
aristotle_submission: NONE
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

