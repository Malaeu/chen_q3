# STATUS: PROVED — BOUNDED ACTUAL FINITE SCHUR CROSSWALK ACCEPTED
```yaml
PRIMARY: ACCEPT_G3_MODE4_ACTUAL_FINITE_SCHUR_CROSSWALK
PRIMARY_COUNT: 1

ATTACHMENT_LOCK:
  lean_file: D0Mode4BackwardTailFiniteSchurCrosswalk.lean
  lean_sha256_expected: c8866f89a138ba2d4b4ea76c4a2178dec4c5d62b522684c70a1649ab3c64990d
  lean_sha256_observed: c8866f89a138ba2d4b4ea76c4a2178dec4c5d62b522684c70a1649ab3c64990d
  lean_hash_verified: true

  report_file: GOAL058_G3_MODE4_BACKWARD_TAIL_FINITE_SCHUR_CROSSWALK_REPORT_2026-08-14.md
  report_sha256_expected: 2e56b8998f25b8117b24ec11e4bfa9c3c97d520e18b05851ac348cd7628bf0fb
  report_sha256_observed: 2e56b8998f25b8117b24ec11e4bfa9c3c97d520e18b05851ac348cd7628bf0fb
  report_hash_verified: true

SOURCE_BASE:
  required_parent: fdb7b60f
  branch: rh_clean
  remote: origin

SURFACE_AUDIT:
  direct_Q3_imports: 1
  public_definitions: 1
  public_theorems: 2
  public_structures: 0
  public_axioms: 0
  forbidden_tokens: 0

MATHEMATICAL_AUDIT:
  carrier: Fin_K_sum_Fin_d
  retained_carrier_fixed: true
  retained_order: reversed
  retained_coordinate_zero: q_equals_K_minus_1
  tail_order: q_equals_K_through_K_plus_d_minus_1
  sole_cross_block_edge: retained_0_to_tail_0
  cross_block_coefficient: minus_mode4JacobiSymmetricOff_G_K_minus_1
  terminal_convention: zero
  hermitianity: proved
  conditional_exact_schur_identity: proved
  proof_mechanism:
    - finite_tail_minor_identity
    - exact_two_step_determinant_recurrence
    - recursive_nonzero_pivot_to_determinant_nonzero
    - backward_tail_as_suffix_det_over_full_det
    - Matrix_inv_def
    - Matrix_adjugate_fin_succ_eq_det_submatrix
    - Matrix_single_mul_mul_single
    - mode4JacobiSymmetricOff_sq
  d_zero_boundary: proved_separately

AXIOM_PROFILE:
  mode4ActualFiniteJacobiTruncation_isHermitian:
    - propext
    - Classical.choice
    - Quot.sound
  mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx:
    - propext
    - Classical.choice
    - Quot.sound
  project_axioms: none
  sorryAx: absent

BOUNDARY:
  finite_tail_PosDef: false
  Haynsworth_or_inertia_additivity: false
  finite_negative_count: false
  offset_zero: false
  endpoint_counts_2_3: false
  G1: OPEN
  G3: OPEN
  route_promotion: false
  RH_claim: false

API_CAVEAT:
  private_pivot_predicate_exposed_in_public_theorem: true
  fatal_for_this_leaf: false
  required_next_repair:
    derive_and_hide_private_pivots_under_public_separation_hypotheses

COMMIT_RULING:
  commit_authorized: true
  push_authorized: true
  authorization_scope: exact_reviewed_attachment_bytes_only
  preconditions:
    - HEAD_equals_fdb7b60f_before_commit
    - origin_rh_clean_equals_fdb7b60f_before_commit
    - only_two_owned_paths_in_diff
    - both_SHA256_values_unchanged
    - direct_Lean_target_full_q3check_strict_startup_remain_green
  suggested_commit_message: "[RouteB][Goal058] Prove actual finite backward-tail Schur crosswalk"

NEXT_BOUNDED_LEAF:
  id: D0_MODE4_BACKWARD_TAIL_FINITE_TAIL_POSDEF
  owned_file: Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean
  direct_import: Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteSchurCrosswalk
  purpose:
    - prove_the_actual_eliminated_tail_block_PosDef
    - derive_the_recursive_nonzero_pivots
    - expose_a_public_schur_identity_without_the_private_pivot_premise
  no_Haynsworth: true
  no_inertia_count: true

SUCCESS:
  G3_MODE4_ACTUAL_FINITE_SCHUR_CROSSWALK_ACCEPTED

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

| Audit item | Verdict | Reason |
|---|---|---|
| Attachment bytes | **PASS** | Both independently recomputed SHA-256 values exactly match the requested locks. |
| Direct Q3 import | **PASS** | The Lean source has exactly one import: `Q3.Proofs.RouteB.D0Mode4BackwardTailSchurConvergence`. |
| Public surface | **PASS** | Declaration scan gives exactly one non-private `def` and exactly two non-private `theorem`s. |
| Literal carrier | **PASS** | The public matrix type is `Matrix (Fin K ⊕ Fin d) (Fin K ⊕ Fin d) ℝ`. |
| Retained orientation | **PASS within attachment boundary** | The definition uses the accepted reversed `mode4HermitianLeftContinuantMatrix`; the splice is at retained coordinate `0` and is indexed by `K-1`. |
| Tail orientation | **PASS** | The recursive tail starts with center `K`, then recurses at `K+1`; its coordinates are therefore `K,...,K+d-1` in forward order. |
| Cross-block support | **PASS** | `mode4RetainedTailCoupling` is nonzero only when `i.val=0 ∧ j.val=0`. |
| Cross-block value | **PASS** | Its sole value is `-mode4JacobiSymmetricOff G (K-1)`. |
| Terminal zero | **PASS** | The final finite row has no outgoing edge; the Schur formula is identified with `mode4BackwardTail ... d 0`. |
| Hermitianity | **PASS** | The retained and tail blocks are Hermitian, and the off-diagonal blocks are `B` and `Bᴴ`. |
| Exact Schur identity | **PASS** | The public theorem concludes the literal block Schur complement equals the existing `mode4BackwardTailSchurApprox`. |
| Genuine algebra | **PASS** | The proof builds the finite determinant recurrence, derives determinant nonvanishing from recursive pivots, identifies `(D⁻¹)₀₀` through adjugate/determinant algebra, and collapses the rank-one coupling. |
| Axioms | **PASS from exact report evidence** | The report records both public theorem profiles as exactly `[propext, Classical.choice, Quot.sound]`, with all validation gates green. |
| Positivity/inertia boundary | **PASS** | No tail positivity, Haynsworth identity, negative count, offset, endpoint count, G1/G3 closure, promotion, or RH theorem appears. |

The report locks the exact split orientation, public surface, conditional pivot interface, determinant/adjugate proof spine, green validation, standard-only axiom surface, and all required nonclaims. fileciteturn52file2 fileciteturn52file10

I independently inspected the exact Lean attachment. Its executable structure agrees with that report:

- the tail matrix is recursively forward-indexed;
- the retained-tail coupling is a single `(0,0)` matrix entry;
- the actual matrix is assembled with `Matrix.fromBlocks A B B.conjTranspose D`;
- the `d=0` case is handled separately;
- the positive-depth case uses determinant recurrences and `Matrix.inv_def`;
- no forbidden proof token or new axiom declaration occurs.

I did not independently rerun the 7,817-job build. The build and axiom outputs are accepted as exact-byte evidence from the supplied report, as requested.

## FINAL PROPOSAL

### Primary verdict

\[
\boxed{\texttt{ACCEPT\_G3\_MODE4\_ACTUAL\_FINITE\_SCHUR\_CROSSWALK}}
\]

This leaf closes exactly the previously open provenance statement:

> the terminal-zero backward-tail approximation is the genuine Schur complement of the literal finite Hermitian Jacobi truncation, conditional on explicit recursive nonzero elimination pivots.

It is not merely a convergent hand-written approximation anymore.

### Commit and push ruling

**Commit is authorized. Push to `origin/rh_clean` is authorized.**

The ruling applies only to these exact bytes:

```text
Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteSchurCrosswalk.lean
SHA-256:
c8866f89a138ba2d4b4ea76c4a2178dec4c5d62b522684c70a1649ab3c64990d
```

```text
ACTIVE/requests/routeB_lamport_rh_closure/
GOAL058_G3_MODE4_BACKWARD_TAIL_FINITE_SCHUR_CROSSWALK_REPORT_2026-08-14.md
SHA-256:
2e56b8998f25b8117b24ec11e4bfa9c3c97d520e18b05851ac348cd7628bf0fb
```

Required pre-commit conditions:

```text
HEAD = origin/rh_clean = fdb7b60f
git diff contains only the two owned paths
both hashes remain exact
strict startup remains green
direct Lean remains green
target build remains green
full build remains green
q3_check remains green
```

Suggested commit message:

```text
[RouteB][Goal058] Prove actual finite backward-tail Schur crosswalk
```

Any byte change or different parent requires a new review.

## STRONGEST ATTACK

The strongest surviving objection is not mathematical falsity. It is the public API seam:

> `mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx` exposes the private predicate `mode4FiniteTailPivotsNonzero` in its public type.

The report calls this a private interface honestly. The current theorem remains valid and exactly bounded. But downstream production must not pretend the separation inequality has already discharged it.

The next leaf must therefore do two things together:

1. prove positive definiteness of the actual eliminated tail block under the existing production separation inequality and `Λ ≤ 20`;
2. derive the recursive pivot nonvanishing internally and expose a public Schur identity with no private-predicate premise.

This is not a repair to the accepted mathematics. It is the smallest usability and positivity bridge required before finite block inertia can legally consume the crosswalk.

A second attack is simpler:

> Hermitianity plus invertibility does not imply positive definiteness.

Correct. Therefore Haynsworth and “zero negative tail contribution” remain unavailable. The report preserves that boundary exactly. fileciteturn52file10

## CODEX DIRECTIVE

```text
NEXT TARGET:
  D0_MODE4_BACKWARD_TAIL_FINITE_TAIL_POSDEF

OWNED FILE:
  Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean

DIRECT IMPORT:
  Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteSchurCrosswalk

MODE:
  one bounded leaf
  no commit or push until separate review

PURPOSE:
  Prove positive definiteness of the actual eliminated finite tail block under
  the existing production separation inequality, and seal the current private
  pivot interface.

PUBLIC THEOREM 1:
  theorem mode4ActualFiniteJacobiTruncation_tailBlock_posDef
      (mProject K d : ℕ) (Λ : ℝ)
      (hm : 2 ≤ mProject)
      (hK : 3 ≤ K)
      (hsep :
        ∀ q ≥ K,
          (31 / 24 : ℝ) * mode4JacobiG mProject ≤
            mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
      (hΛ : Λ ≤ 20) :
      (mode4ActualFiniteJacobiTruncation
        mProject Λ K d).toBlocks₂₂.PosDef

PUBLIC THEOREM 2:
  theorem
    mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation
      (mProject K d : ℕ) (Λ : ℝ)
      (hm : 2 ≤ mProject)
      (hK : 3 ≤ K)
      (hsep :
        ∀ q ≥ K,
          (31 / 24 : ℝ) * mode4JacobiG mProject ≤
            mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
      (hΛ : Λ ≤ 20) :
      let M :=
        mode4ActualFiniteJacobiTruncation mProject Λ K d
      M.toBlocks₁₁ -
          M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁ =
        mode4BackwardTailSchurApprox mProject Λ K d

PROOF ROUTE:
  1. Reduce `toBlocks₂₂` to the exact finite forward tail.
  2. Prove strict positivity by the existing source separation inequality.
  3. Cover `d=0` explicitly.
  4. Derive positivity/nonvanishing of every suffix pivot.
  5. Invoke the accepted conditional Schur theorem internally.
  6. Do not expose the private pivot predicate in the new public surface.

MANDATORY PLANTS:
  P1:
    Attempt to derive PosDef from Hermitianity alone.
    Required rejection:
      MODE4_FINITE_TAIL_HERMITIAN_NOT_POSDEF.

  P2:
    Drop the production separation hypothesis.
    Required rejection:
      MODE4_FINITE_TAIL_SEPARATION_MISSING.

  P3:
    Replace `Λ ≤ 20` by no spectral upper bound.
    Required rejection:
      MODE4_FINITE_TAIL_LAMBDA_UPPER_MISSING.

  P4:
    Reverse the forward tail order or move the splice away from `(0,0)`.
    Required rejection:
      MODE4_FINITE_TAIL_ORIENTATION_MISMATCH.

VALIDATION:
  lake env lean \
    Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean

  lake build \
    Q3.Proofs.RouteB.D0Mode4BackwardTailFiniteTailPosDef

  lake build

  bash scripts/q3_check.sh \
    q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean

  git diff --check

  #print axioms on both public theorems

EXPECTED AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  G3_MODE4_FINITE_TAIL_POSDEF_AND_PUBLIC_SCHUR_CROSSWALK_PROVED

FAILURE:
  G3_MODE4_FINITE_TAIL_POSDEF_GAP
  G3_MODE4_PRIVATE_PIVOT_INTERFACE_NOT_DISCHARGED
  G3_MODE4_FINITE_TAIL_ORIENTATION_MISMATCH
  LEAN_BUILD_FAIL

FORBIDDEN:
  no Haynsworth theorem
  no inertia additivity
  no negative-count result
  no offset-zero result
  no endpoint counts 2/3
  no G1 closure
  no G3 closure
  no Route promotion
  no RH claim
```

## META CLOSEOUT

**What became smaller?**

The prior gap

```text
hand-written finite approximation
versus
actual finite Schur complement
```

is closed.

**What was killed?**

- the “Approx has no finite source provenance” objection;
- any need to infer the Schur formula from numerical convergence;
- any ambiguity about the sole retained-tail coupling;
- any ambiguity about the terminal-zero finite boundary.

**What must not be tried again?**

Do not use the conditional Schur identity as if finite-tail positivity or inertia additivity had already been proved.

**Current smallest named gap:**

```text
D0_MODE4_BACKWARD_TAIL_FINITE_TAIL_POSDEF
```

**Next cheapest decisive test:**

Prove the exact eliminated tail block `PosDef` under the existing separation inequality and `Λ ≤ 20`, including the `d=0` boundary.

**Fate of the prior registered prediction:**

```text
"The actual finite Schur identity should be algebraic once carrier,
orientation, depth and terminal zero are locked":

CONFIRMED.
```

```yaml
iteration:
  target: actual_finite_backward_tail_Schur_crosswalk
  status: PROGRESS
  failed_strategy: none
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: D0Mode4BackwardTailFiniteTailPosDef
  invariant_learned: finite Schur provenance, tail positivity, and inertia transfer are three separate theorem obligations
  forbidden_future_move: consume Haynsworth before the eliminated tail is proved PosDef
  next_decisive_test: finite_tail_PosDef_under_production_separation
  progress_class: PROOF_PROGRESS
  route_score: 5
```
