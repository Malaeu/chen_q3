# STATUS: PROVED — BOUNDED LEAF ACCEPTED; COMMIT AND PUSH AUTHORIZED ON THE EXACT REVIEWED BYTES
```yaml
PRIMARY: ACCEPT_G3_MODE4_BACKWARD_TAIL_SCHUR_APPROX_TENDSTO_LITERAL
PRIMARY_COUNT: 1

ATTACHMENT_LOCK:
  lean_file: D0Mode4BackwardTailSchurConvergence.lean
  lean_sha256: 73a9bb01f6ce5c43df656aa2d938ec69378896a287b4a4be26de22e4e096af87
  lean_hash_verified: true
  report_file: GOAL058_G3_MODE4_BACKWARD_TAIL_SCHUR_CONVERGENCE_REPORT_2026-08-14.md
  report_sha256: c4726c39f6d6e81eeb48bfec99096a02d0c7affdb2184727eec5e4ca4acb9853
  report_hash_verified: true

SOURCE_BASE:
  expected_head: 36bee52b
  expected_origin_equal: true
  ruling_scope: EXACT_REVIEWED_BYTES_ONLY

SURFACE_AUDIT:
  direct_Q3_imports: 1
  public_definitions: 1
  public_theorems: 2
  forbidden_declarations: 0
  forbidden_proof_tokens: 0

IMPORT_RULING:
  selected_repair: IMPORT_SYMMETRIZATION_DIRECTLY
  accepted: true
  reason:
    - literal target matrix is defined in the symmetrization module
    - this leaf does not consume the accepted stability theorem
    - accepted stability leaf remains byte-unchanged
  alternative_edit_accepted_stability_import: rejected

MATHEMATICAL_AUDIT:
  fixed_carrier: proved
  sole_d_varying_entry: newest_0_0_entry
  terminal_value: 0
  all_other_entries_d_independent: true
  approximation_hermitian: proved
  matrix_tendsto_literal: proved_entrywise
  scalar_supplier:
    mode4BackwardTail_tendsto_rightTailLimit
  standard_axioms_only:
    - propext
    - Classical.choice
    - Quot.sound

BOUNDARY:
  actual_finite_DLMF_matrix_defined: false
  actual_finite_Schur_complement_identity: false
  finite_tail_posdef: false
  Haynsworth_inertia_identity: false
  offset_zero: false
  endpoint_counts_2_3: false
  G1: OPEN
  G3: OPEN
  route_promotion: false
  RH_claim: false

COMMIT_RULING:
  commit: AUTHORIZED
  push: AUTHORIZED
  branch: rh_clean
  remote: origin
  preconditions:
    - HEAD remains 36bee52b before commit
    - worktree diff contains only the two owned files
    - the reviewed SHA-256 values remain exact
    - strict startup and stated validation gates remain green
  suggested_commit_message: "[RouteB][Goal058] Prove fixed-carrier backward-tail Schur convergence"

NEXT_BOUNDED_LEAF:
  name: D0_MODE4_BACKWARD_TAIL_FINITE_SCHUR_CROSSWALK
  purpose: identify an actual finite source Jacobi truncation whose Schur complement is the accepted Approx matrix
  direct_import: Q3.Proofs.RouteB.D0Mode4BackwardTailSchurConvergence
  required_surface:
    - one source-locked finite Jacobi truncation definition
    - Hermitianity theorem for that truncation
    - conditional exact Schur-complement equality to mode4BackwardTailSchurApprox
  explicit_boundary:
    - tail invertibility may remain an explicit hypothesis
    - no tail PosDef theorem
    - no Haynsworth theorem
    - no inertia count
    - no offset zero
    - no endpoint 2/3
    - no G1 or G3 closure
    - no route promotion
    - no RH claim

SUCCESS:
  G3_MODE4_BACKWARD_TAIL_SCHUR_APPROX_TENDSTO_LITERAL_ACCEPTED

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

| Check | Verdict | Exact reason |
|---|---|---|
| Attachment hashes | **PASS** | Both supplied SHA-256 values match the exact attachment bytes. |
| Direct import | **PASS** | The Lean file has one import, `Q3.Proofs.RouteB.D0Mode4SchurHermitianSymmetrization`. |
| Import-wall repair | **PASS** | The target `mode4HermitianSchurMatrix` is needed directly; this leaf never invokes the accepted negative-count stability theorem. Editing the accepted leaf would add risk and change its accepted hash without benefit. |
| Public surface | **PASS** | Exactly one public `def` and two public `theorem` declarations occur. |
| Fixed carrier | **PASS** | The convergence map is `d ↦ Matrix (Fin K) (Fin K) ℝ`; `K` is fixed outside the approximating index. |
| Sole varying entry | **PASS** | In the definition, `d` occurs only in `mode4BackwardTail ... (n + 1) d 0`, the newest `(0,0)` entry. |
| Hermitianity | **PASS** | The proof splits the newest row and column, matches the two off-diagonal entries, and delegates the old lower-right block to `mode4HermitianLeftContinuantMatrix_isHermitian`. |
| Tendsto | **PASS** | The proof is entrywise via two `tendsto_pi_nhds` steps. The `(0,0)` branch uses `mode4BackwardTail_tendsto_rightTailLimit`; every other branch is constant and closes by simplification. |
| Terminal convention | **PASS** | The scalar supplier is instantiated at terminal value `0`, with the required membership proof for `0 ∈ Icc 0 (1/2)`. |
| Axiom boundary | **PASS FROM EXACT REPORT EVIDENCE** | Both public theorems are reported with exactly `[propext, Classical.choice, Quot.sound]`; the source contains the corresponding `#print axioms` commands. |
| Actual finite Schur boundary | **PASS** | The name is `Approx`; module and declaration documentation explicitly deny an actual finite Schur-complement identification. No finite tail block, inverse, congruence, Haynsworth theorem, or inertia result is introduced. |

## FINAL PROPOSAL

Accept the leaf exactly as submitted.

The theorem proves only:

\[
\operatorname{mode4BackwardTailSchurApprox}(d)
\longrightarrow
\operatorname{mode4HermitianSchurMatrix}
\]

on one fixed matrix carrier.

It does not prove that the approximating matrix is the Schur complement of an actual finite Jacobi truncation. That missing identity is not hidden; it is the next source-object boundary.

### Commit and push ruling

**Commit is authorized. Push to `origin/rh_clean` is authorized.**

The authorization applies only if:

1. pre-commit `HEAD` is still `36bee52b`;
2. the diff contains only:
   - `Q3/Proofs/RouteB/D0Mode4BackwardTailSchurConvergence.lean`;
   - the Goal 058 convergence report;
3. both reviewed hashes remain unchanged;
4. strict startup and the reported Lean/build/check gates remain green.

Suggested commit message:

```text
[RouteB][Goal058] Prove fixed-carrier backward-tail Schur convergence
```

### Registered prediction

For the next leaf, the exact finite Schur identity should be algebraic once the finite truncation carrier, block orientation, depth index, and terminal-zero convention are source-locked.

The likeliest first failure is an off-by-one or reversed-block convention in the newest diagonal, not an analytic convergence issue.

## STRONGEST ATTACK

The strongest objection is:

> The object called `mode4BackwardTailSchurApprox` may be only a hand-written formula that converges to the desired literal matrix; it has not been shown to arise from any actual finite DLMF Jacobi matrix.

Correct.

That objection does not invalidate this bounded leaf, because the leaf explicitly claims only Hermitianity and fixed-carrier convergence of the formula. It would invalidate any later inertia transfer that treated this formula as an actual finite Schur complement without a separate crosswalk.

The weakest necessary repair is therefore not a change to this leaf. It is the next bounded leaf below.

## CODEX DIRECTIVE

```text
NEXT TARGET:
  D0_MODE4_BACKWARD_TAIL_FINITE_SCHUR_CROSSWALK

MODE:
  one bounded leaf;
  no commit or push until separate review.

DIRECT IMPORT:
  Q3.Proofs.RouteB.D0Mode4BackwardTailSchurConvergence

PURPOSE:
  Introduce the literal finite source mode-four Jacobi truncation and prove
  that its Schur complement onto the retained `Fin K` block is exactly
  `mode4BackwardTailSchurApprox mProject Λ K d`.

REQUIRED PUBLIC SURFACE:
  1. Exactly one source-locked definition of the actual finite Jacobi truncation.
  2. One theorem proving that finite truncation is Hermitian.
  3. One theorem proving the exact Schur-complement equality.

THEOREM BOUNDARY:
  The Schur-complement equality may assume explicit invertibility of the
  eliminated finite tail block. Do not prove tail positivity in this leaf.

MANDATORY CHECKS:
  - one direct Q3 import;
  - fixed retained carrier `Fin K`;
  - exact block orientation;
  - exact depth convention;
  - exact terminal-zero convention;
  - no relabeling before the equality compiles;
  - standard-only axiom profile.

FORBIDDEN:
  - no finite-tail PosDef claim;
  - no Haynsworth inertia theorem;
  - no negative-count conclusion;
  - no offset-zero claim;
  - no endpoint counts `2/3`;
  - no G1 closure;
  - no G3 closure;
  - no Route promotion;
  - no RH claim.

SUCCESS:
  G3_MODE4_ACTUAL_FINITE_SCHUR_CROSSWALK_PROVED

FAILURE:
  G3_MODE4_FINITE_JACOBI_BLOCK_ORIENTATION_GAP
```

## META CLOSEOUT

**What became smaller?**

The convergence side is closed:

```text
finite backward-tail scalar convergence
→ fixed-carrier Hermitian matrix convergence.
```

**What was killed?**

- the need to mutate the accepted stability leaf;
- the incorrect direct import;
- any ambiguity about which matrix entry varies with depth;
- any claim that the carrier grows with depth.

**What must not be tried again?**

Do not call the accepted `Approx` an actual finite Schur complement before the exact block identity exists.

**Current smallest named gap:**

```text
D0_MODE4_BACKWARD_TAIL_FINITE_SCHUR_CROSSWALK
```

**Next cheapest decisive test:**

Define the literal finite block matrix and make its Schur-complement `(0,0)` entry reduce to the existing finite backward-tail recursion with terminal value zero.

**Fate of the import-wall prediction:**

```text
Recommended repair A:
  CONFIRMED.

Alternative repair B:
  REJECTED AS UNNECESSARY HASH-BREAKING EDIT.
```

```yaml
iteration:
  target: fixed_carrier_backward_tail_Schur_convergence
  status: PROGRESS
  failed_strategy: import_accepted_stability_leaf_for_a_target_it_does_not_export
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: D0Mode4BackwardTailFiniteSchurCrosswalk
  invariant_learned: convergence of a literal formula and actual finite Schur provenance are separate theorem obligations
  forbidden_future_move: consume inertia stability before actual finite Schur and tail-positivity bridges exist
  next_decisive_test: exact finite block Schur-complement identity
  progress_class: PROOF_PROGRESS
  route_score: 5
```
