# Goal 058 G3 finite-limit inertia route — Proshka verdict

Date: `2026-08-14`

Transport: same living Proshka chat, two exact UTF-8 attachments.

Observed natural reasoning: `11m04s`.

`Answer now` was shown and was not clicked.

Input packet:
`GOAL058_G3_CLASSICAL_SPECTRUM_TO_LITERAL_SCHUR_INERTIA_SOURCE_PACKET_2026-08-14.md`

Input packet SHA-256:
`2f8072b247e846641b7923974309bc76986108cf0779424c678ee878eae54f14`

Mythos verdict:
`GOAL058_G3_FINITE_LIMIT_SOURCE_FORK_MYTHOS_VERDICT_2026-08-14.md`

Mythos verdict SHA-256:
`42e98afbe8fad2e40239172620c472d464e5910dcf42593385cdcf9a6fc07f33`

Capture boundary: normalized durable capture of the visible Proshka response,
not a byte-verbatim Markdown export.  It preserves the operative class,
mathematical rulings, exact selected theorem name, bounded directive, plants,
and nonclaims.  It is an external architecture verdict, not a Lean proof.

## Primary

```yaml
STATUS: OPEN
PRIMARY: TRY_MODE4_HERMITIAN_NEGATIVE_COUNT_STABILITY
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_MODE4_HERMITIAN_NEGATIVE_COUNT_STABILITY
ROUTE_INERTIA_FINITE_LIMIT:
  verdict: ACCEPT_ARCHITECTURE_WITH_REPAIR
  finite_split_can_force_offset_zero: CONDITIONAL_ON_THREE_UNPROVED_FINITE_LEAVES
  DLMF_alone_proves_literal_Schur_count: false
  classical_to_literal_crosswalk_circular: false_if_all_seven_leaves_are_proved_independently
  endpoint_counts_2_3_proved_now: false
  upper_endpoint_le_20_preserved: true
  current_literal_consumer_preserved: true
OFFSET_ZERO:
  status: NOT_PROVED
  required:
    - exact_q0_index_and_finite_matrix_crosswalk
    - inertia_preserving_reversal_and_positive_diagonal_similarity
    - positive_finite_tail_and_Haynsworth_congruence
  forbidden:
    - assume_offset_zero
    - infer_offset_from_DLMF_limit_only
    - replace_exact_tail_Schur_by_plain_finite_truncation
SELECTED_LEAF:
  theorem: mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero
```

## Mathematical ruling

The finite-dimensional architecture is accepted in principle:

`J_d(Λ) -> S_{K,d}(Λ) -> mode4HermitianSchurMatrix(m, Λ, K)`.

If the finite tail block is positive definite, a proved Haynsworth congruence
can give exact equality between the negative count of the finite DLMF matrix
and the finite Schur complement, with no negative contribution from the
eliminated tail.  Offset zero then still requires all of the following as
independent proofs:

1. the finite DLMF matrix starts at the literal even index `q = 0`;
2. reversal and positive diagonal symmetrization preserve inertia exactly;
3. the finite Schur correction converges to the exact recessive-tail
   correction on the fixed carrier `Fin K`;
4. the limiting literal matrix is nonsingular.

DLMF 30.16.2--3 does not itself prove the literal Schur count.  It supplies
ordered finite spectral approximants with the load-bearing direction

`alpha_(p,d+1) <= alpha_(p,d)` and `alpha_(p,d) -> chi_(2(p-1))`.

Thus a strict classical separator eventually gives the classical finite
count.  The conventions `q = 0` and `p = 3 <-> n = 4` are load-bearing and
must be planted.  Equality with the literal infinite-tail Schur count still
requires the finite matrix crosswalk, positive-tail Haynsworth step,
fixed-carrier convergence, and inertia stability.

The production consumer is unchanged.  It still requires the literal
exact-tail `mode4HermitianSchurMatrix`, nonsingular endpoints satisfying
`ΛLower <= ΛUpper <= 20`, and exact negative counts `2` and `3`.  A plain
finite Jacobi truncation is not an admissible replacement.  Determinant sign
is also insufficient because it records only parity of the negative count.

## Exact selected leaf

Use the current project invariant
`mode4HermitianNegativeEigenvalueCount` and `Matrix.IsHermitian`, not the
informal `negativeCount` / `IsSymm` surface from the Mythos sketch.

For fixed `K`, prove that if Hermitian matrices `A d` converge to a Hermitian
matrix `L` and `L.det != 0`, then the project negative count of `A d` is
eventually equal to the project negative count of `L`.

This theorem assumes no DLMF result, endpoint count, root, offset, or spectral
index.  A success is infrastructure only; it does not prove an endpoint
count or close G3.

## Registered predictions

```yaml
P-INERTIA-5-1:
  prediction: the theorem is mathematically provable from finite-dimensional Hermitian spectral continuity at a nonsingular limit
  confidence: 0.95
P-INERTIA-5-2:
  prediction: the main friction is Mathlib API for continuity/local constancy of Hermitian inertia, not a missing mathematical hypothesis
  confidence: 0.80
P-INERTIA-5-3:
  prediction: determinant sign alone will be insufficient and the exact negative-count invariant must be retained
  confidence: 0.99
```

## Bounded Codex directive

```yaml
TARGET:
  G3_MODE4_HERMITIAN_NEGATIVE_COUNT_EVENTUAL_STABILITY
OPERATIVE_CLASS:
  TRY_MODE4_HERMITIAN_NEGATIVE_COUNT_STABILITY
MODE:
  - one local Lean file
  - one report
  - no Aristotle
  - no commit
  - no push
  - no route/runtime/Bus edits
SOURCE_LOCK:
  packet_sha256: 2f8072b247e846641b7923974309bc76986108cf0779424c678ee878eae54f14
  mythos_sha256: 42e98afbe8fad2e40239172620c472d464e5910dcf42593385cdcf9a6fc07f33
OWNED_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean
DIRECT_IMPORT:
  Q3.Proofs.RouteB.D0Mode4SchurInertiaOrientation
REQUIRED_PLANT:
  singular_limit_counterexample_must_fail_the_nonsingular_contract
```

## Closeout boundary

```yaml
ROUTE_INERTIA_FINITE_LIMIT: CONFIRMED_AS_ARCHITECTURE_NOT_AS_PROVED_CROSSWALK
OFFSET_ZERO: CONDITIONAL_NOT_PROVED
DLMF_MONOTONE_DIRECTION: LOAD_BEARING
GENERIC_LEAF_5: AUTHORIZED_WITH_EXACT_OBJECT_REPAIR
ENDPOINT_COUNTS_2_3: NOT_AVAILABLE
G1: OPEN
G3: OPEN
ROUTE_B_PROMOTION: FORBIDDEN
RH_CLAIM: FORBIDDEN
```
