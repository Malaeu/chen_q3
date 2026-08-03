# Goal 051 — M1: PosDef-self-adjoint ⇒ real spectrum (H2b keystone)

ISSUED: 2026-08-03, conductor-CLI on owner's order, from litreview formula cards.
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen untouched
NUMBERING: 051. Supersedes the tentative verbal reservation "051=hRm-canon / 052=habs"
  from the 048-numbering-reconciliation — those Müntz-supplier follow-ups are lower
  priority; M1 is the active H2b/roof frontier. hRm-canon/habs take the next free
  numbers when issued.
ADDRESSED TO: PROSHKA first (verify the math plan below is correct, complete, and
  closes with NO gap), THEN Codex formalizes on her kill-pass. Owner approval per action.

## WHY THIS IS THE KEYSTONE

The H2b real-zero engine is Connes–van Suijlekom (arXiv:2511.23257). Q3 mirrors its
FINITE §5 route (bypassing the C*-algebra §2 and the Carathéodory–Fejér Toeplitz
corollary — confirmed in CVS_H2B_FORMALIZATION_BRIDGE.md). That §5 route needs ONE
linear-algebra keystone (M1) that we do NOT yet have welded:

  D self-adjoint w.r.t. a POSITIVE-DEFINITE form Q  ⇒  D has REAL spectrum.

Our scaffold already has `zerosRealOn_of_hermitian_charpoly_mul` (docs/routeB_bus/
HermitianDeterminantRealZeros.lean:31) but it demands a GENUINELY Hermitian matrix
(`hM : M.IsHermitian`). CvS's D is NOT Hermitian in the standard inner product — it is
self-adjoint w.r.t. Q. M1 bridges that gap.

## TARGET THEOREM (to formalize; Proshka may sharpen the statement)

```lean
-- D self-adjoint w.r.t. a positive-definite Q (i.e. Qᴴ D = Dᴴ Q, Q Hermitian PosDef)
-- ⇒ D is similar to a Hermitian matrix, hence charpoly D has all-real roots.
theorem posDefSelfAdjoint_charpoly_zerosReal
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q D : Matrix n n ℂ) (hQ : Q.PosDef) (hSA : Qᴴ * D = Dᴴ * Q) :
    ∃ H : Matrix n n ℂ, H.IsHermitian ∧ H.charpoly = D.charpoly
```

(Consumer form: feed the resulting `H.IsHermitian` + `charpoly` equality into the
existing `zerosRealOn_of_hermitian_charpoly_mul` to obtain `ZerosRealOn Set.univ` of
the CvS finite approximant. Proshka: confirm this is the right consumer coupling and
whether the hypothesis should be `Qᴴ*D = Dᴴ*Q` or the equivalent `Q*D = Dᴴ*Q` with Q
Hermitian — the inertia/self-adjointness convention is exactly what must be pinned.)

## MATH PROOF PLAN (6 steps) — VERBATIM SOURCE EXCERPTS for Proshka to verify

All excerpts from Horn & Johnson, *Matrix Analysis*, 2nd ed. (2013),
pdfs/horn_johnson_matrix_analysis_2013.pdf (see M1_MATRIX_FORMULA_CARDS.md for the
full verbatim cards; theorem numbers below are what Proshka should re-check).

Step 1 — Q PosDef ⇒ Q = S² with S Hermitian PosDef (symmetric square root).
  Horn–Johnson **Theorem 7.2.6** (positive semidefinite k-th root; k=2 ⇒ unique
  Hermitian PosDef square root A^{1/2}). Lean: `Matrix.PosDef.sqrt` / `PosSemidef.sqrt`.
  (Preferred over Cholesky Cor 7.2.9 because S stays HERMITIAN, so the conjugation
  below is manifestly Hermitian — the M1-agent's tactical note.)

Step 2 — Form H := S D S⁻¹ (S invertible since PosDef).
  Similarity by an invertible matrix.

Step 3 — H is Hermitian.
  From hSA: Qᴴ D = Dᴴ Q with Q = S² (S Hermitian, Sᴴ=S). Then S² D = Dᴴ S²
  ⇒ S D S⁻¹ = S⁻¹ Dᴴ S = (S D S⁻¹)ᴴ. I.e. H = Hᴴ.
  (Proshka: this algebra is the CRUX — verify Hᴴ = (S D S⁻¹)ᴴ = S⁻ᴴ Dᴴ Sᴴ = S⁻¹ Dᴴ S
   and that S² D = Dᴴ S² gives S⁻¹ Dᴴ S = S D S⁻¹. Uses Sᴴ=S, S invertible.)

Step 4 — H (Hermitian) has real eigenvalues.
  Horn–Johnson **Theorem 4.1.3(b)** (Hermitian ⇒ real eigenvalues). Lean:
  `Matrix.IsHermitian.eigenvalues` are real / `spectrum_eq_image_range` (already used
  inside `zerosRealOn_of_hermitian_charpoly_mul`).

Step 5 — Similar matrices have the same characteristic polynomial.
  Horn–Johnson **Theorem 1.3.3 + Corollary 1.3.4(a)** (similarity ⇒ same char poly /
  eigenvalues). Lean: `Matrix.charpoly` similarity invariance
  (`Matrix.charpoly_conjugate` / `IsConj`).
  ⇒ D.charpoly = H.charpoly, and H.IsHermitian ⇒ D.charpoly roots are real.

Step 6 — Weld to the existing consumer.
  Supply `H.IsHermitian` and `hfactor` to `zerosRealOn_of_hermitian_charpoly_mul`
  (HermitianDeterminantRealZeros.lean:31): its `hM.spectrum_eq_image_range` step
  consumes exactly `IsHermitian` to conclude real zeros of the CvS approximant `F`.

Supporting primitives (available, per M1 cards, if a sub-step needs them):
  - Sylvester's law of inertia — Horn–Johnson **Theorem 4.5.8, p.282** (congruence
    Q=SᵀS preserves inertia) — the conceptual justification the real spectrum is a
    congruence invariant.
  - Matrix-determinant lemma — Horn–Johnson **eq (0.8.5.11), p.26**, adjugate form
    `det(Ã + xyᵀ) = det Ã + yᵀ(adj Ã)x` (no invertibility side-condition) — arms the
    rank-one-correction determinant steps `det_rankOneCorrection_sub_smul_one`.

## MATHLIB PRIMITIVES (all present, per the CvS bridge Mathlib assessment)
`Matrix.PosDef`, `Matrix.PosSemidef.sqrt`, `Matrix.IsHermitian`,
`Matrix.IsHermitian.spectrum_eq_image_range`, `Matrix.charpoly`, similarity/conjugation
charpoly invariance, `Matrix.mul_adjugate`. Carathéodory–Fejér / Toeplitz-zeros are
NOT needed (finite §5 route).

## FOR PROSHKA — what to verify (kill or repair)
1. Is the Step-3 algebra correct (H = S D S⁻¹ Hermitian from S²D = Dᴴ S², S Hermitian)?
   Is the hypothesis form `Qᴴ*D = Dᴴ*Q` the right encoding of "D self-adjoint w.r.t. Q",
   or should it be `Q*D = Dᴴ*Q` (Q Hermitian)? Pin the exact convention.
2. Does the 6-step chain CLOSE with no gap, using ONLY the cited Horn–Johnson theorems
   + Mathlib primitives (no appeal to the unproved Horn–Johnson Problem 7.2.P10)?
3. Is the consumer coupling to `zerosRealOn_of_hermitian_charpoly_mul` type-correct
   (charpoly equality + IsHermitian ⇒ its `hM` hypothesis)?
4. Does closing M1 actually discharge the CvS §5 finite-matrix layer of H2b, and does
   H2b remain CONDITIONAL on H2a (SIMPLE_EVEN) — i.e. no overclaim of H2b closure?
5. Register the verdict + any repaired statement. On kill-pass, authorize Codex.

## CODEX DIRECTIVE (only after Proshka kill-pass + owner OK)
Formalize `posDefSelfAdjoint_charpoly_zerosReal` (or Proshka's repaired statement) in a
NEW file under Q3/Proofs/RouteB/ (do not edit HermitianDeterminantRealZeros.lean or
RankOneCorrection*.lean — consume them). Then wire it to
`zerosRealOn_of_hermitian_charpoly_mul` as the M1 consumer. Taint 0, standard triple,
no new axiom, no sorry. Validation: lake build; #print axioms; taint scan.

## Success / Failure codes
SUCCESS: M1_POSDEF_SELFADJOINT_REAL_SPECTRUM_PROVED
FAILURE (fail-closed, exactly one):
  M1_STEP3_HERMITIAN_ALGEBRA_GAP
  M1_SQRT_API_GAP           (PosSemidef.sqrt shape mismatch)
  M1_CHARPOLY_SIMILARITY_API_GAP
  M1_CONSUMER_COUPLING_MISMATCH
  LEAN_BUILD_FAIL

## Registered predictions
P051-C1 (conductor): the whole M1 chain closes in Lean from the cited primitives; the
  only real friction is the Step-3 Hermitian algebra + the exact self-adjointness
  convention (Qᴴ*D=Dᴴ*Q vs Q*D=Dᴴ*Q).
P051-C2: no new Mathlib machinery needed (all primitives present); Carathéodory–Fejér
  not invoked.

## Answer requirements
051_*.answer.md with handoff + ACTIONS LOG; scoring P051-C1/C2; goal consumed by
SHA-256; Route B state row (no promotion); canon+mirror one transaction.

## Excerpt provenance (litreview, all in pdfs/, cite-locked)
- M1_MATRIX_FORMULA_CARDS.md — Horn–Johnson 6/6 (Thms 7.2.6, 4.1.3b, 1.3.3/1.3.4,
  4.5.8, eq 0.8.5.11).
- CVS_H2B_FORMALIZATION_BRIDGE.md — the §5-route bridge tally (HAVE 5 / PARTIAL 5 /
  MISSING 5; M1 = keystone).
- CVS-QFRZ-2025 (2511.23257) — the H2b engine theorem (conditional on H2a simple+even).
