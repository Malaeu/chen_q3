# STATUS: PROVED — ACCEPT_G3_MODE4_FINITE_TAIL_POSDEF_AND_PUBLIC_SCHUR_CROSSWALK

Transport note: captured with the chat's `Copy response` action.  The rendered
mathematical equality was returned as a seven-equals conflict-marker line;
this record normalizes that single line to `=` and removes end-of-line spaces.
No mathematical wording, path, or reviewed artifact hash was changed.

```yaml
PRIMARY: ACCEPT_G3_MODE4_FINITE_TAIL_POSDEF_AND_PUBLIC_SCHUR_CROSSWALK
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REQUIRED_PARENT: c65ea047d68642e66f23dac089298d97af98ffde
  LEAN_SHA256:
    expected: 19a20a506f5b6a264b469efac555553e3f9565791c8a7da903117c8a22c40e7e
    observed: 19a20a506f5b6a264b469efac555553e3f9565791c8a7da903117c8a22c40e7e
    status: PASS
  REPORT_SHA256:
    expected: 61f78b578d034cfb73ec0cbad7f80d6a0c5288e3f172b5caa83739ca1b4ae21f
    observed: 61f78b578d034cfb73ec0cbad7f80d6a0c5288e3f172b5caa83739ca1b4ae21f
    status: PASS
  PLANT_SHA256:
    expected: 6e5b2583578e378668dd700ad614aeacdb60c9f4f2519ffd5337873e71999b31
    byte_rehashed_by_judge: false
    status: REPORT_LOCK_ONLY

LEAN_LEAF:
  file: Q3/Proofs/RouteB/D0Mode4BackwardTailFiniteTailPosDef.lean
  scope: FINITE_CELL
  verifier: LEAN
  public_theorems:
    - mode4ActualFiniteJacobiTruncation_tailBlock_posDef
    - mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation
  public_definitions: 0
  public_structures: 0
  public_axioms: 0

MATHEMATICAL_RULING:
  literal_tail_block_posDef: PROVED
  exact_tail_orientation_K_Kplus1: PRESERVED
  source_off_diagonal: PRESERVED
  d_zero_boundary: PROVED_VACUOUSLY
  private_pivot_predicate_exposed: false
  public_schur_identity: PROVED
  haynsworth_or_inertia_additivity: NOT_PROVED
  finite_negative_count: NOT_PROVED
  endpoint_counts_2_3: NOT_PROVED

PLANTS:
  hermitian_not_posDef: ADEQUATE_PASS_REPORTED
  missing_separation: ADEQUATE_PASS_REPORTED
  missing_Lambda_upper: ADEQUATE_PASS_REPORTED
  reversed_orientation: ADEQUATE_PASS_REPORTED

TRUST:
  direct_Lean: REPORT_PASS
  target_build: REPORT_PASS_7753
  full_build: REPORT_PASS_7817
  q3_check: REPORT_PASS
  judge_reran_builds: false
  public_axioms:
    - propext
    - Classical.choice
    - Quot.sound
  sorryAx: ABSENT_REPORTED
  Aristotle_output_consumed: false

COMMIT:
  isolated_two_file_commit_authorized: true
  push_origin_rh_clean_authorized: true
  byte_changes_authorized: false
  plant_scratch_commit_authorized: false

NEXT_BOUNDED_LEAF:
  code: G3_MODE4_FINITE_BLOCK_INERTIA_ADDITIVITY
  target: >-
    Prove that the negative-eigenvalue count of the literal actual finite
    Jacobi truncation equals the negative-eigenvalue count of its exact finite
    Schur complement, because the eliminated tail block is PosDef.
  scope: FINITE_CELL
  verifier: LEAN

G1: OPEN
G3: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Attachment hash-lock observations

The extracted embedded Lean artifact is exactly `13 167` UTF-8 bytes and matches the required SHA-256. The extracted embedded report also matches its required SHA-256. The plant scratch source is not embedded, so its bytes cannot be independently rehashed here; only its hash, theorem descriptions, and reported execution are available. This limitation does not affect the semantic audit of the production Lean leaf itself.

`[FINITE_CELL][LEAN]`

## Public-surface audit

The production file adds no public definition, structure, axiom, or placeholder. Its only public declarations are:

```lean
mode4ActualFiniteJacobiTruncation_tailBlock_posDef

mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation
```

Both use exactly:

```lean
(mProject K d : ℕ)
(Λ : ℝ)
(hm : 2 ≤ mProject)
(hK : 3 ≤ K)
(hsep :
  ∀ q ≥ K,
    (31 / 24 : ℝ) * mode4JacobiG mProject ≤
      mode4JacobiIndex q *
        (mode4JacobiIndex q + 1) - 20)
(hΛ : Λ ≤ 20)
```

The first theorem concludes `Matrix.PosDef` for the literal `toBlocks₂₂`. The second publishes the exact Schur-complement identity without exposing the predecessor’s recursive pivot predicate.

`[FINITE_CELL][LEAN]`

## Exact mathematical audit

The proof is source-faithful.

First, it identifies the literal eliminated block entrywise with a recursive forward tail whose coordinates are ordered:

[
K,K+1,\ldots,K+d-1.
]

This closes the principal object-mismatch risk; the private recursive matrix is not merely similar to the source block—it is proved equal to it.

Second, the quadratic form is split exactly as:

[
\langle x,Ax\rangle
===================

## c_Kx_0^2

2s_Kx_0x_1
+
\langle x_{\mathrm{tail}},A_{K+1}x_{\mathrm{tail}}\rangle.
]

The cross term uses the literal source coefficient:

```lean
-mode4JacobiSymmetricOff G K
```

and `mode4JacobiSymmetricOff_sq` supplies the weighted Young inequality:

[
2s_Kx_0x_1
\le
U_Kx_0^2+L_{K+1}x_1^2.
]

The induction then proves the stronger private estimate:

[
L_Kx_0^2+\frac{G}{12}\sum_i x_i^2
\le
\langle x,Ax\rangle.
]

Since (G=\texttt{mode4JacobiG};mProject>0), every nonzero vector in a nonempty tail has strictly positive quadratic form. For (d=0), no nonzero vector exists, so `PosDef` holds vacuously.

Third, the public Schur theorem separately proves every recursive finite-elimination pivot nonzero. It uses the accepted backward-tail invariant in ([0,\tfrac12]) and the exact center-minus-upper-times-tail lower bound. The private pivot predicate is discharged inside the proof and does not survive in the theorem head.

No Haynsworth theorem, inertia count, endpoint count, zero offset, limiting argument, or classical-spectrum identification occurs in the source.

`[FINITE_CELL][LEAN]`

## Axiom and trust-boundary audit

The embedded production source contains no `sorry`, `admit`, `exact?`, new `axiom`, or unsafe proof shortcut.

The report records:

```text
direct Lean: PASS
target build: PASS — 7753 jobs
full build: PASS — 7817 jobs
q3_check: PASS
git diff --check: PASS
```

Those executions were not rerun in this adjudication; they remain exact report evidence rather than fresh judge executions. Both public theorem profiles are reported as exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The still-running independent Aristotle job is not imported or consumed anywhere in the local proof.

`[FINITE_CELL][LEAN]`

## Planted-falsifier audit

All four plants are mathematically relevant to this bounded leaf:

1. **Hermitian-not-PosDef** blocks the invalid inference:

   ```text
   Hermitian → PosDef.
   ```

2. **Missing separation** uses an actual `d=1` source tail satisfying the remaining public assumptions but failing positivity. This demonstrates that `hsep` is not decorative.

3. **Missing `Λ ≤ 20`** gives another actual `d=1` source tail with separation but negative quadratic form at large (\Lambda). This demonstrates that the production domain is load-bearing.

4. **Reversed orientation** distinguishes the actual (K,K+1,\ldots) tail from a reversed surrogate.

The plant suite is adequate for the exact theorem shape. The plant source itself was not embedded, so this audit ratifies the stated mathematical discriminators and reported Lean outcomes, not the unseen scratch bytes.

`[FINITE_CELL][PAPER]`

## Strongest surviving attack

The surviving wall is **finite block-inertia additivity**.

`Matrix.PosDef` of the eliminated block plus the exact Schur identity does not itself prove:

[
n_-(M)
======

n_-!\left(
M_{11}-M_{12}M_{22}^{-1}M_{21}
\right).
]

That equality needs an exact block congruence or Haynsworth-style finite-dimensional theorem using the same block orientation, the same inverse, and the current project negative-count invariant.

This is not a defect in the accepted leaf. It is precisely the next independent bounded theorem. The current proof must not be relabelled as an inertia result.

`[FINITE_CELL][CONDITIONAL]`

## Commit and push ruling

**Authorized** for exactly these two byte-locked artifacts:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4BackwardTailFiniteTailPosDef.lean

q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
  GOAL058_G3_MODE4_FINITE_TAIL_POSDEF_AND_PUBLIC_SCHUR_CROSSWALK_REPORT_2026-08-14.md
```

The Lean file must retain SHA-256:

```text
19a20a506f5b6a264b469efac555553e3f9565791c8a7da903117c8a22c40e7e
```

The report must retain SHA-256:

```text
61f78b578d034cfb73ec0cbad7f80d6a0c5288e3f172b5caa83739ca1b4ae21f
```

Do not stage the scratch plant, semantic-index output, Route/Bus/runtime files, or any unrelated byte. **Any byte change requires a new review.**

## Next exact bounded leaf

```text
G3_MODE4_FINITE_BLOCK_INERTIA_ADDITIVITY
```

Exact mathematical contract:

[
\boxed{
n_-!\left(
\operatorname{mode4ActualFiniteJacobiTruncation}
(mProject,\Lambda,K,d)
\right)
=

n_-!\left(
\operatorname{mode4BackwardTailSchurApprox}
(mProject,\Lambda,K,d)
\right)
}
]

under the same `hm`, `hK`, `hsep`, and `hΛ`, using:

```text
mode4ActualFiniteJacobiTruncation_isHermitian
mode4ActualFiniteJacobiTruncation_tailBlock_posDef
mode4ActualFiniteJacobiTruncation_schurComplement_eq_approx_of_separation
```

The theorem must prove the congruence/inertia equality. It may not assume the negative count, endpoint counts `2/3`, offset zero, or any finite-to-limit stabilization theorem.

## Explicit nonclaims

```text
G1 OPEN
G3 OPEN
NO HAYNSWORTH RESULT YET
NO FINITE NEGATIVE COUNT YET
NO LIMIT-STABILITY CLAIM
NO ZERO-OFFSET CLAIM
NO ENDPOINT COUNTS 2/3
NO ACTUAL INDEXED PSI CONSTRUCTOR
NO CCM LEMMA 7.2 RATE
NO ROUTE PROMOTION
NO RH CLAIM
```
