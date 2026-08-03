# STATUS: CONDITIONAL — M1 KILL-PASS AFTER REPAIR; CODEX AUTHORIZED
```yaml
PRIMARY: M1_MATH_PLAN_KILL_PASS_REPAIRED_CODEX_AUTHORIZED
PRIMARY_COUNT: 1

TRANSACTION:
  GOAL: 051_m1_posdef_selfadjoint_real_spectrum
  PIN: 8083f121203931aa4df50249804f710aa28207e1
  GOAL_SHA256: 1989992e5e1acce958464cd9b5ac3c81d1b2bde008f506b22b4d53142caf537b
  GOAL_SHA256_MATCHES_PINNED_MANIFEST: true
  GOAL_SHA256_RECOMPUTED_LOCALLY: false

SCOPE: ABSTRACT
VERIFIER: PAPER_PLUS_PINNED_MATHLIB_SOURCE_AUDIT
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
RH_CLAIMED: false
BUS_010: VOID

M1:
  MATHEMATICAL_CHAIN_NO_GAP_AFTER_REPAIR: true
  STEP3_HERMITIAN_ALGEBRA: PASS
  STANDARD_SELFADJOINTNESS_CONVENTION: "Dᴴ * Q = Q * D"
  PROJECT_MATCHING_ORIENTATION: "Q * D = Dᴴ * Q"
  ORIGINAL_QHD_FORM:
    status: EQUIVALENT_ONLY_USING_hQ_IS_HERMITIAN
    preferred: false
  HORN_JOHNSON_P10_USED: false
  SYLVESTER_INERTIA_USED: false
  MATRIX_DETERMINANT_LEMMA_USED: false

MATHLIB_V4_26:
  PIN: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
  SQRT_API:
    use:
      - CFC.sqrt
      - Matrix.PosSemidef.sqrt_mul_self
      - Matrix.PosDef.posDef_sqrt
      - Matrix.PosDef.isUnit
    reject_as_exact_api:
      - Matrix.PosDef.sqrt
  CHARPOLY_API:
    use: Matrix.charpoly_units_conj
  HERMITIAN_API:
    use:
      - Matrix.IsHermitian
      - Matrix.isHermitian_conjTranspose_mul_mul
      - Matrix.IsHermitian.inv

CONSUMER:
  CORE_COUPLING_TYPE_CORRECT: true
  DIRECT_REAL_SCAFFOLD_COUPLING_REQUIRES_EXPLICIT_SCALAR_EXTENSION: true
  REQUIRED_COROLLARY: zerosRealOn_of_posDefSelfAdjoint_charpoly_mul
  REQUIRED_REAL_WRAPPER: real_weightedSymmetric_to_complex_consumer
  EXISTING_CONSUMER_FILE_MUTATION_ALLOWED: false

H2B_SCOPE:
  M1_SUBLAYER_CLOSED_BY_FORMALIZATION: true
  CVS_SECTION5_FINITE_LAYER_CLOSED_BY_M1_ALONE: false
  H2B_CLOSED: false
  H2A_SIMPLE_EVEN_STILL_REQUIRED: true
  REMAINING:
    - M2_DEGENERATE_Q_SEPARATED_QUOTIENT_POSDEF
    - M3_DETERMINANT_TO_LAGRANGE_IDENTIFICATION
    - M4_FOURIER_POLE_CANCELLATION_AND_LIMIT_IF_FULL_ENGINE_REQUIRED

PREDICTIONS:
  P051_C1: CONFIRMED_WITH_API_AND_STATEMENT_REPAIR
  P051_C2: CONFIRMED

CODEX:
  AUTHORIZED: true
  OWNER_OK_STILL_REQUIRED_FOR_REPO_WRITE: true
  TARGET_FILE: Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean

SUCCESS_CODE: M1_POSDEF_SELFADJOINT_REAL_SPECTRUM_PROVED
FAILURE_CODES:
  - M1_STEP3_HERMITIAN_ALGEBRA_GAP
  - M1_CFC_SQRT_API_GAP
  - M1_CHARPOLY_UNITS_CONJ_API_GAP
  - M1_REAL_TO_COMPLEX_CONSUMER_GLUE_GAP
  - M1_CONSUMER_COUPLING_MISMATCH
  - LEAN_BUILD_FAIL

PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 5
```

## ROUTE MAP

| Node | Verdict | Exact meaning | Tags |
|---|---|---|---|
| M1 abstract matrix theorem | **KILL-PASS AFTER REPAIR** | A matrix self-adjoint for a positive-definite Hermitian form is similar to a Hermitian matrix. | `[ABSTRACT][PAPER]` |
| Step-3 conjugation algebra | **PASS** | \(H=SDS^{-1}\) is Hermitian from \(Q=S^2\) and \(QD=D^{*}Q\). | `[ABSTRACT][PAPER]` |
| Pinned Mathlib support | **PASS WITH API REPAIR** | The required square root, invertibility, Hermitian-congruence, and charpoly-conjugation primitives exist in Mathlib v4.26. | `[ABSTRACT][LEAN]` |
| Existing complex consumer | **PASS WITH EXPLICIT GLUE** | `H.IsHermitian` plus `H.charpoly = D.charpoly` is exactly sufficient after rewriting the factorization. The real scaffold needs an explicit real-to-complex wrapper. | `[ABSTRACT][CONDITIONAL]` |
| CvS §5 finite layer | **STILL OPEN** | M1 closes only the weighted-self-adjoint \(\to\) real-spectrum keystone. M2 and M3 remain. | `[ABSTRACT][PAPER]` |
| H2b | **CONDITIONAL ON H2a** | `SIMPLE_EVEN` remains an input; no H2b or Route B promotion is authorized by M1. | `[ABSTRACT][PAPER]` |

---

## VERIFICATION QUESTION 1 — STEP-3 ALGEBRA AND CONVENTION

### Correct self-adjointness convention

Use the weighted inner product

\[
\langle x,y\rangle_Q:=x^{*}Qy.
\]

Then

\[
\langle Dx,y\rangle_Q
=
x^{*}D^{*}Qy,
\qquad
\langle x,Dy\rangle_Q
=
x^{*}QDy.
\]

Therefore \(D\) is self-adjoint with respect to \(Q\) exactly when

\[
\boxed{D^{*}Q=QD.}
\]

The project scaffold writes the same equality in the orientation

\[
\boxed{QD=D^{*}Q.}
\]

That is the preferred Lean hypothesis because it literally matches the real theorem

```lean
T * D' = D'.transpose * T
```

already proved by `rankOneCorrection_weightedSymmetric`.

The goal's hypothesis

\[
Q^{*}D=D^{*}Q
\]

is equivalent only after using `hQ.isHermitian`, hence \(Q^{*}=Q\). It is mathematically legal but not the direct definition and introduces a pointless rewrite.

### Repaired hypothesis

```lean
(hSA : Q * D = Dᴴ * Q)
```

### Step-3 calculation

Let

\[
S:=Q^{1/2}.
\]

Since \(Q\) is positive definite:

\[
S^{*}=S,\qquad S^2=Q,\qquad S\ \text{is invertible}.
\]

Define

\[
H:=SDS^{-1}.
\]

Then

\[
H^{*}
=
(S^{-1})^{*}D^{*}S^{*}
=
S^{-1}D^{*}S.
\]

From weighted self-adjointness,

\[
S^2D=D^{*}S^2.
\]

Multiplying this equality on the left and right by \(S^{-1}\) gives

\[
SDS^{-1}=S^{-1}D^{*}S.
\]

Consequently,

\[
\boxed{H=H^{*}.}
\]

The algebra is correct. There is no commutativity assumption on \(D\) and \(S\).

### Mandatory negative plant

Positive definiteness cannot be weakened to mere Hermitian invertibility.

Take

\[
Q=
\begin{pmatrix}
1&0\\
0&-1
\end{pmatrix},
\qquad
D=
\begin{pmatrix}
0&1\\
-1&0
\end{pmatrix}.
\]

Then

\[
QD=D^{T}Q,
\]

but

\[
\operatorname{Spec}(D)=\{i,-i\}.
\]

Thus `PosDef` is load-bearing.

---

## VERIFICATION QUESTION 2 — DOES THE SIX-STEP CHAIN CLOSE?

### Verdict

\[
\boxed{\text{YES, for M1 itself, after three explicit repairs.}}
\]

The proof does not need Horn–Johnson Problem 7.2.P10.

### Citable mathematical chain

1. \(Q\succ0\) has a unique Hermitian positive-definite square root \(S=Q^{1/2}\).
2. \(S\) is invertible.
3. The Step-3 calculation proves \(H=SDS^{-1}\) Hermitian.
4. A Hermitian matrix has real spectrum.
5. Similar matrices have the same characteristic polynomial.
6. The existing consumer turns Hermitian charpoly zeros into `ZerosRealOn`.

### Pinned Mathlib chain

At the pinned Mathlib v4.26 commit, use:

```lean
CFC.sqrt Q
hQ.posSemidef.sqrt_mul_self
hQ.posDef_sqrt
(hQ.posDef_sqrt).isUnit
Matrix.charpoly_units_conj
Matrix.isHermitian_conjTranspose_mul_mul
Matrix.IsHermitian.inv
```

The cards' suggested name `Matrix.PosDef.sqrt` is not the exact pinned API. This is an API repair, not a mathematical gap.

### Exact charpoly transfer

If `Su : (Matrix n n 𝕜)ˣ` is the unit corresponding to \(S\), Mathlib provides

```lean
Matrix.charpoly_units_conj Su D :
  (Su.val * D * Su⁻¹.val).charpoly = D.charpoly
```

which exactly matches \(H=SDS^{-1}\).

### Non-load-bearing material to remove from the proof dependency list

- Horn–Johnson Problem 7.2.P10: not used.
- Sylvester's law of inertia: not used.
- The rank-one determinant lemma: not used by M1.

Two comments in the formula cards must not be propagated:

1. “similar to a real matrix” does **not** imply real spectrum; a real rotation matrix has eigenvalues \(\pm i\);
2. congruence/inertia does not by itself transfer the spectrum of the non-Hermitian matrix \(D\).

Neither error affects the repaired square-root/similarity proof.

---

## VERIFICATION QUESTION 3 — CONSUMER COUPLING

The existing consumer has the form

```lean
zerosRealOn_of_hermitian_charpoly_mul
    (M : Matrix n n ℂ)
    (hM : M.IsHermitian)
    ...
    (hfactor : ∀ z,
      F z = unit z * (M.charpoly.eval z * realFactor z))
```

Suppose M1 returns

```lean
⟨H, hH, hchar⟩
```

with

```lean
hH    : H.IsHermitian
hchar : H.charpoly = D.charpoly
```

and the existing determinant factorization is written using `D.charpoly`. Then the new consumer corollary rewrites `H.charpoly` with `hchar` and applies the existing theorem unchanged.

Therefore the coupling is type-correct.

### Required direct corollary

```lean
theorem zerosRealOn_of_posDefSelfAdjoint_charpoly_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q D : Matrix n n ℂ)
    (hQ : Q.PosDef)
    (hSA : Q * D = Dᴴ * Q)
    (F unit realFactor : ℂ → ℂ)
    (hunit : ∀ z, unit z ≠ 0)
    (hrealFactor : ZerosRealOn Set.univ realFactor)
    (hfactor : ∀ z,
      F z = unit z * (D.charpoly.eval z * realFactor z)) :
    ZerosRealOn Set.univ F
```

The proof should obtain \(H\), rewrite the factorization, and invoke
`zerosRealOn_of_hermitian_charpoly_mul`.

### Real scaffold caveat

`rankOneCorrection_weightedSymmetric` currently produces a theorem over real matrices:

```lean
T * D' = D'.transpose * T.
```

The Hermitian consumer is complex-valued. The formalization must therefore include one explicit wrapper:

```text
real PosDef weighted-symmetric matrix
→ real symmetric similar matrix
→ map that matrix to ℂ
→ use Matrix.charpoly_map
→ invoke the complex consumer.
```

This scalar-extension step is routine, but it is not written in the six-step goal. It must not be hidden.

---

## VERIFICATION QUESTION 4 — WHAT DOES M1 CLOSE?

M1 closes exactly:

```text
β6 / β8d bridge:
Q-self-adjoint on a genuine positive-definite finite space
→ similar Hermitian matrix
→ real charpoly roots.
```

M1 does **not** by itself close the full CvS §5 finite-matrix layer.

The actual CvS form before separation is positive semidefinite and has a radical. Still open are:

```text
M2:
  identify the radical from H2a simplicity;
  construct the Q-separated quotient;
  prove the induced form positive definite;
  descend the corrected operator self-adjointly.

M3:
  identify the determinant/adjugate expression with the Lagrange polynomial P(s).
```

For the complete Fourier-transform real-zero engine, the pole-cancellation and limit layer remains a separate analytic obligation when required.

Hence:

\[
\boxed{\text{H2b remains OPEN and CONDITIONAL on H2a SIMPLE\_EVEN.}}
\]

No Route B promotion, RH claim, or Bus 010 action follows from M1.

---

## VERIFICATION QUESTION 5 — REGISTERED VERDICT

### Repaired core theorem

Prefer a reusable `RCLike` theorem:

```lean
theorem posDefSelfAdjoint_exists_hermitian
    {𝕜 n : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n]
    (Q D : Matrix n n 𝕜)
    (hQ : Q.PosDef)
    (hSA : Q * D = Dᴴ * Q) :
    ∃ H : Matrix n n 𝕜,
      H.IsHermitian ∧ H.charpoly = D.charpoly
```

If the `RCLike` generality causes avoidable API friction, the authorized fallback is the complex theorem from the goal with the repaired `hSA`.

### Formalization boundary

Codex is authorized to formalize:

1. the M1 core theorem;
2. the direct complex `ZerosRealOn` consumer corollary;
3. the explicit real-to-complex wrapper matching
   `rankOneCorrection_weightedSymmetric`.

Codex is not authorized to claim M2, M3, H2b, H2a, or RH.

---

## FINAL PROPOSAL

Use the square-root similarity route.

Registered prediction before Lean execution:

```text
P051-F1:
  The core theorem compiles using CFC.sqrt, PosDef.isUnit,
  and Matrix.charpoly_units_conj.

P051-F2:
  The main tactical friction is unit/inverse simplification,
  not a missing mathematical theorem.

P051-F3:
  The real-to-complex wrapper is a separate small theorem;
  if it fails, the core M1 theorem remains valid but the Q3 weld is incomplete.
```

Cheapest decisive test:

```text
Compile the core theorem first, before writing the consumer wrapper.
```

Likeliest failure point:

```text
CFC.sqrt / Units normalization in the Step-3 matrix equality.
```

Response:

```text
Do not change the theorem.
Switch the proof representation to the manifestly Hermitian matrix

  S⁻¹ * (Q * D) * S⁻¹

prove it equals S * D * S⁻¹,
then use charpoly_units_conj.
```

This is the authorized representation shift if direct `Hᴴ = H` simplification stalls.

---

## STRONGEST ATTACK

The strongest overclaim would be:

> M1 proves the CvS finite real-zero theorem.

It does not.

M1 assumes a genuine positive-definite form. CvS reaches such a form only after quotienting by the radical, and identifying that radical consumes the simple-kernel part of H2a. The determinant-to-Lagrange identification also remains independent.

The weakest correct statement is:

\[
\boxed{
\text{M1 closes the positive-definite weighted-self-adjoint real-spectrum keystone.}
}
\]

---

## CODEX DIRECTIVE

```text
TARGET:
  M1_PosDefSelfAdjointRealSpectrum

PIN:
  8083f121203931aa4df50249804f710aa28207e1

NEW FILE:
  Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean

DO NOT EDIT:
  Q3/Proofs/RouteB/HermitianDeterminantRealZeros.lean
  Q3/Proofs/RouteB/RankOneCorrectionWeightedSymmetry.lean
  Q3/Proofs/RouteB/RankOneCorrectionDeterminant.lean
  Q3/Proofs/RouteB/RankOneCorrectionAllSpectralPoints.lean
  Q3.Main
  frozen Route B state

IMPORT:
  Mathlib.Analysis.Matrix.Order
  Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
  Q3.Proofs.RouteB.HermitianDeterminantRealZeros
  Q3.Proofs.RouteB.RankOneCorrectionWeightedSymmetry

PRIMARY THEOREM:
  posDefSelfAdjoint_exists_hermitian

PRIMARY HYPOTHESIS:
  hSA : Q * D = Dᴴ * Q

PROOF ROUTE:
  1. let S := CFC.sqrt Q;
  2. obtain S*S=Q from hQ.posSemidef.sqrt_mul_self;
  3. obtain S.PosDef from hQ.posDef_sqrt;
  4. obtain IsUnit S from PosDef.isUnit and lift S to a matrix unit;
  5. define H = S * D * S⁻¹;
  6. prove H.IsHermitian by the frozen Step-3 calculation;
  7. prove H.charpoly = D.charpoly with Matrix.charpoly_units_conj.

MANDATORY COROLLARY:
  zerosRealOn_of_posDefSelfAdjoint_charpoly_mul

MANDATORY Q3 WELD:
  add a real-to-complex wrapper consuming
  rankOneCorrection_weightedSymmetric;
  use Matrix.charpoly_map explicitly.

MANDATORY PLANTS:
  1. Q=1, D a real diagonal matrix: theorem accepts.
  2. indefinite Q=diag(1,-1),
     D=[[0,1],[-1,0]]:
       weighted symmetry holds and spectrum is nonreal;
       document that PosDef rejects the plant.
  3. reuse nonHermitian_charpoly_nonreal_zero to confirm
     the Hermitian consumer hypothesis cannot be dropped.

FORBIDDEN:
  - no Horn–Johnson Problem 7.2.P10;
  - no Sylvester-inertia argument;
  - no matrix-determinant lemma inside M1;
  - no new axiom;
  - no sorry/admit/exact?/native_decide;
  - no replacement of PosDef by invertible Hermitian;
  - no H2b/H2a/RH promotion;
  - no mutation of the existing consumer.

VALIDATION:
  lake env lean Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean
  lake build Q3.Proofs.RouteB.PosDefSelfAdjointRealSpectrum
  lake build
  rg -n 'sorry|admit|exact\?|axiom|native_decide' \
    Q3/Proofs/RouteB/PosDefSelfAdjointRealSpectrum.lean
  #print axioms Q3.RouteB.posDefSelfAdjoint_exists_hermitian
  #print axioms Q3.RouteB.zerosRealOn_of_posDefSelfAdjoint_charpoly_mul
  taint scan

EXPECTED AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  M1_POSDEF_SELFADJOINT_REAL_SPECTRUM_PROVED

FAILURE:
  M1_STEP3_HERMITIAN_ALGEBRA_GAP
  M1_CFC_SQRT_API_GAP
  M1_CHARPOLY_UNITS_CONJ_API_GAP
  M1_REAL_TO_COMPLEX_CONSUMER_GLUE_GAP
  M1_CONSUMER_COUPLING_MISMATCH
  LEAN_BUILD_FAIL

REPORT MUST SAY:
  M1 closed or exact failure;
  M2/M3 remain open;
  H2b remains conditional on H2a SIMPLE_EVEN;
  no Route B promotion.
```

---

## ACTIONS LOG

```text
READ:
  051_m1_posdef_selfadjoint_real_spectrum.goal.md
  M1_MATRIX_FORMULA_CARDS.md
  CVS_H2B_FORMALIZATION_BRIDGE.md
  HermitianDeterminantRealZeros.lean

PIN AUDIT:
  commit 8083f121203931aa4df50249804f710aa28207e1 located;
  goal SHA-256 matches the pinned manifest entry.

MATH AUDIT:
  Step-3 algebra PASS;
  self-adjointness convention repaired to QD=DᴴQ;
  PosDef necessity plant PASS.

SOURCE AUDIT:
  square-root/similarity proof independent of HJ Problem 7.2.P10;
  non-load-bearing 4.1.7 and Sylvester glosses quarantined.

MATHLIB AUDIT:
  v4.26 pin recovered;
  CFC.sqrt path located;
  PosDef.isUnit located;
  charpoly_units_conj located;
  Hermitian congruence/inverse primitives located.

CONSUMER AUDIT:
  abstract complex coupling PASS;
  real-to-complex wrapper explicitly added to formalization contract.

SCOPE AUDIT:
  M1 only;
  M2/M3 open;
  H2b conditional on H2a;
  no promotion.
```

---

## META CLOSEOUT

**What became smaller?**

```text
“weighted self-adjoint real spectrum”
```

became one exact square-root similarity theorem plus one explicit scalar-extension wrapper.

**What was killed?**

- `QᴴD=DᴴQ` as the preferred convention;
- reliance on HJ Problem 7.2.P10;
- Sylvester inertia as an M1 proof;
- the claim that M1 alone closes CvS §5;
- hidden real-to-complex consumer glue.

**What must not be tried again?**

Do not formalize the degenerate PSD ambient form by pretending it is PosDef. M2 must perform the separated quotient honestly.

**Current smallest named gap after M1 formalization:**

```text
M2_DEGENERATE_Q_SEPARATED_QUOTIENT_POSDEF
```

then

```text
M3_DETERMINANT_TO_LAGRANGE_IDENTIFICATION
```

**Next cheapest decisive test:**

Compile the M1 core theorem before the consumer wrapper.

**Fate of prior predictions:**

```text
P051-C1:
  CONFIRMED WITH REPAIR.
  No mathematical gap; exact convention and CFC/Units API needed repair.

P051-C2:
  CONFIRMED.
  No Carathéodory–Fejér or new Mathlib machinery is needed.
```

```yaml
iteration:
  target: Goal_051_M1_weighted_selfadjoint_real_spectrum
  status: PROGRESS
  failed_strategy: treat_supporting_inertia_and_P10_material_as_dependencies
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: M2_DEGENERATE_Q_SEPARATED_QUOTIENT_POSDEF
  invariant_learned: weighted_selfadjointness_is_DstarQ_eq_QD_and_PosDef_is_load_bearing
  forbidden_future_move: apply_M1_directly_to_the_degenerate_CvS_form
  next_decisive_test: compile_M1_core_with_CFC_sqrt_and_charpoly_units_conj
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
