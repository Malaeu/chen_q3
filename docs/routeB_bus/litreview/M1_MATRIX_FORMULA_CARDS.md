# M1 keystone — matrix-analysis formula cards (Horn–Johnson)

Source: pdfs/horn_johnson_matrix_analysis_2013.pdf
(Horn & Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013.)

**M1 target being armed:** "A matrix `D` that is self-adjoint w.r.t. a positive-definite
form `Q` (i.e. `Q D = Dᵀ Q`, `Q > 0`) has REAL spectrum." Standard route: congruence
`Q = SᵀS` (Cholesky) ⇒ `S D S⁻¹` symmetric ⇒ real eigenvalues.

**Page mapping used:** book page N = PDF page N + 19 (verified: book p.1 = PDF p.20).

**Score: 6 / 6 of the requested targets found verbatim** (target 5 is not stated as a
standalone theorem but is armed exactly by Problem 7.2.P10 + Theorem 4.1.7). Two most
important:
- Sylvester's law of inertia = **Theorem 4.5.8 (Sylvester), p.282**.
- Matrix-determinant lemma = **Cauchy's rank-one determinant formula (0.8.5.11), p.26**.

---

## 1. Hermitian matrix ⇒ real eigenvalues — Horn–Johnson Theorem 4.1.3, p.228
VERBATIM: "**Theorem 4.1.3.** Let A ∈ Mₙ be Hermitian. Then
(a) x*Ax is real for all x ∈ Cⁿ
(b) the eigenvalues of A are real
(c) S*AS is Hermitian for all S ∈ Mₙ"

Proof (verbatim): "Compute (x̄*Ax) = (x*Ax)* = x*A*x = x*Ax, so x*Ax equals its complex
conjugate and hence is real. If Ax = λx and x*x = 1, then λ = λx*x = x*λx = x*Ax is real
by (a). Finally, (S*AS)* = S*A*S = S*AS, so S*AS is always Hermitian."

LEAN TARGET: Arms the final step of M1 (once `S D S⁻¹` is shown Hermitian/symmetric, its
eigenvalues are real). Nearest Mathlib: `Matrix.IsHermitian.eigenvalues` are `ℝ`-valued
(`Matrix.IsHermitian.eigenvalues : Fin n → ℝ`); over `ℝ`, `Matrix.IsSymm`. Property (c) is
`Matrix.IsHermitian.conjTranspose_mul_mul_apply`-style congruence closure.
NOTE: Hypothesis: `A = A*` (Hermitian). Part (b) is the load-bearing conclusion.

### 1b. Converse / characterization — Theorem 4.1.4, p.228
VERBATIM: "**Theorem 4.1.4.** Let A = [aᵢⱼ] ∈ Mₙ be given. Then A is Hermitian if and only
if at least one of the following conditions is satisfied:
(a) x*Ax is real for all x ∈ Cⁿ
(b) A is normal and has only real eigenvalues
(c) S*AS is Hermitian for all S ∈ Mₙ"
NOTE: Useful as the biconditional if the Lean proof needs "real spectrum + normal ⇒ Hermitian".

### 1c. Spectral theorem restatement — Theorem 4.1.5, p.229
VERBATIM: "**Theorem 4.1.5.** A matrix A ∈ Mₙ is Hermitian if and only if there is a
unitary U ∈ Mₙ and a real diagonal Λ ∈ Mₙ such that A = UΛU*. Moreover, A is real and
Hermitian (that is, real symmetric) if and only if there is a real orthogonal P ∈ Mₙ and a
real diagonal Λ ∈ Mₙ such that A = PΛPᵀ."
LEAN TARGET: `Matrix.IsHermitian.spectral_theorem`; over ℝ the real-symmetric orthogonal
diagonalization. NOTE: the real-symmetric clause (A = PΛPᵀ, P orthogonal, Λ real diagonal)
is the exact object M1 lands on after congruence.

---

## 2. Sylvester's law of inertia — Horn–Johnson Theorem 4.5.8 (Sylvester), p.282
VERBATIM: "**Theorem 4.5.8 (Sylvester).** Hermitian matrices A, B ∈ Mₙ are *congruent if
and only if they have the same inertia, that is, if and only if they have the same number
of positive eigenvalues and the same number of negative eigenvalues."

Supporting definitions/theorems on the same pages:
- **Definition 4.5.4, p.281** (congruence): "Let A, B ∈ Mₙ be given. If there exists a
  nonsingular matrix S such that (a) B = SAS*, then B is said to be *congruent
  (\"star-congruent\") or conjunctive to A; (b) B = SASᵀ, then B is said to be congruent or
  ᵀcongruent (\"tee-congruent\") to A."
- **Theorem 4.5.5, p.281**: "Both *congruence and congruence are equivalence relations."
- **Definition 4.5.6, p.281** (inertia): "Let A ∈ Mₙ be Hermitian. The inertia of A is the
  ordered triple i(A) = (i₊(A), i₋(A), i₀(A))" where (p.282) "i₊(A) is the number of
  positive eigenvalues of A, i₋(A) is the number of negative eigenvalues of A, and i₀(A) is
  the number of zero eigenvalues of A. The signature of A is the quantity i₊(A) − i₋(A)."
- **Theorem 4.5.7, p.282**: "Each Hermitian matrix is *congruent to its inertia matrix."

LEAN TARGET: Congruence `Q = SᵀS` preserves inertia — guarantees `S D S⁻¹` keeps the real
spectral structure through the congruence step. Mathlib has no packaged Sylvester's law of
inertia (as of the toolchain in use); candidate namespace `Matrix.IsHermitian` / quadratic
forms `QuadraticForm`. NOTE: For M1 the special case is the definite one — see Cor. 7.2.8
below (positive definite ⇔ *congruent to identity), which is the exact instance needed.

### 2b. Quantitative refinement — Theorem 4.5.9 (Ostrowski), p.283
VERBATIM: "**Theorem 4.5.9 (Ostrowski).** Let A, S ∈ Mₙ with A Hermitian and S nonsingular.
Let the eigenvalues of A, SAS*, and SS* be arranged in nondecreasing order (4.2.1). Let
σ₁ ≥ ⋯ ≥ σₙ > 0 be the singular values of S. For each k = 1, …, n there is a positive real
number θₖ ∈ [σₙ², σ₁²] such that λₖ(SAS*) = θₖ λₖ(A)."
NOTE: Signs of eigenvalues are preserved under congruence (magnitudes may change); this is
the quantitative statement behind Sylvester. Not needed if only sign/real-ness is required.

---

## 3. Matrix-determinant lemma (rank-one update) — Horn–Johnson eq. (0.8.5.11), p.26
VERBATIM: "Equating the right-hand side of this identity to that of (0.8.5.10) and setting
a = −1 gives *Cauchy's formula for the determinant of a rank-one perturbation*
    det(Ã + xyᵀ) = det Ã + yᵀ (adj Ã) x    (0.8.5.11)"

Companion (bordered-matrix / Cauchy-expansion) form on the same page:
VERBATIM: "det [ Ã  x ; yᵀ  a ] = a det Ã − yᵀ (adj Ã) x    (0.8.5.10)"
and (for a ≠ 0): "det [ Ã  x ; yᵀ  a ] = a det(Ã − a⁻¹ x yᵀ)".

LEAN TARGET: The det-of-rank-one-update primitive. When `Ã` is nonsingular,
`adj Ã = det(Ã)·Ã⁻¹`, so (0.8.5.11) becomes `det(Ã + x yᵀ) = det(Ã)(1 + yᵀ Ã⁻¹ x)`, the
usual matrix-determinant lemma. Nearest Mathlib: `Matrix.det_one_add_col_mul_row`,
`Matrix.det_updateRow_add`, and adjugate lemmas `Matrix.mul_adjugate` /
`Matrix.adjugate_mul` (`A * adjugate A = det A • 1`).
NOTE: (0.8.5.11) holds for ALL Ã (no invertibility needed) because it uses the adjugate,
not the inverse — the form to prefer in Lean to avoid a nonsingularity side-condition.

### 3b. Adjugate identity (for deriving 3) — eq. (0.8.2.1), p.22
VERBATIM: "(adj A) A = A (adj A) = (det A) I    (0.8.2.1)"
LEAN TARGET: `Matrix.mul_adjugate`, `Matrix.adjugate_mul`. NOTE: bridges adjugate form
(0.8.5.11) to the inverse form of the lemma.

### 3c. Characteristic polynomial of a rank-one correction (supporting primitive)
NOT FOUND as a numbered standalone theorem in the sections read. It follows directly from
(0.8.5.11) with Ã := tI − A:
    p_{A+xyᵀ}(t) = det(tI − A − x yᵀ) = det(tI − A) − yᵀ adj(tI − A) x
and, where tI − A is nonsingular, = det(tI − A)·(1 − yᵀ (tI − A)⁻¹ x).
NOTE: derive in Lean from card 3, no separate source needed.

---

## 4. Similarity preserves characteristic polynomial / eigenvalues — Horn–Johnson Theorem 1.3.3 + Corollary 1.3.4, p.58
VERBATIM: "**Theorem 1.3.3.** Let A, B ∈ Mₙ. If B is similar to A, then A and B have the
same characteristic polynomial."

Proof (verbatim): "Compute
  p_B(t) = det(tI − B)
         = det(tS⁻¹S − S⁻¹AS) = det(S⁻¹(tI − A)S)
         = det S⁻¹ det(tI − A) det S = (det S)⁻¹(det S) det(tI − A)
         = det(tI − A) = p_A(t)"

VERBATIM: "**Corollary 1.3.4.** Let A, B ∈ Mₙ and suppose that A is similar to B. Then
(a) A and B have the same eigenvalues.
(b) If B is a diagonal matrix, its main diagonal entries are the eigenvalues of A.
(c) B = 0 (a diagonal matrix) if and only if A = 0.
(d) B = I (a diagonal matrix) if and only if A = I."

Supporting:
- **Definition 1.3.1, p.58** (similarity): "Let A, B ∈ Mₙ be given. We say that B is similar
  to A if there exists a nonsingular S ∈ Mₙ such that B = S⁻¹AS."
- **Observation 1.3.2, p.58**: "Similarity is an equivalence relation on Mₙ; that is,
  similarity is reflexive, symmetric, and transitive."

LEAN TARGET: Arms `S D S⁻¹` step — the similarity `S D S⁻¹` has the same eigenvalues as `D`,
so proving the conjugated matrix has real spectrum transfers back to `D`. Nearest Mathlib:
`Matrix.charpoly` invariance under conjugation (`Matrix.charpoly_conj` / spectrum
invariance `Matrix.IsConj`), `LinearMap.charpoly`. NOTE: In M1 the similarity is
`S D S⁻¹` with `S` from Cholesky `Q = SᵀS`; Cor. 1.3.4(a) is the exact transfer of the real
spectrum from `S D S⁻¹` back to `D`.

---

## 5. Self-adjoint w.r.t. a positive-definite form ⇒ real spectrum — Horn–Johnson Problem 7.2.P10, p.443 (+ Theorem 4.1.7, p.229)
No standalone numbered theorem states this in the sections read; it is armed EXACTLY by:

VERBATIM (Problem 7.2.P10, p.443): "Let A ∈ Mₙ. Theorem 4.1.7 says that A is similar to A*
via a *Hermitian* matrix if and only if A is similar to a real matrix. Show that A is
similar to A* via a *Hermitian positive definite* matrix if and only if A is similar to a
real diagonal matrix."

VERBATIM (Theorem 4.1.7, p.229): "Let A ∈ Mₙ be given. The following statements are
equivalent:
(a) A is similar to a real matrix.
(b) A is similar to A*.
(c) A is similar to A* via a Hermitian similarity transformation.
(d) A = HK, in which H, K ∈ Mₙ are Hermitian and at least one factor is nonsingular.
(e) A = HK, in which H, K ∈ Mₙ are Hermitian."

LEAN TARGET: This is the DIRECT M1 statement. The hypothesis `Q D = Dᵀ Q` with `Q ≻ 0` says
`Q D` is symmetric (`(QD)ᵀ = Dᵀ Qᵀ = Dᵀ Q = Q D`), so `D = Q⁻¹(Q D)` is a product of two
Hermitian/symmetric matrices with the first factor `Q⁻¹` positive definite — i.e. `D` is
similar to `A*` (here `Dᵀ`) via a **Hermitian positive definite** matrix `Q`. Problem
7.2.P10 then gives: `D` is similar to a **real diagonal** matrix ⇒ real (and semisimple)
spectrum. Theorem 4.1.7(e)/(d) gives the weaker "similar to a real matrix" (real spectrum)
from just `D = HK` with `H, K` Hermitian.
NOTE: 7.2.P10 is a *problem* (unproved in text, hint only), not a citable theorem. For a
fully-citable Lean chain prefer the constructive congruence route: Cor. 7.2.8/7.2.9
(Cholesky `Q = SᵀS`) + Theorem 1.3.3/1.3.4 (similarity) + Theorem 4.1.3(b) (Hermitian ⇒
real). That triad proves M1 without relying on the problem statement.

---

## 6. Cholesky / positive-definite ⇒ Q = SᵀS factorization — Horn–Johnson Corollary 7.2.9 (Cholesky factorization), p.441
VERBATIM: "**Corollary 7.2.9 (Cholesky factorization).** Let A ∈ Mₙ be Hermitian. Then A is
positive semidefinite (respectively, positive definite) if and only if there is a lower
triangular matrix L ∈ Mₙ with nonnegative (respectively, positive) diagonal entries such
that A = LL*. If A is positive definite, L is unique. If A is real, L may be taken to be
real."

The exact congruence form M1 needs (positive definite ⇔ Q = S*S):
VERBATIM (**Corollary 7.2.8, p.441**): "A Hermitian matrix A is positive definite if and
only if it is *congruent to the identity." (Proof: "This is simply a restatement of
(7.2.7).")

VERBATIM (**Theorem 7.2.7, p.440**): "Let A ∈ Mₙ be Hermitian.
(a) A is positive semidefinite if and only if there is a B ∈ M_{m,n} such that A = B*B.
(b) If A = B*B with B ∈ M_{m,n}, and if x ∈ Cⁿ, then Ax = 0 if and only if Bx = 0, so
nullspace A = nullspace B and rank A = rank B.
(c) If A = B*B with B ∈ M_{m,n}, then A is positive definite if and only if B has full
column rank."

VERBATIM (**Theorem 7.2.1, p.438**): "A Hermitian matrix is positive semidefinite if and
only if all of its eigenvalues are nonnegative. It is positive definite if and only if all
of its eigenvalues are positive."

Supporting (unique positive-definite square root, an alternative to Cholesky):
VERBATIM (**Theorem 7.2.6, p.439**): "Let A ∈ Mₙ be Hermitian and positive semidefinite, let
r = rank A, and let k ∈ {2, 3, …}. (a) There is a unique Hermitian positive semidefinite
matrix B such that Bᵏ = A. (b) There is a polynomial p with real coefficients such that
B = p(A). … (d) B is real if A is real." (The `k = 2` case is `A^{1/2}`, so `Q = (Q^{1/2})²`
with `Q^{1/2}` symmetric positive definite gives the symmetric `S = Q^{1/2}` congruence.)

LEAN TARGET: Provides the `Q = SᵀS` factorization that opens M1. Two Mathlib-friendly routes:
(i) `A^{1/2}` symmetric square root — Mathlib `Matrix.PosDef.sqrt` / `Matrix.PosSemidef.sqrt`
(`Matrix.PosSemidef.sqrt_mul_self`), giving `Q = S S` with `S = Sᵀ ≻ 0`, then
`S D S⁻¹` is symmetric; (ii) Cholesky `Matrix.PosDef` LDL / `Matrix.PosDef` factorization
if available. Cor. 7.2.8 (`Matrix.PosDef` ⇔ congruent to `1`) is the cleanest primitive.
NOTE: For M1 the symmetric-square-root `S = Q^{1/2}` (Thm 7.2.6, k=2) is usually easier in
Lean than triangular Cholesky, because it keeps `S` symmetric so `S D S⁻¹ = S⁻¹(QD)S⁻¹` is
manifestly symmetric when `QD` is symmetric.

---

## Assembled M1 proof chain (all citable, no reliance on the problem 7.2.P10)
1. `Q ≻ 0`, `Q D = Dᵀ Q` ⇒ `Q D` symmetric.
2. `Q = S² ` with `S = Q^{1/2}` symmetric positive definite — **Thm 7.2.6 (k=2), p.439**
   (or `Q = SᵀS` via **Cor. 7.2.9 Cholesky / Cor. 7.2.8, p.441**).
3. `S D S⁻¹ = S⁻¹ (Q D) S⁻¹` is symmetric (Hermitian) since `Q D` is — **Thm 4.1.3(c), p.228**.
4. Symmetric ⇒ real eigenvalues — **Thm 4.1.3(b), p.228**.
5. Similarity transfers eigenvalues back to `D` — **Thm 1.3.3 / Cor. 1.3.4(a), p.58**.
6. (Inertia/definiteness bookkeeping, if needed) — **Thm 4.5.8 Sylvester, p.282**;
   **Cor. 7.2.8, p.441**.
Rank-one supporting primitives (if the M1 keystone feeds a determinant argument):
**(0.8.5.11) p.26** (det of rank-one update) + **(0.8.2.1) p.22** (adjugate).
