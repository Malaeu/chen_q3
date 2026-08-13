import Q3.Proofs.RouteB.CCMProposition59ComplexHermitianConnector

set_option linter.mathlibStandardSet false

/-!
# Goal 058 literal complex trial-line Feshbach decomposition

This file identifies the exact off-diagonal Feshbach/Schur coupling of the
literal finite CCM source cell.  Writing

* `q = D0Pstar.sourceCCMComplexRow S i` (the literal complex unit source row),
* `K = D0Pstar.sourceCCMFiniteMatrix i` (the literal finite CCM source matrix),
* `a = D0Pstar.sourceCCMFiniteRayleigh S i` (the literal real Rayleigh value),
* `r = D0Pstar.sourceCCMFiniteResidual S i` (the literal finite residual),
* `P = complexTrialLineProjection q`, `Q = 1 - P`,

the main theorem is the exact matrix identity

`K - a • 1 = vecMulVec q (star r) + vecMulVec r (star q) + Q * (K - a • 1) * Q`.

Everything here is a finite-cell algebraic identity for the literal source
objects.  No inequality, no floor, no spectral gap, no simplicity, no
eigenvector, no ground-to-trial tracking, no decay, no cofinal schedule, no
realification or parity input, no scalar commutator observable, no route
promotion, and no global claim is used or proved.  In particular the two
remaining source obligations (control of `r`, and a lower floor for
`Q * (K - a • 1) * Q`) are *not* addressed.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-- Algebraic complement of the complex trial line spanned by `q`. -/
noncomputable def complexTrialLineComplement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ) : Matrix ι ι ℂ :=
  1 - complexTrialLineProjection q

/-- The literal shifted complement (Feshbach) block of the finite CCM source
cell. -/
noncomputable def sourceCCMComplexTrialComplementBlock
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) :
    Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ :=
  let q := D0Pstar.sourceCCMComplexRow S i
  let K := D0Pstar.sourceCCMFiniteMatrix i
  let a : ℂ := (D0Pstar.sourceCCMFiniteRayleigh S i : ℂ)
  let Q := complexTrialLineComplement q
  Q * (K - a •
    (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) * Q

/-! ### Private generic support lemmas -/

/-- Action of the Hermitian rank-one trial-line projection on an arbitrary
vector. -/
private theorem complexTrialLineProjection_mulVec
    {ι : Type*} [Fintype ι] (q v : ι → ℂ) :
    complexTrialLineProjection q *ᵥ v = (star q ⬝ᵥ v) • q := by
  ext j
  simp [complexTrialLineProjection, Matrix.mulVec, Matrix.vecMulVec_apply,
    dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Action of the trial-line complement on an arbitrary vector. -/
private theorem complexTrialLineComplement_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q v : ι → ℂ) :
    complexTrialLineComplement q *ᵥ v = v - (star q ⬝ᵥ v) • q := by
  rw [complexTrialLineComplement, Matrix.sub_mulVec, Matrix.one_mulVec,
    complexTrialLineProjection_mulVec]

/-- From `star q ⬝ᵥ q = 1`, the trial-line projection fixes `q`. -/
private theorem complexTrialLineProjection_mulVec_self_of_unit
    {ι : Type*} [Fintype ι] (q : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    complexTrialLineProjection q *ᵥ q = q := by
  rw [complexTrialLineProjection_mulVec, hq, one_smul]

/-- From `star q ⬝ᵥ q = 1`, the trial-line complement annihilates `q`. -/
private theorem complexTrialLineComplement_mulVec_self_of_unit
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    complexTrialLineComplement q *ᵥ q = 0 := by
  rw [complexTrialLineComplement_mulVec, hq, one_smul, sub_self]

/-- The trial-line complement is Hermitian. -/
private theorem complexTrialLineComplement_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℂ) :
    (complexTrialLineComplement q).IsHermitian := by
  show (complexTrialLineComplement q)ᴴ = complexTrialLineComplement q
  rw [complexTrialLineComplement, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, complexTrialLineProjection_isHermitian q]

/-- Hermitian transfer of a left `star`-multiplication into a right one. -/
private theorem vecMul_star_of_isHermitian
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (v : ι → ℂ) :
    star v ᵥ* M = star (M *ᵥ v) := by
  have h := Matrix.vecMul_conjTranspose M (star v)
  rw [hM.eq, star_star] at h
  exact h

/-- `Q * K * P = vecMulVec r (star q)` for Hermitian `K`, unit `q`,
`a = star q ⬝ᵥ K q` and `r = K q - a • q`.  The unit binder `hq` is part of the
locked helper interface; this single block identity does not consume it, while
the assembled shifted identity below does. -/
private theorem hermitian_trialLine_left_block_eq_residual_vecMulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ) (r : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1)
    (ha : a = star q ⬝ᵥ (K *ᵥ q))
    (hr : r = K *ᵥ q - a • q) :
    complexTrialLineComplement q * K * complexTrialLineProjection q =
      Matrix.vecMulVec r (star q) := by
  have hKP :
      K * complexTrialLineProjection q =
        Matrix.vecMulVec (K *ᵥ q) (star q) := by
    rw [complexTrialLineProjection, Matrix.mul_vecMulVec]
  rw [Matrix.mul_assoc, hKP, Matrix.mul_vecMulVec,
    complexTrialLineComplement_mulVec, ← ha, ← hr]

/-- `P * K * Q = vecMulVec q (star r)` under the same hypotheses.  The
conjugate orientation is derived from Hermiticity of `K` and of the
complement, not from commutativity or transpose symmetry.  As above, the unit
binder `hq` is part of the locked helper interface and is not consumed by this
single block. -/
private theorem hermitian_trialLine_right_block_eq_vecMulVec_residual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ) (r : ι → ℂ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (ha : a = star q ⬝ᵥ (K *ᵥ q))
    (hr : r = K *ᵥ q - a • q) :
    complexTrialLineProjection q * K * complexTrialLineComplement q =
      Matrix.vecMulVec q (star r) := by
  have hPK :
      complexTrialLineProjection q * K =
        Matrix.vecMulVec q (star (K *ᵥ q)) := by
    rw [complexTrialLineProjection, Matrix.vecMulVec_mul,
      vecMul_star_of_isHermitian K hK q]
  have hQ := complexTrialLineComplement_isHermitian (q := q)
  have hlast :
      star (K *ᵥ q) ᵥ* complexTrialLineComplement q = star r := by
    have h :=
      vecMul_star_of_isHermitian (complexTrialLineComplement q) hQ (K *ᵥ q)
    rw [h, complexTrialLineComplement_mulVec, ← ha, ← hr]
  rw [hPK, Matrix.vecMulVec_mul, hlast]

/-- `P * K * P = a • P` under the same hypotheses.  As above, the unit binder
`hq` is part of the locked helper interface and is not consumed by this single
block. -/
private theorem hermitian_trialLine_center_block_eq_rayleigh_projection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (ha : a = star q ⬝ᵥ (K *ᵥ q)) :
    complexTrialLineProjection q * K * complexTrialLineProjection q =
      a • complexTrialLineProjection q := by
  have hPK :
      complexTrialLineProjection q * K =
        Matrix.vecMulVec q (star (K *ᵥ q)) := by
    rw [complexTrialLineProjection, Matrix.vecMulVec_mul,
      vecMul_star_of_isHermitian K hK q]
  have hdot : star (K *ᵥ q) ⬝ᵥ q = a := by
    rw [ha, Matrix.dotProduct_mulVec, vecMul_star_of_isHermitian K hK q]
  rw [hPK, complexTrialLineProjection, Matrix.vecMulVec_mul_vecMulVec, hdot,
    Matrix.vecMulVec_smul]

/-- Exact shifted Feshbach identity for a Hermitian matrix and a unit complex
trial row.  No positivity, gap, floor, eigenvector, simplicity, or nonzero
residual hypothesis is used; the case `r = 0` is included. -/
private theorem hermitian_unit_trialLine_shifted_feshbach
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ) (r : ι → ℂ)
    (hK : K.IsHermitian)
    (hq : star q ⬝ᵥ q = 1)
    (ha : a = star q ⬝ᵥ (K *ᵥ q))
    (hr : r = K *ᵥ q - a • q) :
    K - a • (1 : Matrix ι ι ℂ) =
      Matrix.vecMulVec q (star r) + Matrix.vecMulVec r (star q) +
        complexTrialLineComplement q *
          (K - a • (1 : Matrix ι ι ℂ)) * complexTrialLineComplement q := by
  have hPP := complexTrialLineProjection_sq_of_unit q hq
  have hM := hermitian_trialLine_center_block_eq_rayleigh_projection K q a hK hq ha
  have hL := hermitian_trialLine_left_block_eq_residual_vecMulVec K q a r hq ha hr
  have hR :=
    hermitian_trialLine_right_block_eq_vecMulVec_residual K q a r hK hq ha hr
  set P := complexTrialLineProjection q with hP
  set Q := complexTrialLineComplement q with hQdef
  have hQeq : Q = 1 - P := by rw [hQdef, hP, complexTrialLineComplement]
  have hPQ : P + Q = 1 := by rw [hQeq]; abel
  have hPQzero : P * Q = 0 := by
    rw [hQeq, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hQPzero : Q * P = 0 := by
    rw [hQeq, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hexp : ∀ X Y : Matrix ι ι ℂ,
      X * (K - a • (1 : Matrix ι ι ℂ)) * Y = X * K * Y - a • (X * Y) := by
    intro X Y
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul,
      Matrix.smul_mul]
  have hfour : ∀ M : Matrix ι ι ℂ,
      M = P * M * P + P * M * Q + Q * M * P + Q * M * Q := by
    intro M
    have h1 : (P + Q) * M * (P + Q) = M := by
      rw [hPQ, Matrix.one_mul, Matrix.mul_one]
    calc M = (P + Q) * M * (P + Q) := h1.symm
      _ = P * M * P + P * M * Q + Q * M * P + Q * M * Q := by
          simp only [Matrix.add_mul, Matrix.mul_add]
          abel
  have hcenter : P * (K - a • (1 : Matrix ι ι ℂ)) * P = 0 := by
    rw [hexp, hM, hPP, sub_self]
  have hright :
      P * (K - a • (1 : Matrix ι ι ℂ)) * Q = Matrix.vecMulVec q (star r) := by
    rw [hexp, hPQzero, hR, smul_zero, sub_zero]
  have hleft :
      Q * (K - a • (1 : Matrix ι ι ℂ)) * P = Matrix.vecMulVec r (star q) := by
    rw [hexp, hQPzero, hL, smul_zero, sub_zero]
  calc K - a • (1 : Matrix ι ι ℂ)
      = P * (K - a • (1 : Matrix ι ι ℂ)) * P +
          P * (K - a • (1 : Matrix ι ι ℂ)) * Q +
          Q * (K - a • (1 : Matrix ι ι ℂ)) * P +
          Q * (K - a • (1 : Matrix ι ι ℂ)) * Q :=
        hfour (K - a • (1 : Matrix ι ι ℂ))
    _ = Matrix.vecMulVec q (star r) + Matrix.vecMulVec r (star q) +
          Q * (K - a • (1 : Matrix ι ι ℂ)) * Q := by
        rw [hcenter, hright, hleft, zero_add]

/-! ### Literal source specializations -/

/-- The complement of the literal complex source trial line applied to
`K q` is exactly the literal finite source residual. -/
theorem sourceCCMComplexTrialComplement_mulVec_Kq_eq_residual
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) :
    let q := D0Pstar.sourceCCMComplexRow S i
    let K := D0Pstar.sourceCCMFiniteMatrix i
    let Q := complexTrialLineComplement q
    Q *ᵥ (K *ᵥ q) =
      D0Pstar.sourceCCMFiniteResidual S i := by
  intro q K Q
  rw [show Q = complexTrialLineComplement q from rfl,
    complexTrialLineComplement_mulVec]
  rw [D0Pstar.sourceCCMFiniteResidual]
  simp only [ambientResidual, D0Pstar.sourceCCMFiniteOperator,
    Matrix.mulVecLin_apply]
  rw [D0Pstar.sourceCCMFiniteRayleigh_coe]

/-- Exact literal CCM complex trial-line Feshbach decomposition of the shifted
finite source matrix.  The full off-diagonal coupling is exactly the literal
source residual `r`; the only other block is the literal shifted complement
block.  Nothing about the size of `r` or the spectrum of the complement block
is claimed. -/
theorem sourceCCMFiniteMatrix_sub_rayleigh_eq_complexTrialFeshbach
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) :
    let q := D0Pstar.sourceCCMComplexRow S i
    let K := D0Pstar.sourceCCMFiniteMatrix i
    let a : ℂ := (D0Pstar.sourceCCMFiniteRayleigh S i : ℂ)
    let r := D0Pstar.sourceCCMFiniteResidual S i
    K - a •
        (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ) =
      Matrix.vecMulVec q (star r) +
        Matrix.vecMulVec r (star q) +
          sourceCCMComplexTrialComplementBlock S i := by
  intro q K a r
  have hK : K.IsHermitian := D0Pstar.sourceCCMFiniteMatrix_isHermitian i
  have hq : star q ⬝ᵥ q = 1 := D0Pstar.sourceCCMComplexRow_unit S i
  have ha : a = star q ⬝ᵥ (K *ᵥ q) := D0Pstar.sourceCCMFiniteRayleigh_coe S i
  have hr : r = K *ᵥ q - a • q := rfl
  have hblock :
      sourceCCMComplexTrialComplementBlock S i =
        complexTrialLineComplement q *
          (K - a •
            (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *
          complexTrialLineComplement q := rfl
  rw [hblock]
  exact hermitian_unit_trialLine_shifted_feshbach K q a r hK hq ha hr

/-! ### Mandatory falsifier plants

These finite plants are checks only.  None of them is used by the two public
source theorems above, and none of them introduces a floor, a gap, an
eigenvector, a simplicity, a decay, or a cofinal premise.
-/

/-- P5 plant: the exact unit complex row `(3/5, 4i/5)` on `Fin 2`. -/
def goal058FeshbachOrientationRow : Fin 2 → ℂ := ![3 / 5, (4 / 5) * Complex.I]

theorem goal058FeshbachOrientationRow_unit :
    star goal058FeshbachOrientationRow ⬝ᵥ goal058FeshbachOrientationRow = 1 := by
  norm_num [goal058FeshbachOrientationRow, dotProduct, Fin.sum_univ_succ,
    Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]

/-- P5: the Hermitian orientation `vecMulVec q (star q)` is not the reversed
orientation `vecMulVec (star q) q`; the off-diagonal entry changes sign. -/
theorem goal058FeshbachOrientationPlant_orientation_matters :
    complexTrialLineProjection goal058FeshbachOrientationRow ≠
      Matrix.vecMulVec (star goal058FeshbachOrientationRow)
        goal058FeshbachOrientationRow := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [complexTrialLineProjection, Matrix.vecMulVec_apply,
    goal058FeshbachOrientationRow, Complex.ext_iff, Complex.div_re,
    Complex.div_im, Complex.normSq] at h01

/-- P6 plant matrix: the exact Hermitian swap matrix on `Fin 2`. -/
def goal058FeshbachResidualPlantMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- P6 plant row: the exact unit row `(1, 0)`. -/
def goal058FeshbachResidualPlantRow : Fin 2 → ℂ := ![1, 0]

/-- P6 plant residual: the exact source-shaped residual `K q - a q = (0, 1)`. -/
def goal058FeshbachResidualPlantResidual : Fin 2 → ℂ := ![0, 1]

theorem goal058FeshbachResidualPlantMatrix_isHermitian :
    goal058FeshbachResidualPlantMatrix.IsHermitian := by
  show goal058FeshbachResidualPlantMatrixᴴ = goal058FeshbachResidualPlantMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goal058FeshbachResidualPlantMatrix, Matrix.conjTranspose_apply]

theorem goal058FeshbachResidualPlantRow_unit :
    star goal058FeshbachResidualPlantRow ⬝ᵥ goal058FeshbachResidualPlantRow
      = 1 := by
  simp [goal058FeshbachResidualPlantRow, dotProduct, Fin.sum_univ_succ]

theorem goal058FeshbachResidualPlant_rayleigh_zero :
    (0 : ℂ) =
      star goal058FeshbachResidualPlantRow ⬝ᵥ
        (goal058FeshbachResidualPlantMatrix *ᵥ
          goal058FeshbachResidualPlantRow) := by
  simp [goal058FeshbachResidualPlantRow, goal058FeshbachResidualPlantMatrix,
    dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

theorem goal058FeshbachResidualPlant_residual_eq :
    goal058FeshbachResidualPlantResidual =
      goal058FeshbachResidualPlantMatrix *ᵥ goal058FeshbachResidualPlantRow -
        (0 : ℂ) • goal058FeshbachResidualPlantRow := by
  funext j
  fin_cases j <;>
    simp [goal058FeshbachResidualPlantResidual,
      goal058FeshbachResidualPlantRow, goal058FeshbachResidualPlantMatrix]

/-- P6: with the exact source-shaped residual the shifted Feshbach identity
holds for the plant. -/
theorem goal058FeshbachResidualPlant_identity :
    goal058FeshbachResidualPlantMatrix -
        (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.vecMulVec goal058FeshbachResidualPlantRow
          (star goal058FeshbachResidualPlantResidual) +
        Matrix.vecMulVec goal058FeshbachResidualPlantResidual
          (star goal058FeshbachResidualPlantRow) +
        complexTrialLineComplement goal058FeshbachResidualPlantRow *
          (goal058FeshbachResidualPlantMatrix -
            (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          complexTrialLineComplement goal058FeshbachResidualPlantRow :=
  hermitian_unit_trialLine_shifted_feshbach
    goal058FeshbachResidualPlantMatrix goal058FeshbachResidualPlantRow 0
    goal058FeshbachResidualPlantResidual
    goal058FeshbachResidualPlantMatrix_isHermitian
    goal058FeshbachResidualPlantRow_unit
    goal058FeshbachResidualPlant_rayleigh_zero
    goal058FeshbachResidualPlant_residual_eq

/-- P6: the sign-mutated residual `a q - K q` breaks the identity for the same
plant, so the residual orientation is detected. -/
theorem goal058FeshbachResidualSignPlant_mutant_fails :
    Matrix.vecMulVec goal058FeshbachResidualPlantRow
          (star (-goal058FeshbachResidualPlantResidual)) +
        Matrix.vecMulVec (-goal058FeshbachResidualPlantResidual)
          (star goal058FeshbachResidualPlantRow) +
        complexTrialLineComplement goal058FeshbachResidualPlantRow *
          (goal058FeshbachResidualPlantMatrix -
            (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          complexTrialLineComplement goal058FeshbachResidualPlantRow ≠
      goal058FeshbachResidualPlantMatrix -
        (0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro hmut
  have hcorrect := goal058FeshbachResidualPlant_identity
  have hcancel :
      Matrix.vecMulVec goal058FeshbachResidualPlantRow
            (star (-goal058FeshbachResidualPlantResidual)) +
          Matrix.vecMulVec (-goal058FeshbachResidualPlantResidual)
            (star goal058FeshbachResidualPlantRow) =
        Matrix.vecMulVec goal058FeshbachResidualPlantRow
            (star goal058FeshbachResidualPlantResidual) +
          Matrix.vecMulVec goal058FeshbachResidualPlantResidual
            (star goal058FeshbachResidualPlantRow) :=
    add_right_cancel (hmut.trans hcorrect)
  have h01 := congrFun (congrFun hcancel 0) 1
  norm_num [Matrix.vecMulVec_apply, goal058FeshbachResidualPlantRow,
    goal058FeshbachResidualPlantResidual] at h01

/-- P7 plant: the non-unit row `(2, 0)`. -/
def goal058FeshbachNonUnitRow : Fin 2 → ℂ := ![2, 0]

/-- P7: without `star q ⬝ᵥ q = 1` the complement does not annihilate the row,
so the unit normalization in the private helpers cannot be dropped and is
never silently reintroduced. -/
theorem goal058FeshbachNonUnitPlant_complement_mulVec_ne_zero :
    complexTrialLineComplement goal058FeshbachNonUnitRow *ᵥ
      goal058FeshbachNonUnitRow ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [complexTrialLineComplement, complexTrialLineProjection,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_succ,
    goal058FeshbachNonUnitRow, Complex.ext_iff] at h0

/-- P8 plant matrix: a Hermitian diagonal matrix on `Fin 2`. -/
def goal058FeshbachZeroResidualPlantMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 2]

/-- P8 plant row: a unit eigenvector of the plant matrix. -/
def goal058FeshbachZeroResidualPlantRow : Fin 2 → ℂ := ![1, 0]

theorem goal058FeshbachZeroResidualPlantMatrix_isHermitian :
    goal058FeshbachZeroResidualPlantMatrix.IsHermitian := by
  show goal058FeshbachZeroResidualPlantMatrixᴴ =
    goal058FeshbachZeroResidualPlantMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goal058FeshbachZeroResidualPlantMatrix, Matrix.conjTranspose_apply]

theorem goal058FeshbachZeroResidualPlantRow_unit :
    star goal058FeshbachZeroResidualPlantRow ⬝ᵥ
      goal058FeshbachZeroResidualPlantRow = 1 := by
  simp [goal058FeshbachZeroResidualPlantRow, dotProduct, Fin.sum_univ_succ]

theorem goal058FeshbachZeroResidualPlant_rayleigh :
    (1 : ℂ) =
      star goal058FeshbachZeroResidualPlantRow ⬝ᵥ
        (goal058FeshbachZeroResidualPlantMatrix *ᵥ
          goal058FeshbachZeroResidualPlantRow) := by
  simp [goal058FeshbachZeroResidualPlantRow,
    goal058FeshbachZeroResidualPlantMatrix, dotProduct, Matrix.mulVec,
    Fin.sum_univ_succ]

theorem goal058FeshbachZeroResidualPlant_residual_zero :
    (0 : Fin 2 → ℂ) =
      goal058FeshbachZeroResidualPlantMatrix *ᵥ
          goal058FeshbachZeroResidualPlantRow -
        (1 : ℂ) • goal058FeshbachZeroResidualPlantRow := by
  funext j
  fin_cases j <;>
    simp [goal058FeshbachZeroResidualPlantRow,
      goal058FeshbachZeroResidualPlantMatrix]

/-- P8: on the zero-residual branch the identity degenerates to the exact
block-diagonal statement, with no division by a residual norm, an overlap, or
a gap anywhere. -/
theorem goal058FeshbachZeroResidualPlant_identity :
    goal058FeshbachZeroResidualPlantMatrix -
        (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      complexTrialLineComplement goal058FeshbachZeroResidualPlantRow *
        (goal058FeshbachZeroResidualPlantMatrix -
          (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        complexTrialLineComplement goal058FeshbachZeroResidualPlantRow := by
  have h :=
    hermitian_unit_trialLine_shifted_feshbach
      goal058FeshbachZeroResidualPlantMatrix
      goal058FeshbachZeroResidualPlantRow 1 0
      goal058FeshbachZeroResidualPlantMatrix_isHermitian
      goal058FeshbachZeroResidualPlantRow_unit
      goal058FeshbachZeroResidualPlant_rayleigh
      goal058FeshbachZeroResidualPlant_residual_zero
  simpa using h

#print axioms complexTrialLineComplement
#print axioms sourceCCMComplexTrialComplementBlock
#print axioms sourceCCMComplexTrialComplement_mulVec_Kq_eq_residual
#print axioms sourceCCMFiniteMatrix_sub_rayleigh_eq_complexTrialFeshbach
#print axioms goal058FeshbachOrientationRow_unit
#print axioms goal058FeshbachOrientationPlant_orientation_matters
#print axioms goal058FeshbachResidualPlant_identity
#print axioms goal058FeshbachResidualSignPlant_mutant_fails
#print axioms goal058FeshbachNonUnitPlant_complement_mulVec_ne_zero
#print axioms goal058FeshbachZeroResidualPlant_identity

end Q3.RouteB
