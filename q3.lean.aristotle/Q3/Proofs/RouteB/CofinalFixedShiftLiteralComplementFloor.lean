import Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementFloor
import Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.mathlibStandardSet false

open Complex Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace Q3.RouteB

/-!
# Cofinal fixed-shift literal CCM complement floor

This file enters the actual fixed-shift spectral wall.  It does not assume a
free floor predicate and it does not introduce free head, coupling, or tail
matrices.

For one literal production cell it forms the exact matrix

`Q * (K - aStar I) * Q - betaStar Q`

from `sourceCCMFiniteMatrix`, `sourceCCMComplexRow`, and the chosen fixed real
shift.  After reindexing that exact matrix by a supplied head/tail equivalence,
the head, coupling, and tail blocks are its canonical `toBlocks` projections.
A positive tail and a positive semidefinite Schur complement then certify the
fixed-shift floor.

The cofinal theorem applies the same certificate shape on the existing
`selectedPairIndex = parent (extract k)` schedule.  The analytic production of
the tail and corrected-head signs remains open and visible.
-/

/-- The literal fixed-shift floor matrix.  Positive semidefiniteness of this
matrix is exactly the matrix-side certificate needed for a floor `beta` at
the fixed real shift `aStar`. -/
noncomputable def sourceCCMFixedShiftFloorMatrix
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (aStar beta : ℝ) :
    Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ :=
  let q := D0Pstar.sourceCCMComplexRow S i
  let Q := complexTrialLineComplement q
  Q *
      (D0Pstar.sourceCCMFiniteMatrix i -
        (aStar : ℂ) •
          (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *
      Q -
    (beta : ℂ) • Q

/-- Source-locked fixed-shift complement-floor predicate. -/
def sourceCCMComplexTrialFixedShiftFloor
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (aStar beta : ℝ) : Prop :=
  complexTrialComplementFloor
    (D0Pstar.sourceCCMFiniteMatrix i)
    (D0Pstar.sourceCCMComplexRow S i)
    (aStar : ℂ)
    beta

private theorem complexTrialLineComplement_isHermitian_fixedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ) :
    (complexTrialLineComplement q).IsHermitian := by
  show (complexTrialLineComplement q)ᴴ = complexTrialLineComplement q
  rw [complexTrialLineComplement, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, complexTrialLineProjection_isHermitian q]

private theorem complexTrialLineComplement_sq_of_unit_fixedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    complexTrialLineComplement q * complexTrialLineComplement q =
      complexTrialLineComplement q := by
  have hP := complexTrialLineProjection_sq_of_unit q hq
  rw [complexTrialLineComplement]
  simp [Matrix.sub_mul, Matrix.mul_sub, hP]

private theorem complexTrialLineComplement_mul_block_fixedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    let Q := complexTrialLineComplement q
    let B := Q * (K - a • (1 : Matrix ι ι ℂ)) * Q
    Q * B = B := by
  intro Q B
  have hQsq := complexTrialLineComplement_sq_of_unit_fixedFloor q hq
  change Q * (Q * (K - a • (1 : Matrix ι ι ℂ)) * Q) =
    Q * (K - a • (1 : Matrix ι ι ℂ)) * Q
  calc
    _ = (Q * Q) * (K - a • (1 : Matrix ι ι ℂ)) * Q := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [show Q * Q = Q by simpa [Q] using hQsq]

/-- A positive semidefinite shifted-block-minus-floor matrix supplies the
trial-complement floor.  Unlike the older Gram checker, this theorem accepts
an arbitrary proof of positive semidefiniteness and therefore exposes Schur
and coercivity certificates directly. -/
theorem complexTrialComplementFloor_of_shiftedBlockSubFloor_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ) (beta : ℝ)
    (hq : star q ⬝ᵥ q = 1)
    (hbeta : 0 < beta)
    (hpsd :
      let Q := complexTrialLineComplement q
      let B := Q * (K - a • (1 : Matrix ι ι ℂ)) * Q
      (B - (beta : ℂ) • Q).PosSemidef) :
    complexTrialComplementFloor K q a beta := by
  let Q := complexTrialLineComplement q
  let B := Q * (K - a • (1 : Matrix ι ι ℂ)) * Q
  have hQherm : Q.IsHermitian :=
    complexTrialLineComplement_isHermitian_fixedFloor q
  have hQB : Q * B = B :=
    complexTrialLineComplement_mul_block_fixedFloor K q a hq
  have hpsd' : (B - (beta : ℂ) • Q).PosSemidef := by
    simpa [B, Q] using hpsd
  change 0 < beta ∧
    ∀ x : ι → ℂ,
      beta * ((star (Q *ᵥ x)) ⬝ᵥ (Q *ᵥ x)).re ≤
        ((star (Q *ᵥ x)) ⬝ᵥ (B *ᵥ x)).re
  refine ⟨hbeta, ?_⟩
  intro x
  have hleft :
      star (Q *ᵥ x) ⬝ᵥ (B *ᵥ x) =
        star x ⬝ᵥ (B *ᵥ x) := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hQherm.eq, hQB]
    exact (Matrix.dotProduct_mulVec (star x) B x).symm
  have hnorm :
      star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) =
        star x ⬝ᵥ (Q *ᵥ x) := by
    have hQsq := complexTrialLineComplement_sq_of_unit_fixedFloor q hq
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hQherm.eq,
      show Q * Q = Q by simpa [Q] using hQsq]
    exact (Matrix.dotProduct_mulVec (star x) Q x).symm
  rw [hleft, hnorm]
  have hnonnegRe :
      0 ≤ (star x ⬝ᵥ ((B - (beta : ℂ) • Q) *ᵥ x)).re :=
    hpsd'.re_dotProduct_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at hnonnegRe
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonnegRe
  rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im] at hnonnegRe
  simp only [zero_mul, sub_zero] at hnonnegRe
  linarith

/-- The literal fixed-shift floor matrix is Hermitian. -/
theorem sourceCCMFixedShiftFloorMatrix_isHermitian
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (aStar beta : ℝ) :
    (sourceCCMFixedShiftFloorMatrix S i aStar beta).IsHermitian := by
  let q := D0Pstar.sourceCCMComplexRow S i
  let Q := complexTrialLineComplement q
  let K := D0Pstar.sourceCCMFiniteMatrix i
  have hQ : Q.IsHermitian :=
    complexTrialLineComplement_isHermitian_fixedFloor q
  have hK : K.IsHermitian := by
    simpa [K] using D0Pstar.sourceCCMFiniteMatrix_isHermitian i
  have hshift :
      (K -
        (aStar : ℂ) •
          (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)).IsHermitian := by
    show
      (K -
        (aStar : ℂ) •
          (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ))ᴴ =
        K -
          (aStar : ℂ) •
            (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)
    rw [Matrix.conjTranspose_sub, hK.eq, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one]
    simp
  have hblock :
      (Q *
        (K -
          (aStar : ℂ) •
            (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *
        Q).IsHermitian := by
    show
      (Q *
        (K -
          (aStar : ℂ) •
            (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *
        Q)ᴴ =
      Q *
        (K -
          (aStar : ℂ) •
            (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *
        Q
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hQ.eq, hshift.eq]
    simp only [Matrix.mul_assoc]
  show
    (Q *
        (K -
          (aStar : ℂ) •
            (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) *
        Q -
      (beta : ℂ) • Q).IsHermitian
  have hsmulQ : ((beta : ℂ) • Q).IsHermitian := by
    show ((beta : ℂ) • Q)ᴴ = (beta : ℂ) • Q
    rw [Matrix.conjTranspose_smul, hQ.eq]
    simp
  exact hblock.sub hsmulQ

/-- Canonical Schur/Feshbach certificate for one literal fixed-shift cell.

The head, coupling, and tail are not caller-provided matrices.  They are the
four canonical `toBlocks` projections of the exact reindexed literal floor
matrix. -/
theorem sourceCCMComplexTrialFixedShiftFloor_of_schurBlocks
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (aStar beta : ℝ)
    {head tail : Type*}
    [Fintype head] [DecidableEq head]
    [Fintype tail] [DecidableEq tail]
    (split : (head ⊕ tail) ≃ CCMModeFinite i.N)
    (hbeta : 0 < beta)
    (hTail :
      let M := sourceCCMFixedShiftFloorMatrix S i aStar beta
      ((M.submatrix split split).toBlocks₂₂).PosDef)
    (hSchur :
      let M := sourceCCMFixedShiftFloorMatrix S i aStar beta
      let R := M.submatrix split split
      (R.toBlocks₁₁ -
        R.toBlocks₁₂ * R.toBlocks₂₂⁻¹ * R.toBlocks₁₂ᴴ).PosSemidef) :
    sourceCCMComplexTrialFixedShiftFloor S i aStar beta := by
  let M := sourceCCMFixedShiftFloorMatrix S i aStar beta
  let R := M.submatrix split split
  have hRherm : R.IsHermitian := by
    exact (sourceCCMFixedShiftFloorMatrix_isHermitian S i aStar beta).submatrix split
  have hCross : R.toBlocks₁₂ᴴ = R.toBlocks₂₁ := by
    have hFrom :
        (Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂
          R.toBlocks₂₁ R.toBlocks₂₂).IsHermitian := by
      simpa only [Matrix.fromBlocks_toBlocks] using hRherm
    exact (Matrix.isHermitian_fromBlocks_iff.mp hFrom).2.1
  have hTail' : R.toBlocks₂₂.PosDef := by
    simpa [R, M] using hTail
  have hSchur' :
      (R.toBlocks₁₁ -
        R.toBlocks₁₂ * R.toBlocks₂₂⁻¹ * R.toBlocks₁₂ᴴ).PosSemidef := by
    simpa [R, M] using hSchur
  letI : Invertible (R.toBlocks₂₂) := hTail'.isUnit.invertible
  have hFrom :
      (Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₁₂ᴴ R.toBlocks₂₂).PosSemidef :=
    (Matrix.PosDef.fromBlocks₂₂
      R.toBlocks₁₁ R.toBlocks₁₂ hTail').2 hSchur'
  have hR : R.PosSemidef := by
    simpa only [hCross, Matrix.fromBlocks_toBlocks] using hFrom
  have hM : M.PosSemidef :=
    (Matrix.posSemidef_submatrix_equiv (M := M) split).mp hR
  apply complexTrialComplementFloor_of_shiftedBlockSubFloor_posSemidef
    (D0Pstar.sourceCCMFiniteMatrix i)
    (D0Pstar.sourceCCMComplexRow S i)
    (aStar : ℂ) beta
    (D0Pstar.sourceCCMComplexRow_unit S i)
    hbeta
  simpa [M, sourceCCMFixedShiftFloorMatrix] using hM

/-- Cofinal source wrapper on the production schedule.  The split may change
with the literal cell, but it is fixed before the block signs are supplied. -/
theorem cofinalFixedShiftLiteralComplementFloor_of_schurBlocks
    (S : D0Pstar.ProlateCanonicalSourceData)
    (aStar beta : ℝ)
    (headSize tailSize : ℕ → ℕ)
    (split : ∀ k,
      (Fin (headSize k) ⊕ Fin (tailSize k)) ≃
        CCMModeFinite (D0Pstar.selectedPairIndex S k).N)
    (hbeta : 0 < beta)
    (hTail : ∀ k,
      let i := D0Pstar.selectedPairIndex S k
      let M := sourceCCMFixedShiftFloorMatrix S i aStar beta
      ((M.submatrix (split k) (split k)).toBlocks₂₂).PosDef)
    (hSchur : ∀ k,
      let i := D0Pstar.selectedPairIndex S k
      let M := sourceCCMFixedShiftFloorMatrix S i aStar beta
      let R := M.submatrix (split k) (split k)
      (R.toBlocks₁₁ -
        R.toBlocks₁₂ * R.toBlocks₂₂⁻¹ * R.toBlocks₁₂ᴴ).PosSemidef) :
    ∀ k,
      sourceCCMComplexTrialFixedShiftFloor S
        (D0Pstar.selectedPairIndex S k) aStar beta := by
  intro k
  exact sourceCCMComplexTrialFixedShiftFloor_of_schurBlocks
    S (D0Pstar.selectedPairIndex S k) aStar beta
    (split k) hbeta (hTail k) (hSchur k)

/-! ### Mandatory corrected-head plant -/

def goal058SchurHeadCollapseA : Matrix (Fin 1) (Fin 1) ℝ := !![-1]
def goal058SchurHeadCollapseC : Matrix (Fin 1) (Fin 1) ℝ := !![0]
def goal058SchurHeadCollapseD : Matrix (Fin 1) (Fin 1) ℝ := !![1]

/-- The model tail block is strictly positive. -/
theorem goal058SchurHeadCollapse_tail_posDef :
    goal058SchurHeadCollapseD.PosDef := by
  have hone : goal058SchurHeadCollapseD = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [goal058SchurHeadCollapseD, Matrix.one_apply]
  rw [hone]
  exact Matrix.PosDef.one

/-- A positive tail alone does not certify the full block: a negative head
direction survives.  Therefore the corrected-head Schur sign in the cofinal
theorem is load-bearing. -/
theorem goal058SchurHeadCollapse_full_not_posSemidef :
    ¬ (Matrix.fromBlocks
      goal058SchurHeadCollapseA
      goal058SchurHeadCollapseC
      goal058SchurHeadCollapseCᵀ
      goal058SchurHeadCollapseD).PosSemidef := by
  intro h
  have hdiag :=
    h.diag_nonneg (i := Sum.inl (0 : Fin 1))
  norm_num [goal058SchurHeadCollapseA,
    goal058SchurHeadCollapseC, goal058SchurHeadCollapseD] at hdiag

#print axioms complexTrialComplementFloor_of_shiftedBlockSubFloor_posSemidef
#print axioms sourceCCMFixedShiftFloorMatrix_isHermitian
#print axioms sourceCCMComplexTrialFixedShiftFloor_of_schurBlocks
#print axioms cofinalFixedShiftLiteralComplementFloor_of_schurBlocks
#print axioms goal058SchurHeadCollapse_tail_posDef
#print axioms goal058SchurHeadCollapse_full_not_posSemidef

end Q3.RouteB
