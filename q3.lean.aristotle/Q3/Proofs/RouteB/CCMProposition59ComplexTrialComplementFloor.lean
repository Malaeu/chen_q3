import Q3.Proofs.RouteB.CCMProposition59ComplexTrialLineFeshbach
import Mathlib.Analysis.Matrix.PosDef

set_option linter.mathlibStandardSet false

/-!
# Goal 058 literal complex trial-complement floor

This file fixes the exact inequality target for the shifted complement block
of the literal finite CCM source trial line.  It also proves that an exact
Gram factorization of the literal shifted block supplies that floor.

The factorization data are explicit certificate inputs.  No spectral gap,
eigenvector, simplicity, parity, cofinal estimate, or asymptotic floor is
assumed or proved here.  In particular, this is a finite-cell certificate
soundness theorem, not the missing source arithmetic that must eventually
produce such certificates on a precommitted cofinal schedule.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped ComplexOrder

/-- A positive lower floor for the shifted complement of a complex unit trial
line.  The unit hypothesis is consumed by the certificate theorem below. -/
def complexTrialComplementFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ) (beta : ℝ) : Prop :=
  let Q := complexTrialLineComplement q
  let B := Q * (K - a • (1 : Matrix ι ι ℂ)) * Q
  0 < beta ∧
    ∀ x : ι → ℂ,
      beta *
          ((star (Q *ᵥ x)) ⬝ᵥ (Q *ᵥ x)).re ≤
        ((star (Q *ᵥ x)) ⬝ᵥ (B *ᵥ x)).re

/-- The generic floor predicate specialized to the exact finite CCM source
matrix, source row, and source Rayleigh value. -/
def sourceCCMComplexTrialComplementFloor
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (beta : ℝ) : Prop :=
  complexTrialComplementFloor
    (D0Pstar.sourceCCMFiniteMatrix i)
    (D0Pstar.sourceCCMComplexRow S i)
    (D0Pstar.sourceCCMFiniteRayleigh S i : ℂ)
    beta

private theorem complexTrialLineComplement_isHermitian_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ) :
    (complexTrialLineComplement q).IsHermitian := by
  show (complexTrialLineComplement q)ᴴ = complexTrialLineComplement q
  rw [complexTrialLineComplement, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, complexTrialLineProjection_isHermitian q]

private theorem complexTrialLineComplement_sq_of_unit_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    complexTrialLineComplement q * complexTrialLineComplement q =
      complexTrialLineComplement q := by
  have hP := complexTrialLineProjection_sq_of_unit q hq
  rw [complexTrialLineComplement]
  simp [Matrix.sub_mul, Matrix.mul_sub, hP]

private theorem complexTrialLineProjection_mulVec_local
    {ι : Type*} [Fintype ι]
    (q v : ι → ℂ) :
    complexTrialLineProjection q *ᵥ v = (star q ⬝ᵥ v) • q := by
  ext j
  simp [complexTrialLineProjection, Matrix.mulVec, Matrix.vecMulVec_apply,
    dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

private theorem complexTrialLineComplement_mul_block_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    let Q := complexTrialLineComplement q
    let B := Q * (K - a • (1 : Matrix ι ι ℂ)) * Q
    Q * B = B := by
  intro Q B
  have hQsq := complexTrialLineComplement_sq_of_unit_local q hq
  change Q *
      (Q * (K - a • (1 : Matrix ι ι ℂ)) * Q) =
    Q * (K - a • (1 : Matrix ι ι ℂ)) * Q
  calc
    _ = (Q * Q) *
        (K - a • (1 : Matrix ι ι ℂ)) * Q := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [show Q * Q = Q by simpa [Q] using hQsq]

/-- Exact Gram-certificate soundness for a complex unit trial complement.

The certificate is the matrix equality

`B - beta • Q = Rᴴ * R`,

where `B = Q * (K - aI) * Q`. -/
theorem complexTrialComplementFloor_of_gramCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (q : ι → ℂ) (a : ℂ) (beta : ℝ)
    (R : Matrix ι ι ℂ)
    (hq : star q ⬝ᵥ q = 1)
    (hbeta : 0 < beta)
    (hgram : let Q := complexTrialLineComplement q
      Q * (K - a • (1 : Matrix ι ι ℂ)) * Q -
          (beta : ℂ) • Q =
        Rᴴ * R) :
    complexTrialComplementFloor K q a beta := by
  let Q := complexTrialLineComplement q
  let B := Q * (K - a • (1 : Matrix ι ι ℂ)) * Q
  have hQherm : Q.IsHermitian :=
    complexTrialLineComplement_isHermitian_local q
  have hQB : Q * B = B :=
    complexTrialLineComplement_mul_block_local K q a hq
  have hpsd : (B - (beta : ℂ) • Q).PosSemidef := by
    rw [show B - (beta : ℂ) • Q = Rᴴ * R by simpa [B, Q] using hgram]
    exact Matrix.posSemidef_conjTranspose_mul_self R
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
    have hQsq := complexTrialLineComplement_sq_of_unit_local q
      hq
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hQherm.eq,
      show Q * Q = Q by simpa [Q] using hQsq]
    exact (Matrix.dotProduct_mulVec (star x) Q x).symm
  rw [hleft, hnorm]
  have hnonnegRe :
      0 ≤ (star x ⬝ᵥ ((B - (beta : ℂ) • Q) *ᵥ x)).re :=
    hpsd.re_dotProduct_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at hnonnegRe
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hnonnegRe
  rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im] at hnonnegRe
  simp only [zero_mul, sub_zero] at hnonnegRe
  linarith

/-- Literal source specialization of the exact Gram-certificate checker.  It
does not assert that the certificate data exist. -/
theorem sourceCCMComplexTrialComplementFloor_of_gramCertificate
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (beta : ℝ)
    (R : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)
    (hbeta : 0 < beta)
    (hgram :
      sourceCCMComplexTrialComplementBlock S i -
          (beta : ℂ) •
            complexTrialLineComplement
              (D0Pstar.sourceCCMComplexRow S i) =
        Rᴴ * R) :
    sourceCCMComplexTrialComplementFloor S i beta := by
  apply complexTrialComplementFloor_of_gramCertificate
    (D0Pstar.sourceCCMFiniteMatrix i)
    (D0Pstar.sourceCCMComplexRow S i)
    (D0Pstar.sourceCCMFiniteRayleigh S i : ℂ)
    beta R
    (D0Pstar.sourceCCMComplexRow_unit S i)
    hbeta
  simpa [sourceCCMComplexTrialComplementBlock] using hgram

/-! ### Exact commutator-collapse falsifier -/

/-- Diagonal mode matrix for the exact `Fin 3` commutator-collapse plant. -/
def goal058ComplementFloorCollapseD : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1, 0, 0; 0, 0, 0; 0, 0, 1]

/-- The all-ones Hermitian matrix in the collapse plant. -/
def goal058ComplementFloorCollapseK : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 1; 1, 1, 1; 1, 1, 1]

def goal058ComplementFloorCollapseEta : Fin 3 → ℂ := ![1, 1, 1]
def goal058ComplementFloorCollapseBeta : Fin 3 → ℂ := ![-1, 0, 1]

/-- The plant has the same exact rank-two commutator shape as the source CCM
matrix. -/
theorem goal058ComplementFloorCollapse_exact_rankTwo_commutator :
    goal058ComplementFloorCollapseD * goal058ComplementFloorCollapseK -
        goal058ComplementFloorCollapseK * goal058ComplementFloorCollapseD =
      Matrix.vecMulVec goal058ComplementFloorCollapseBeta
          goal058ComplementFloorCollapseEta -
        Matrix.vecMulVec goal058ComplementFloorCollapseEta
          goal058ComplementFloorCollapseBeta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [goal058ComplementFloorCollapseD,
      goal058ComplementFloorCollapseK, goal058ComplementFloorCollapseBeta,
      goal058ComplementFloorCollapseEta, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Fin.sum_univ_succ]

/-- A rational complex unit ground vector of the all-ones plant. -/
def goal058ComplementFloorCollapseQ : Fin 3 → ℂ :=
  ![1 / 2, Complex.I / 2, -(1 + Complex.I) / 2]

/-- A second rational complex ground vector, orthogonal to the selected trial
line. -/
def goal058ComplementFloorCollapseY : Fin 3 → ℂ :=
  ![1 - 2 * Complex.I, -2 + Complex.I, 1 + Complex.I]

theorem goal058ComplementFloorCollapseQ_unit :
    star goal058ComplementFloorCollapseQ ⬝ᵥ
        goal058ComplementFloorCollapseQ = 1 := by
  norm_num [goal058ComplementFloorCollapseQ, dotProduct,
    Fin.sum_univ_succ, Complex.ext_iff, Complex.div_re, Complex.div_im,
    Complex.normSq]

theorem goal058ComplementFloorCollapseQ_orthogonal_Y :
    star goal058ComplementFloorCollapseQ ⬝ᵥ
        goal058ComplementFloorCollapseY = 0 := by
  norm_num [goal058ComplementFloorCollapseQ,
    goal058ComplementFloorCollapseY, dotProduct, Fin.sum_univ_succ,
    Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]

theorem goal058ComplementFloorCollapseK_kills_Y :
    goal058ComplementFloorCollapseK *ᵥ
        goal058ComplementFloorCollapseY = 0 := by
  funext i
  fin_cases i <;>
    norm_num [goal058ComplementFloorCollapseK,
      goal058ComplementFloorCollapseY, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Complex.ext_iff]

theorem goal058ComplementFloorCollapseQComplement_fixes_Y :
    complexTrialLineComplement goal058ComplementFloorCollapseQ *ᵥ
        goal058ComplementFloorCollapseY =
      goal058ComplementFloorCollapseY := by
  rw [complexTrialLineComplement, Matrix.sub_mulVec, Matrix.one_mulVec,
    complexTrialLineProjection_mulVec_local,
    goal058ComplementFloorCollapseQ_orthogonal_Y, zero_smul, sub_zero]

theorem goal058ComplementFloorCollapseY_normSq_re :
    (star goal058ComplementFloorCollapseY ⬝ᵥ
      goal058ComplementFloorCollapseY).re = 12 := by
  norm_num [goal058ComplementFloorCollapseY, dotProduct,
    Fin.sum_univ_succ, Complex.ext_iff, Complex.normSq]

/-- P1: exact rank-two commutation does not imply any positive complement
floor.  The checker sees a second nonzero ground vector in the selected trial
line's orthogonal complement and rejects every `beta > 0`. -/
theorem goal058ComplementFloorCollapse_no_positive_floor
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ complexTrialComplementFloor
      goal058ComplementFloorCollapseK goal058ComplementFloorCollapseQ 0 beta := by
  intro hfloor
  have h := hfloor.2 goal058ComplementFloorCollapseY
  let Q := complexTrialLineComplement goal058ComplementFloorCollapseQ
  have hQY : Q *ᵥ goal058ComplementFloorCollapseY =
      goal058ComplementFloorCollapseY :=
    goal058ComplementFloorCollapseQComplement_fixes_Y
  have hBY :
      (Q *
          (goal058ComplementFloorCollapseK -
            (0 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Q) *ᵥ
          goal058ComplementFloorCollapseY = 0 := by
    simp only [zero_smul, sub_zero]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQY,
      goal058ComplementFloorCollapseK_kills_Y, Matrix.mulVec_zero]
  change beta *
      ((star (Q *ᵥ goal058ComplementFloorCollapseY)) ⬝ᵥ
        (Q *ᵥ goal058ComplementFloorCollapseY)).re ≤
    ((star (Q *ᵥ goal058ComplementFloorCollapseY)) ⬝ᵥ
      ((Q *
          (goal058ComplementFloorCollapseK -
            (0 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Q) *ᵥ
        goal058ComplementFloorCollapseY)).re at h
  rw [hQY, hBY, dotProduct_zero, Complex.zero_re,
    goal058ComplementFloorCollapseY_normSq_re] at h
  linarith

/-- The exact Gram checker itself rejects the commutator-collapse plant for
every positive proposed floor. -/
theorem goal058ComplementFloorCollapse_no_gramCertificate
    (beta : ℝ) (hbeta : 0 < beta)
    (R : Matrix (Fin 3) (Fin 3) ℂ) :
    ¬ (let Q := complexTrialLineComplement goal058ComplementFloorCollapseQ
      Q *
            (goal058ComplementFloorCollapseK -
              (0 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Q -
          (beta : ℂ) • Q =
        Rᴴ * R) := by
  intro hgram
  exact goal058ComplementFloorCollapse_no_positive_floor beta hbeta
    (complexTrialComplementFloor_of_gramCertificate
      goal058ComplementFloorCollapseK goal058ComplementFloorCollapseQ
      0 beta R goal058ComplementFloorCollapseQ_unit hbeta hgram)

#print axioms complexTrialComplementFloor
#print axioms sourceCCMComplexTrialComplementFloor
#print axioms complexTrialComplementFloor_of_gramCertificate
#print axioms sourceCCMComplexTrialComplementFloor_of_gramCertificate
#print axioms goal058ComplementFloorCollapse_exact_rankTwo_commutator
#print axioms goal058ComplementFloorCollapse_no_positive_floor
#print axioms goal058ComplementFloorCollapse_no_gramCertificate

end Q3.RouteB
