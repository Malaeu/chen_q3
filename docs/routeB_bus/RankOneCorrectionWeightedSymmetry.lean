import Mathlib

set_option linter.mathlibStandardSet false

namespace Q3.RouteB

/-- Source Lemma 5.4 rank-one correction
`D' = D - |D ξ⟩⟨η|` in real matrix coordinates. -/
def rankOneCorrection
    {n : Type*} [Fintype n]
    (D : Matrix n n ℝ) (xi eta : n → ℝ) : Matrix n n ℝ :=
  D - Matrix.vecMulVec (Matrix.mulVec D xi) eta

/-- The normalization `⟨η,ξ⟩=1` makes the corrected operator kill `ξ`. -/
theorem rankOneCorrection_kills_vector
    {n : Type*} [Fintype n]
    (D : Matrix n n ℝ) (xi eta : n → ℝ)
    (hnormalized : eta ⬝ᵥ xi = 1) :
    Matrix.mulVec (rankOneCorrection D xi eta) xi = 0 := by
  unfold rankOneCorrection
  rw [Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, hnormalized]
  simp

/-- The Lemma-5.2 commutator and `T D ξ = -β` imply symmetry of the rank-one
correction for the bilinear form represented by `T`.  This is weighted
symmetry only; quotient descent and positivity are separate exact inputs. -/
theorem rankOneCorrection_weightedSymmetric
    {n : Type*} [Fintype n] [DecidableEq n]
    (T D : Matrix n n ℝ) (xi beta eta : n → ℝ)
    (hT : T.transpose = T)
    (hD : D.transpose = D)
    (hcomm :
      T * D - D * T =
        - Matrix.vecMulVec beta eta + Matrix.vecMulVec eta beta)
    (hTDxi : Matrix.mulVec T (Matrix.mulVec D xi) = -beta) :
    T * rankOneCorrection D xi eta =
      (rankOneCorrection D xi eta).transpose * T := by
  have hrow :
      Matrix.vecMul (Matrix.mulVec D xi) T = -beta := by
    rw [← Matrix.mulVec_transpose, hT, hTDxi]
  unfold rankOneCorrection
  rw [Matrix.mul_sub, Matrix.transpose_sub, hD, Matrix.sub_mul]
  rw [Matrix.mul_vecMulVec, Matrix.transpose_vecMulVec,
    Matrix.vecMulVec_mul, hTDxi, hrow]
  simp only [Matrix.neg_vecMulVec, Matrix.vecMulVec_neg]
  ext i j
  have hij := congrArg (fun M : Matrix n n ℝ => M i j) hcomm
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
    Matrix.vecMulVec_apply] at hij ⊢
  linarith

/-- Combined reusable certificate corresponding to the algebraic part of H8
Lemma 5.4(ii). -/
theorem rankOneCorrection_kernel_and_weightedSymmetric
    {n : Type*} [Fintype n] [DecidableEq n]
    (T D : Matrix n n ℝ) (xi beta eta : n → ℝ)
    (hT : T.transpose = T)
    (hD : D.transpose = D)
    (hcomm :
      T * D - D * T =
        - Matrix.vecMulVec beta eta + Matrix.vecMulVec eta beta)
    (hTDxi : Matrix.mulVec T (Matrix.mulVec D xi) = -beta)
    (hnormalized : eta ⬝ᵥ xi = 1) :
    Matrix.mulVec (rankOneCorrection D xi eta) xi = 0 ∧
      T * rankOneCorrection D xi eta =
        (rankOneCorrection D xi eta).transpose * T := by
  exact ⟨rankOneCorrection_kills_vector D xi eta hnormalized,
    rankOneCorrection_weightedSymmetric T D xi beta eta
      hT hD hcomm hTDxi⟩

#print axioms rankOneCorrection_kills_vector
#print axioms rankOneCorrection_weightedSymmetric
#print axioms rankOneCorrection_kernel_and_weightedSymmetric

end Q3.RouteB
