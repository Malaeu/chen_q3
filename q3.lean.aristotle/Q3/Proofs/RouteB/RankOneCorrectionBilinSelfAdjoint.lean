import Q3.Proofs.RouteB.RankOneCorrectionWeightedSymmetry
import Mathlib.LinearAlgebra.Matrix.BilinearForm

set_option linter.mathlibStandardSet false

noncomputable section

open Matrix

namespace Q3.RouteB

/-- Weighted symmetry in matrix coordinates is exactly self-adjointness for
the represented bilinear form. -/
theorem matrixWeightedSymmetric_isSelfAdjoint_toBilin
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q A : Matrix n n ℝ)
    (hSA : Q * A = A.transpose * Q) :
    LinearMap.IsSelfAdjoint (Matrix.toBilin' Q) A.mulVecLin := by
  intro x y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  calc
    (A *ᵥ x) ⬝ᵥ (Q *ᵥ y) = ((A *ᵥ x) ᵥ* Q) ⬝ᵥ y :=
      dotProduct_mulVec (A *ᵥ x) Q y
    _ = (x ᵥ* (A.transpose * Q)) ⬝ᵥ y := by
      rw [Matrix.vecMul_mulVec]
    _ = (x ᵥ* (Q * A)) ⬝ᵥ y := by
      rw [hSA]
    _ = x ⬝ᵥ ((Q * A) *ᵥ y) :=
      (dotProduct_mulVec x (Q * A) y).symm
    _ = x ⬝ᵥ (Q *ᵥ (A *ᵥ y)) := by
      rw [Matrix.mulVec_mulVec]

/-- The source rank-one matrix identities yield self-adjointness of the exact
corrected ambient endomorphism for the bilinear form represented by `T`. -/
theorem rankOneCorrection_isSelfAdjoint_toBilin
    {n : Type*} [Fintype n] [DecidableEq n]
    (T D : Matrix n n ℝ)
    (xi beta eta : n → ℝ)
    (hT : T.transpose = T)
    (hD : D.transpose = D)
    (hcomm :
      T * D - D * T =
        - Matrix.vecMulVec beta eta + Matrix.vecMulVec eta beta)
    (hTDxi : Matrix.mulVec T (Matrix.mulVec D xi) = -beta) :
    LinearMap.IsSelfAdjoint (Matrix.toBilin' T)
      (rankOneCorrection D xi eta).mulVecLin := by
  apply matrixWeightedSymmetric_isSelfAdjoint_toBilin
  exact rankOneCorrection_weightedSymmetric
    T D xi beta eta hT hD hcomm hTDxi

#print axioms matrixWeightedSymmetric_isSelfAdjoint_toBilin
#print axioms rankOneCorrection_isSelfAdjoint_toBilin

end Q3.RouteB
