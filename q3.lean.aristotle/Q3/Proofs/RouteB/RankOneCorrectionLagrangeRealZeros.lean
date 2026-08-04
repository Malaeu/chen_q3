import Q3.Proofs.RouteB.RankOneCorrectionLagrangeRadicalCharpoly
import Q3.Proofs.RouteB.QuotientByRadicalRealZeroConsumer
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

open Matrix

/-- A symmetric matrix represents a symmetric bilinear form in the standard
coordinate basis. -/
theorem matrixToBilin_isSymm_of_transpose_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (hT : T.transpose = T) :
    (Matrix.toBilin' T).IsSymm := by
  refine ⟨?_⟩
  intro x y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  calc
    x ⬝ᵥ (T *ᵥ y) = (x ᵥ* T) ⬝ᵥ y := dotProduct_mulVec x T y
    _ = (T.transpose *ᵥ x) ⬝ᵥ y := by rw [Matrix.mulVec_transpose]
    _ = (T *ᵥ x) ⬝ᵥ y := by rw [hT]
    _ = y ⬝ᵥ (T *ᵥ x) := dotProduct_comm _ _

/-- Scalar extension of a basis matrix commutes with passage from a linear
endomorphism to its characteristic polynomial. -/
theorem toMatrix_map_charpoly_eq_linearMap_charpoly_map
    {V ι : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (A : Module.End ℝ V) :
    ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ)).charpoly =
      A.charpoly.map (algebraMap ℝ ℂ) := by
  rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

/-- Under the explicit nonnegativity premise on the exact source form, the
complexified source Lagrange polynomial has only real zeros. -/
theorem sourceLagrangePolynomial_complex_zerosRealOn_of_radical_nonneg
    {n ι : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι]
    (T : Matrix n n ℝ)
    (lam xi beta : n → ℝ)
    (hT : T.transpose = T)
    (hpos : ∀ x, 0 ≤ Matrix.toBilin' T x x)
    (hcomm :
      T * Matrix.diagonal lam - Matrix.diagonal lam * T =
        - Matrix.vecMulVec beta (1 : n → ℝ) +
          Matrix.vecMulVec (1 : n → ℝ) beta)
    (hTDxi :
      Matrix.mulVec T (Matrix.mulVec (Matrix.diagonal lam) xi) = -beta)
    (hnormalized : (1 : n → ℝ) ⬝ᵥ xi = 1)
    (hTxi : Matrix.mulVec T xi = 0)
    (hker1 : Module.finrank ℝ (LinearMap.ker T.mulVecLin) = 1)
    (b : Module.Basis ι ℝ
      ((n → ℝ) ⧸ LinearMap.ker (Matrix.toBilin' T))) :
    ZerosRealOn Set.univ
      (fun z =>
        ((sourceLagrangePolynomial lam xi).map
          (algebraMap ℝ ℂ)).eval z) := by
  let B : LinearMap.BilinForm ℝ (n → ℝ) := Matrix.toBilin' T
  let A : Module.End ℝ (n → ℝ) :=
    (rankOneCorrection
      (Matrix.diagonal lam) xi (1 : n → ℝ)).mulVecLin
  have hB : B.IsSymm := matrixToBilin_isSymm_of_transpose_eq T hT
  have hself : LinearMap.IsSelfAdjoint B A :=
    rankOneCorrection_isSelfAdjoint_toBilin
      T (Matrix.diagonal lam) xi beta (1 : n → ℝ)
      hT (by simp) hcomm hTDxi
  apply zerosRealOn_of_quotientByRadical_charpoly_mul
    B hB hpos A hself b
    (fun z =>
      ((sourceLagrangePolynomial lam xi).map
        (algebraMap ℝ ℂ)).eval z)
    (fun _ => -((-1 : ℂ) ^ Fintype.card n))
    (fun _ => 1)
  · intro z
    simp
  · intro z hz hzero
    simp at hzero
  · intro z
    have hsource :=
      sourceLagrangePolynomial_eq_signed_radical_quotient_charpoly
        T lam xi beta hT hcomm hTDxi hnormalized hTxi hker1
    have hmap := congrArg
      (fun p : Polynomial ℝ =>
        (p.map (algebraMap ℝ ℂ)).eval z) hsource
    have hchar :=
      toMatrix_map_charpoly_eq_linearMap_charpoly_map b
        (quotientByRadicalEnd B A hself)
    rw [hchar]
    simpa [B, A] using hmap

#print axioms matrixToBilin_isSymm_of_transpose_eq
#print axioms toMatrix_map_charpoly_eq_linearMap_charpoly_map
#print axioms sourceLagrangePolynomial_complex_zerosRealOn_of_radical_nonneg

end Q3.RouteB
