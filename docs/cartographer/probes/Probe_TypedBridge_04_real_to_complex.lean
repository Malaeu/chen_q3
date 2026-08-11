import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
set_option maxHeartbeats 800000
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem real_symm_map_complex_isHermitian (A : Matrix n n ℝ) (h : Aᵀ = A) :
    (A.map (algebraMap ℝ ℂ)).IsHermitian := by
  ext i j
  have hji : A j i = A i j := by
    have := congrFun (congrFun h i) j
    simpa [Matrix.transpose_apply] using this
  simp [Matrix.conjTranspose_apply, Matrix.map_apply, hji, Complex.star_def,
        Complex.conj_ofReal]

#print axioms real_symm_map_complex_isHermitian
