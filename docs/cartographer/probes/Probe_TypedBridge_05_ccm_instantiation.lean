-- ИНСТАНЦИРОВАНИЕ на настоящей ccmWeilMatFinite. Цель списана с сигнатуры потребителя.
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

set_option maxHeartbeats 1000000
open Matrix Q3.RouteB

/-- МОСТ на конкретной CCM-матрице. -/
theorem ccmWeilMatFinite_toEuclideanLin_isSymmetric
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    (Matrix.toEuclideanLin (ccmWeilMatFinite mProject N)).IsSymmetric :=
  isHermitian_iff_isSymmetric.mp (ccmWeilMatFinite_transpose_eq mProject N hm hN)

/-- RAYLEIGH на конкретной CCM-матрице. Заключение не ослаблено. -/
theorem ccmWeilMatFinite_hasEigenvalue_iInf_rayleigh
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (ccmWeilMatFinite mProject N))
      ↑(⨅ x : { x : EuclideanSpace ℝ (CCMModeFinite N) // x ≠ 0 },
          RCLike.re (inner ℝ (Matrix.toEuclideanLin (ccmWeilMatFinite mProject N) ↑x) ↑x)
            / ‖(x : EuclideanSpace ℝ (CCMModeFinite N))‖ ^ 2) :=
  (ccmWeilMatFinite_toEuclideanLin_isSymmetric mProject N hm hN).hasEigenvalue_iInf_of_finiteDimensional

/-- ПОДЪЁМ ℝ→ℂ на конкретной CCM-матрице: вход обоих наших станков над ℂ. -/
theorem ccmWeilMatFinite_map_complex_isHermitian
    (mProject N : ℕ) (hm : 2 ≤ mProject) (hN : 1 ≤ N) :
    ((ccmWeilMatFinite mProject N).map (algebraMap ℝ ℂ)).IsHermitian := by
  ext i j
  have hji := congrFun (congrFun (ccmWeilMatFinite_transpose_eq mProject N hm hN) i) j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply,
        Complex.conj_ofReal] at hji ⊢
  simpa using hji

#print axioms ccmWeilMatFinite_toEuclideanLin_isSymmetric
#print axioms ccmWeilMatFinite_hasEigenvalue_iInf_rayleigh
#print axioms ccmWeilMatFinite_map_complex_isHermitian
