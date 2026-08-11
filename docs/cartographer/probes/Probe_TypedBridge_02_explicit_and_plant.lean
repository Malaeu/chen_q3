-- Фаза 2 — ЯВНЫЙ ТЕРМ (не подсказка поиска) + Фаза 4 — ОТРИЦАТЕЛЬНЫЙ КОНТРОЛЬ.
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

set_option maxHeartbeats 1000000

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- МОСТ. Ровно то, что даёт наш `ccmWeilMatFinite_transpose_eq`. -/
theorem transpose_eq_toEuclideanLin_isSymmetric
    (A : Matrix n n ℝ) (h : Aᵀ = A) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  isHermitian_iff_isSymmetric.mp h

/-- RAYLEIGH. Заключение НЕ ослаблено: скопировано из типа Фазы 0. -/
theorem transpose_eq_hasEigenvalue_iInf_rayleigh
    [Nonempty n] (A : Matrix n n ℝ) (h : Aᵀ = A) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin A)
      ↑(⨅ x : { x : EuclideanSpace ℝ n // x ≠ 0 },
          RCLike.re (inner ℝ (Matrix.toEuclideanLin A ↑x) ↑x)
            / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) :=
  (transpose_eq_toEuclideanLin_isSymmetric A h).hasEigenvalue_iInf_of_finiteDimensional

#print axioms transpose_eq_toEuclideanLin_isSymmetric
#print axioms transpose_eq_hasEigenvalue_iInf_rayleigh

-- ─────────── ФАЗА 4: ОТРИЦАТЕЛЬНЫЙ КОНТРОЛЬ ───────────
-- Произвольная НЕсимметричная 2×2. Мост обязан НЕ закрыться.
-- Ожидается ошибка компиляции; её отсутствие = H2A_PLANT_NOT_REJECTED.
noncomputable def plantM : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

example : (Matrix.toEuclideanLin plantM).IsSymmetric := by exact?
