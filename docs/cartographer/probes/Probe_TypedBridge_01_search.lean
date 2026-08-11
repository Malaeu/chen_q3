-- Фаза 1 — ПОЗИТИВНЫЙ поиск. Цель списана с сигнатуры нашего потребителя
-- `ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple`
-- (CCMFiniteWeilBottomSpectral.lean:61) и из вывода Фазы 0, не из головы.
--
-- Наш вход, который УЖЕ доказан: `ccmWeilMatFinite_transpose_eq : Aᵀ = A`.
-- Целевой носитель Mathlib из Фазы 0: `EuclideanSpace ℝ n`.
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

set_option maxHeartbeats 1000000

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

-- ШАГ 1. Aᵀ = A  ⟹  A.IsHermitian   (над ℝ: star = id)
example (A : Matrix n n ℝ) (h : Aᵀ = A) : A.IsHermitian := by exact?

-- ШАГ 2. A.IsHermitian  ⟹  оператор Евклида симметричен   (МОСТ)
example (A : Matrix n n ℝ) (h : A.IsHermitian) :
    (Matrix.toEuclideanLin A).IsSymmetric := by exact?

-- ШАГ 3. Цепь целиком: ровно то, что даёт наш `ccmWeilMatFinite_transpose_eq`
example (A : Matrix n n ℝ) (h : Aᵀ = A) :
    (Matrix.toEuclideanLin A).IsSymmetric := by exact?

-- ШАГ 4. Заключение Rayleigh, скопированное из вывода Фазы 0 дословно.
example [Nonempty n] (A : Matrix n n ℝ) (h : Aᵀ = A) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin A)
      ↑(⨅ x : { x : EuclideanSpace ℝ n // x ≠ 0 },
          RCLike.re (inner ℝ (Matrix.toEuclideanLin A ↑x) ↑x) / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) := by
  exact?
