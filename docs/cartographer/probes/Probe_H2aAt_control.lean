/-  Проба яруса 3, второй заход: сперва убедиться, что МЕТОД работает, — цель,
    для которой лемма заведомо существует. Потом наши формулировки.  -/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum

open Module.End

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}

-- (A) контроль метода: точная сигнатура hasEigenvalue_iInf_of_finiteDimensional
example [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T ↑(⨅ x : { x : E // x ≠ 0 }, RCLike.re ⟪T x, x⟫_𝕜 / ‖(x : E)‖ ^ 2 : ℝ) := by
  exact?

-- (B) наш hsimple: собственный вектор из уравнения — есть ли готовое
example (μ : 𝕜) (v : E) (hv : v ≠ 0) (h : T v = μ • v) : HasEigenvector T μ v := by
  exact?

-- (C) наш носитель: собственное значение эрмитовой матрицы вещественно
example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (i : n) :
    (hA.eigenvalues i : ℝ) = hA.eigenvalues i := by
  exact?
