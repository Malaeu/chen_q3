/-  Проба яруса 3: словарная запись H2aAt, три перевода, судит Lean.
    exact? = comparator: кандидат перестаёт быть кандидатом, когда компилятор его принял. -/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Matrix.Spectrum

open Module.End InnerProductSpace

-- ── hbottom: нижняя грань частного Рэлея есть собственное значение ────────────
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) :
    HasEigenvalue T ↑(⨅ x : {x : E // x ≠ 0}, RCLike.re ⟪T x, x⟫_ℝ / ‖(x : E)‖ ^ 2) := by
  exact?

-- ── hsimple: кратность как размерность собственного подпространства ───────────
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (μ : ℝ) (v : E) (hv : v ≠ 0) (h : T v = μ • v) :
    HasEigenvector T μ v := by
  exact?

-- ── heig: собственный вектор эрмитовой МАТРИЦЫ (наш носитель) ─────────────────
example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (i : n) :
    A *ᵥ (hA.eigenvectorBasis i) = hA.eigenvalues i • (hA.eigenvectorBasis i) := by
  exact?
