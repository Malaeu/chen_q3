-- ПРОГОН №3 (зависимые типы: размерность растёт с индексом, как у CCM). Разрез `hfactor` на две связки по разбору Мифоса 2026-08-11.
--
-- Гипотеза: остаток сжимается ровно в [family ↔ Лагранж с нормировкой c_N],
-- а [Лагранж ↔ вещественность] уже закрыт полкой.
--
-- Маршрут КОРОЧЕ вчерашнего: `..._zerosRealOn_of_radical_nonneg` даёт вещественность
-- прямо на Лагранже, минуя charpoly, M1 и β8d целиком. Это R3-P3 Мифоса.
import Q3.Proofs.RouteB.CanonicalRHRouteSkeleton
import Q3.Proofs.RouteB.RankOneCorrectionLagrangeRealZeros

set_option maxHeartbeats 1000000
open Q3.RouteB Q3.RouteB.CanonicalRHRoute Matrix

/-- `Theorem510RealZeroBridge` из ОДНОГО недостающего звена: семейство есть ненулевая
кратность лагранжева многочлена. Всё остальное — полка. -/
theorem theorem510_of_lagrange_normalization
    {Index : Type*} (C : CanonicalApproximation Index) (H2aAt : Index → Prop)
    (n ι : Index → Type)
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (T : ∀ i, Matrix (n i) (n i) ℝ)
    (lam xi beta : ∀ i, n i → ℝ)
    (hT : ∀ i, (T i).transpose = T i)
    (hpos : ∀ i x, 0 ≤ Matrix.toBilin' (T i) x x)
    (hcomm : ∀ i,
      T i * Matrix.diagonal (lam i) - Matrix.diagonal (lam i) * T i =
        - Matrix.vecMulVec (beta i) (1 : n i → ℝ) +
          Matrix.vecMulVec (1 : n i → ℝ) (beta i))
    (hTDxi : ∀ i,
      Matrix.mulVec (T i) (Matrix.mulVec (Matrix.diagonal (lam i)) (xi i)) = -(beta i))
    (hnormalized : ∀ i, (1 : n i → ℝ) ⬝ᵥ xi i = 1)
    (hTxi : ∀ i, Matrix.mulVec (T i) (xi i) = 0)
    (hker1 : ∀ i, Module.finrank ℝ (LinearMap.ker (T i).mulVecLin) = 1)
    (b : ∀ i, Module.Basis (ι i) ℝ ((n i → ℝ) ⧸ LinearMap.ker (Matrix.toBilin' (T i))))
    -- ── ЕДИНСТВЕННОЕ НЕДОСТАЮЩЕЕ ЗВЕНО ──
    (cN : Index → ℂ) (hcN : ∀ i, cN i ≠ 0)
    (hfamily : ∀ i z, C.Pstar.family i z =
      cN i * ((sourceLagrangePolynomial (lam i) (xi i)).map (algebraMap ℝ ℂ)).eval z) :
    Theorem510RealZeroBridge C H2aAt := by
  intro i _ _
  have hzr :=
    sourceLagrangePolynomial_complex_zerosRealOn_of_radical_nonneg
      (T i) (lam i) (xi i) (beta i) (hT i) (hpos i) (hcomm i) (hTDxi i)
      (hnormalized i) (hTxi i) (hker1 i) (b i)
  intro z _ hz
  have hL : ((sourceLagrangePolynomial (lam i) (xi i)).map (algebraMap ℝ ℂ)).eval z = 0 := by
    have := hfamily i z
    rw [this] at hz
    exact (mul_eq_zero.mp hz).resolve_left (hcN i)
  exact hzr z (Set.mem_univ z) hL

#print axioms theorem510_of_lagrange_normalization
