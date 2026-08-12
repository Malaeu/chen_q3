/-
  Solution.lean — НЕДОВЕРЕННЫЙ модуль решения: ПОЛОЖИТЕЛЬНАЯ ЗАКЛАДКА.

  Та же формулировка, что в `Challenge.lean`, доказанная обращением к настоящему
  поставщику. Читать его для понимания ЧТО доказано не нужно — для этого есть вызов.

  Ожидаемый исход пробы: СОБИРАЕТСЯ, аксиомы ровно
  `[propext, Classical.choice, Quot.sound]`.
-/
import Q3.Proofs.RouteB.MuntzV3.RplusExactClass

open Set MeasureTheory Complex

namespace Q3Challenge

theorem rplus_analyticOnNhd_shiftedHalfPlane_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (EStarMuntzZeroMassContinuation.Rplus h Λ)
      EStarMuntzZeroMassContinuation.shiftedHalfPlane :=
  EStarMuntzZeroMassContinuation.rplus_analyticOnNhd_shiftedHalfPlane_v3Class
    h b K hmeas hsupp hlip Λ hΛ

end Q3Challenge
