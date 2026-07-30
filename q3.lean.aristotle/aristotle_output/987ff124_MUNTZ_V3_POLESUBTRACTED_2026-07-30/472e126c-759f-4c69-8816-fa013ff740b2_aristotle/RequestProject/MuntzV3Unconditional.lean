import RequestProject.MellinCompactSupportAnalyticity

open scoped BigOperators Real Nat Classical Pointwise
open Set Filter MeasureTheory Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace EStarMuntzZeroMassContinuation

/-- T5 with the v3 Mellin-analyticity hypothesis discharged by the compact
support/Lipschitz bridge. The other analytic inputs are the retained
window/tail layer of the contract. -/
theorem continued_window_identity_unconditional_mellin
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico 0 b))
    (hmass : ∫ u in Set.Ioi (0 : ℝ), h u = 0)
    (Λ : ℝ)
    (hG : AnalyticOnNhd ℂ (Gwin h Λ) shiftedHalfPlane)
    (hRm : AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane)
    (hRp : AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane)
    (habs : ∀ s : ℂ, 1 / 2 < s.re →
      Gwin h Λ s = riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s :=
  continued_window_identity_of_analytic h Λ
    (mellin_compactSupport_analyticOnNhd h b K hmeas hsupp hlip)
    (mellin_one_eq_zero h hmass) hG hRm hRp habs

/-- Punctured raw-product corollary with the v3 Mellin hypothesis discharged. -/
theorem continued_window_identity_raw_off_pole_unconditional_mellin
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico 0 b))
    (hmass : ∫ u in Set.Ioi (0 : ℝ), h u = 0)
    (Λ : ℝ)
    (hG : AnalyticOnNhd ℂ (Gwin h Λ) shiftedHalfPlane)
    (hRm : AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane)
    (hRp : AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane)
    (habs : ∀ s : ℂ, 1 / 2 < s.re →
      Gwin h Λ s = riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re → s ≠ 1 / 2 →
      Gwin h Λ s = riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s :=
  continued_window_identity_raw_off_pole h Λ (mellin_one_eq_zero h hmass)
    (continued_window_identity_unconditional_mellin h b K hmeas hsupp hlip hmass
      Λ hG hRm hRp habs)

/-- Pole-value corollary with the v3 Mellin hypothesis discharged. -/
theorem continued_window_identity_pole_value_unconditional_mellin
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico 0 b))
    (hmass : ∫ u in Set.Ioi (0 : ℝ), h u = 0)
    (Λ : ℝ)
    (hG : AnalyticOnNhd ℂ (Gwin h Λ) shiftedHalfPlane)
    (hRm : AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane)
    (hRp : AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane)
    (habs : ∀ s : ℂ, 1 / 2 < s.re →
      Gwin h Λ s = riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s) :
    Gwin h Λ (1 / 2) =
      deriv (Mellin h) 1 - Rminus h Λ (1 / 2) - Rplus h Λ (1 / 2) :=
  continued_window_identity_pole_value h Λ
    (continued_window_identity_unconditional_mellin h b K hmeas hsupp hlip hmass
      Λ hG hRm hRp habs)

#print axioms continued_window_identity_unconditional_mellin
#print axioms continued_window_identity_raw_off_pole_unconditional_mellin
#print axioms continued_window_identity_pole_value_unconditional_mellin

end EStarMuntzZeroMassContinuation
