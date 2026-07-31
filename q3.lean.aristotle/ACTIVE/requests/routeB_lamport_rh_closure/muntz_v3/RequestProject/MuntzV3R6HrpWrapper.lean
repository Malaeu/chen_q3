import RequestProject.Main
import RequestProject.R6Export.TailAnalyticity

open Set Complex

namespace EStarMuntzZeroMassContinuation

/-- R6 supplies the v3 hRp consumer under its original global hypotheses. -/
theorem rplus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane := by
  have hdiff : Differentiable ℂ (Rplus h Λ) := by
    change Differentiable ℂ (R6Export.Rplus h Λ)
    exact R6Export.Rplus_differentiable h a b ha hab K hsupp hlip Λ hΛ
  exact hdiff.differentiableOn.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

end EStarMuntzZeroMassContinuation

