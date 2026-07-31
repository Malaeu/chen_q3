import RequestProject.Main
import RequestProject.R6Export.TailAnalyticity

open MeasureTheory Set Complex

namespace EStarMuntzZeroMassContinuation

/-- The v3 and exported R6 half-planes are propositionally equal. -/
lemma shiftedHalfPlane_eq_r6HalfPlane :
    shiftedHalfPlane = {s : ℂ | -(1 : ℝ) / 2 < s.re} := by
  ext s
  simp only [shiftedHalfPlane, Set.mem_setOf_eq]
  norm_num

/-- R6 supplies the v3 hRm consumer under its original global hypotheses. -/
theorem rminus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane := by
  rw [shiftedHalfPlane_eq_r6HalfPlane]
  have hdiff :
      DifferentiableOn ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re} := by
    change DifferentiableOn ℂ (R6Export.Rminus h Λ)
      {s : ℂ | -(1 : ℝ) / 2 < s.re}
    exact R6Export.Rminus_differentiableOn_halfPlane
      h a b ha hab K hsupp hlip hmass Λ hΛ
  exact hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end EStarMuntzZeroMassContinuation
