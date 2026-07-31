import RequestProject.Main
import RequestProject.R6Export.RiemannBoundaryCellBridge

open Set MeasureTheory Complex
open scoped BigOperators

namespace EStarMuntzZeroMassContinuation

/-- The sealed E-star square-root bound on the exact v3 class, with the
minimal nonnegative-support-endpoint guard required by its explicit constant. -/
theorem EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      ‖Estar h u‖ ≤
        (K * b + (‖h 0‖ + K * b) + ‖h b‖) * Real.sqrt u := by
  intro u hu
  by_cases hb0 : b = 0
  · subst b
    have hterms : ∀ n : ℕ+, h ((n : ℝ) * u) = 0 := by
      intro n
      apply hsupp
      simp only [Set.mem_Icc, not_and_or]
      right
      exact not_le_of_gt (mul_pos (by positivity) hu.1)
    have hEstar : Estar h u = 0 := by
      simp [Estar, hterms]
    rw [hEstar, norm_zero]
    positivity
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    change ‖_root_.Estar h u‖ ≤ _
    exact riemannBoundaryCellBridge_Estar
      h b hbpos K hsupp hlip hmeas hmass u hu

#print axioms EstarBoundedBySqrtOfZeroMass_IccZero_IcoLipschitz

end EStarMuntzZeroMassContinuation
