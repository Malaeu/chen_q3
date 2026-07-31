import RequestProject.MuntzV3GwinExactClass
import RequestProject.MuntzV3PL1MassBlowupWitness

open Set MeasureTheory Complex

namespace EStarMuntzZeroMassContinuation

/-- Mandatory PL1 plant: the endpoint-jump, nonzero-mass witness is accepted by
the exact-class entire-window theorem. -/
theorem pl1Witness_gwin_entire :
    Differentiable ℂ (Gwin pl1Witness 1) := by
  apply gwin_entire pl1Witness 1 1
  · change Measurable
      ((Set.Ioc (0 : ℝ) 1).indicator (fun t => (t : ℂ) ^ (1 : ℂ)))
    simpa only [Complex.cpow_one, pow_one] using
      (Complex.continuous_ofReal.pow 1).measurable.indicator
        (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))
  · intro u hu
    simp only [pl1Witness, Set.indicator_apply]
    have hout : u ∉ Set.Ioc (0 : ℝ) 1 := by
      intro hui
      exact hu ⟨hui.1.le, hui.2⟩
    simp [hout]
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxw : pl1Witness x = (x : ℂ) := by
      by_cases h0 : x = 0
      · simp [pl1Witness, h0]
      · have hx0 : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0)
        simp [pl1Witness, Set.mem_Ioc, hx0, hx.2.le, Complex.cpow_one]
    have hyw : pl1Witness y = (y : ℂ) := by
      by_cases h0 : y = 0
      · simp [pl1Witness, h0]
      · have hy0 : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm h0)
        simp [pl1Witness, Set.mem_Ioc, hy0, hy.2.le, Complex.cpow_one]
    rw [hxw, hyw]
    simpa using (Complex.isometry_ofReal.dist_eq x y).le
  · norm_num

#print axioms pl1Witness_gwin_entire

end EStarMuntzZeroMassContinuation
