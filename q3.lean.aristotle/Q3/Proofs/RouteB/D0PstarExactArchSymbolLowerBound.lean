import Q3.Proofs.RouteB.D0PstarExactArchSymbolLogDomination

noncomputable section

open scoped Real

namespace Q3.RouteB.D0Pstar

private lemma b3_0n_one_fourth_le_norm_sourceArchimedeanArgument
    (t : ℝ) :
    (1 / 4 : ℝ) ≤
      ‖(1 / 4 : ℂ) +
        Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hre : |z.re| ≤ ‖z‖ := by
    simpa using (RCLike.abs_re_le_norm z)
  simpa [z, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] using hre

private lemma b3_0n_sourceArchimedeanStieltjesCorrection_le
    (t : ℝ) :
    |(((1 / 4 : ℂ) +
        Complex.I * ((Real.pi * t : ℝ) : ℂ))).re /
        (2 * ‖(1 / 4 : ℂ) +
          Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ^ 2)| ≤ 2 := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using
      b3_0n_one_fourth_le_norm_sourceArchimedeanArgument t
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le (by norm_num) hlower
  have hsq : (1 / 16 : ℝ) ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - 1 / 4)]
  have hden_pos : 0 < 2 * ‖z‖ ^ 2 := by
    positivity
  have hnonneg : 0 ≤ z.re / (2 * ‖z‖ ^ 2) := by
    rw [show z.re = (1 / 4 : ℝ) by simp [z]]
    positivity
  rw [show (((1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ))).re = z.re by rfl]
  rw [show ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ = ‖z‖ by rfl]
  rw [abs_of_nonneg hnonneg,
    show z.re = (1 / 4 : ℝ) by simp [z]]
  apply (div_le_iff₀ hden_pos).2
  nlinarith

private lemma b3_0n_sourceArchimedeanStieltjesRemainder_le
    (t : ℝ) :
    1 / (4 * ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ^ 2) ≤ 4 := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using
      b3_0n_one_fourth_le_norm_sourceArchimedeanArgument t
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le (by norm_num) hlower
  have hsq : (1 / 16 : ℝ) ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - 1 / 4)]
  have hden_pos : 0 < 4 * ‖z‖ ^ 2 := by
    positivity
  rw [show ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ = ‖z‖ by rfl]
  apply (div_le_iff₀ hden_pos).2
  nlinarith

/-- The exact source archimedean multiplier has a source-derived uniform
lower bound.  Equivalently, the displayed finite constant shift makes the
multiplier pointwise nonnegative. -/
theorem sourceArchimedeanMultiplier_add_explicitShift_nonneg
    (t : ℝ) :
    0 ≤ sourceArchimedeanMultiplier t +
      (|Real.log Real.pi| + Real.log 4 + 6) := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hz : 0 < z.re := by
    simp [z]
  have hrem := Q3.re_digamma_remainder_bound_stieltjes z hz
  let E : ℝ :=
    (Q3.digamma z).re - Real.log ‖z‖ +
      z.re / (2 * ‖z‖ ^ 2)
  have hE : |E| ≤ 1 / (4 * ‖z‖ ^ 2) := by
    simpa [E] using hrem
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using
      b3_0n_one_fourth_le_norm_sourceArchimedeanArgument t
  have hlog_quarter :
      Real.log (1 / 4 : ℝ) ≤ Real.log ‖z‖ :=
    Real.log_le_log (by norm_num) hlower
  have hlog_lower : -Real.log 4 ≤ Real.log ‖z‖ := by
    have hlog_inv : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hlog_inv] at hlog_quarter
    exact hlog_quarter
  have hcorr : |z.re / (2 * ‖z‖ ^ 2)| ≤ 2 := by
    simpa [z] using
      b3_0n_sourceArchimedeanStieltjesCorrection_le t
  have hrem4 :
      1 / (4 * ‖z‖ ^ 2) ≤ 4 := by
    simpa [z] using
      b3_0n_sourceArchimedeanStieltjesRemainder_le t
  have hE4 : |E| ≤ 4 := hE.trans hrem4
  have hdecomp :
      sourceArchimedeanMultiplier t =
        -Real.log Real.pi + Real.log ‖z‖ -
          z.re / (2 * ‖z‖ ^ 2) + E := by
    simp only [sourceArchimedeanMultiplier, z, E]
    ring
  have hpi : -|Real.log Real.pi| ≤ -Real.log Real.pi := by
    exact neg_le_neg (le_abs_self (Real.log Real.pi))
  have hcorr_upper : z.re / (2 * ‖z‖ ^ 2) ≤ 2 :=
    (abs_le.mp hcorr).2
  have hE_lower : -4 ≤ E := (abs_le.mp hE4).1
  rw [hdecomp]
  nlinarith

#print axioms sourceArchimedeanMultiplier_add_explicitShift_nonneg

end Q3.RouteB.D0Pstar
