import Q3.Proofs.RouteB.D0PstarExactArchSymbolLowerBound

set_option linter.mathlibStandardSet false

noncomputable section

open scoped Real

namespace Q3.RouteB.D0Pstar

/-!
# Explicit high-frequency lower bound for the source archimedean symbol

Yoshida's high-mode argument first chooses a frequency threshold beyond which
the archimedean multiplier dominates a prescribed constant.  This file proves
that supplier directly for the production Fourier normalization.  The cutoff
is deliberately crude but fully symbolic and kernel checked; no sampled
digamma maximum or numerical enclosure is consumed.

This is only the pointwise symbol half of the source coercivity argument.  The
low-frequency Fourier-mass estimate for high periodic modes remains separate.
-/

private lemma b3_0ak_one_fourth_le_norm_sourceArchimedeanArgument
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

private lemma b3_0ak_sourceArchimedeanStieltjesCorrection_le
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
      b3_0ak_one_fourth_le_norm_sourceArchimedeanArgument t
  have hsq : (1 / 16 : ℝ) ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - 1 / 4)]
  have hden_pos : 0 < 2 * ‖z‖ ^ 2 := by
    have : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hlower
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

private lemma b3_0ak_sourceArchimedeanStieltjesRemainder_le
    (t : ℝ) :
    1 / (4 * ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ^ 2) ≤ 4 := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using
      b3_0ak_one_fourth_le_norm_sourceArchimedeanArgument t
  have hsq : (1 / 16 : ℝ) ≤ ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - 1 / 4)]
  have hden_pos : 0 < 4 * ‖z‖ ^ 2 := by
    have : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hlower
    positivity
  rw [show ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ = ‖z‖ by rfl]
  apply (div_le_iff₀ hden_pos).2
  nlinarith

/-- The production archimedean multiplier dominates its literal logarithmic
main term minus one explicit global constant. -/
theorem sourceArchimedeanMultiplier_ge_logNorm_sub_explicitShift
    (t : ℝ) :
    Real.log
          ‖(1 / 4 : ℂ) +
            Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ -
        (|Real.log Real.pi| + 6) ≤
      sourceArchimedeanMultiplier t := by
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
  have hcorr : |z.re / (2 * ‖z‖ ^ 2)| ≤ 2 := by
    simpa [z] using
      b3_0ak_sourceArchimedeanStieltjesCorrection_le t
  have hrem4 : 1 / (4 * ‖z‖ ^ 2) ≤ 4 := by
    simpa [z] using
      b3_0ak_sourceArchimedeanStieltjesRemainder_le t
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
  have hE_lower : -4 ≤ E :=
    (abs_le.mp (hE.trans hrem4)).1
  rw [show
    Real.log
          ‖(1 / 4 : ℂ) +
            Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ =
      Real.log ‖z‖ by rfl]
  rw [hdecomp]
  nlinarith

/-- A fully explicit Yoshida-style frequency threshold: outside
`exp (C + |log pi| + 6)`, the production archimedean multiplier is at least
`C`.  The threshold is analytic and intentionally not optimized. -/
theorem sourceArchimedeanMultiplier_ge_of_exp_shift_le_abs
    (C t : ℝ)
    (ht : Real.exp (C + |Real.log Real.pi| + 6) ≤ |t|) :
    C ≤ sourceArchimedeanMultiplier t := by
  let z : ℂ :=
    (1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hpi_one : (1 : ℝ) ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hz_im : z.im = Real.pi * t := by
    simp [z]
  have habs_le_norm : |t| ≤ ‖z‖ := by
    calc
      |t| = 1 * |t| := by ring
      _ ≤ Real.pi * |t| :=
        mul_le_mul_of_nonneg_right hpi_one (abs_nonneg t)
      _ = |z.im| := by
        rw [hz_im, abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ ‖z‖ := by
        simpa using (RCLike.abs_im_le_norm z)
  have hexp_le_norm :
      Real.exp (C + |Real.log Real.pi| + 6) ≤ ‖z‖ :=
    ht.trans habs_le_norm
  have hlog :
      C + |Real.log Real.pi| + 6 ≤ Real.log ‖z‖ := by
    calc
      C + |Real.log Real.pi| + 6 =
          Real.log (Real.exp (C + |Real.log Real.pi| + 6)) := by
        rw [Real.log_exp]
      _ ≤ Real.log ‖z‖ :=
        Real.log_le_log (Real.exp_pos _) hexp_le_norm
  have hbase :=
    sourceArchimedeanMultiplier_ge_logNorm_sub_explicitShift t
  rw [show
    ‖(1 / 4 : ℂ) +
        Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ = ‖z‖ by rfl] at hbase
  nlinarith

#print axioms sourceArchimedeanMultiplier_ge_logNorm_sub_explicitShift
#print axioms sourceArchimedeanMultiplier_ge_of_exp_shift_le_abs

end Q3.RouteB.D0Pstar
