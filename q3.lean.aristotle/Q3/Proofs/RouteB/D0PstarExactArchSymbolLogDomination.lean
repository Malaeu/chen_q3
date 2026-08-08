import Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
import Q3.DigammaRemainder

/-!
# Goal 057 B3.0B2: exact archimedean-symbol domination

This file places the source archimedean multiplier in the same
cycles-per-unit frequency coordinate used by Mathlib's Fourier transform.
It proves a global explicit logarithmic majorant directly from the
foundational Stieltjes remainder, without importing the generated PSD/Step33
backend.

The result is only a pointwise source-symbol certificate.  The exact-symbol
weighted-`L²` transfer is the separate B3.0B3 child.
-/

noncomputable section

open scoped Real

namespace Q3.RouteB.D0Pstar

/--
The source archimedean multiplier in the same frequency coordinate used by
Mathlib's Fourier kernel `exp (-2 * pi * I * x * t)`.

This equals the paper's angular-frequency multiplier `hPlus` evaluated at
`2 * pi * t`.
-/
def sourceArchimedeanMultiplier (t : ℝ) : ℝ :=
  -Real.log Real.pi +
    (Q3.digamma
      ((1 / 4 : ℂ) +
        Complex.I * ((Real.pi * t : ℝ) : ℂ))).re

/-- Exact normalization in the production Mathlib Fourier coordinate. -/
theorem sourceArchimedeanMultiplier_eq_neg_aStar_scaled
    (t : ℝ) :
    sourceArchimedeanMultiplier t =
      -Q3.a_star t / (2 * Real.pi) := by
  unfold sourceArchimedeanMultiplier Q3.a_star Q3.a
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

private lemma sourceArchimedeanArgument_re (t : ℝ) :
    (((1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ))).re = (1 / 4 : ℝ) := by
  simp

private lemma one_fourth_le_norm_sourceArchimedeanArgument (t : ℝ) :
    (1 / 4 : ℝ) ≤
      ‖(1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ := by
  let z : ℂ :=
    (1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hre : |z.re| ≤ ‖z‖ := by
    simpa using (RCLike.abs_re_le_norm z)
  simpa [z, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] using hre

private lemma norm_sourceArchimedeanArgument_le (t : ℝ) :
    ‖(1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ≤
      4 * (2 + |t|) := by
  have htri :
      ‖(1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ≤
        ‖(1 / 4 : ℂ)‖ +
          ‖Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ :=
    norm_add_le _ _
  have hpi : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
  have habs_nonneg : 0 ≤ |t| := abs_nonneg t
  have hmul : Real.pi * |t| ≤ 4 * |t| :=
    mul_le_mul_of_nonneg_right hpi habs_nonneg
  calc
    ‖(1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)‖
        ≤ ‖(1 / 4 : ℂ)‖ +
            ‖Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ := htri
    _ = (1 / 4 : ℝ) + Real.pi * |t| := by
      simp [abs_of_pos Real.pi_pos]
    _ ≤ (1 / 4 : ℝ) + 4 * |t| := by linarith
    _ ≤ 4 * (2 + |t|) := by linarith

private lemma abs_log_norm_sourceArchimedeanArgument_le (t : ℝ) :
    |Real.log
        ‖(1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)‖| ≤
      Real.log 4 + Real.log (2 + |t|) := by
  let z : ℂ :=
    (1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using one_fourth_le_norm_sourceArchimedeanArgument t
  have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hlower
  have hupper : ‖z‖ ≤ 4 * (2 + |t|) := by
    simpa [z] using norm_sourceArchimedeanArgument_le t
  have htwo_pos : 0 < (2 + |t| : ℝ) := by positivity
  have hfour_pos : (0 : ℝ) < 4 := by norm_num
  have hlog_upper :
      Real.log ‖z‖ ≤ Real.log 4 + Real.log (2 + |t|) := by
    calc
      Real.log ‖z‖ ≤ Real.log (4 * (2 + |t|)) :=
        Real.log_le_log hnorm_pos hupper
      _ = Real.log 4 + Real.log (2 + |t|) := by
        rw [Real.log_mul (ne_of_gt hfour_pos) (ne_of_gt htwo_pos)]
  have hlog_lower :
      -(Real.log 4 + Real.log (2 + |t|)) ≤ Real.log ‖z‖ := by
    have hlog_quarter : Real.log (1 / 4 : ℝ) ≤ Real.log ‖z‖ :=
      Real.log_le_log (by norm_num) hlower
    have hlog_two_nonneg : 0 ≤ Real.log (2 + |t|) := by
      exact Real.log_nonneg (by linarith [abs_nonneg t])
    have hlog_four : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hlog_four] at hlog_quarter
    linarith
  exact abs_le.mpr ⟨hlog_lower, hlog_upper⟩

private lemma sourceArchimedeanStieltjesCorrection_le (t : ℝ) :
    |(((1 / 4 : ℂ) +
        Complex.I * ((Real.pi * t : ℝ) : ℂ))).re /
        (2 * ‖(1 / 4 : ℂ) +
          Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ^ 2)| ≤ 2 := by
  let z : ℂ :=
    (1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using one_fourth_le_norm_sourceArchimedeanArgument t
  have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hlower
  have hsq : (1 / 16 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1 / 4)]
  have hden_pos : 0 < 2 * ‖z‖ ^ 2 := by positivity
  have hnonneg : 0 ≤ z.re / (2 * ‖z‖ ^ 2) := by
    rw [show z.re = (1 / 4 : ℝ) by simp [z]]
    positivity
  rw [show (((1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ))).re = z.re by rfl]
  rw [show ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ = ‖z‖ by rfl]
  rw [abs_of_nonneg hnonneg, show z.re = (1 / 4 : ℝ) by simp [z]]
  apply (div_le_iff₀ hden_pos).2
  nlinarith

private lemma sourceArchimedeanStieltjesRemainder_le (t : ℝ) :
    1 / (4 * ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ ^ 2) ≤ 4 := by
  let z : ℂ :=
    (1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa [z] using one_fourth_le_norm_sourceArchimedeanArgument t
  have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hlower
  have hsq : (1 / 16 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1 / 4)]
  have hden_pos : 0 < 4 * ‖z‖ ^ 2 := by positivity
  rw [show ‖(1 / 4 : ℂ) +
      Complex.I * ((Real.pi * t : ℝ) : ℂ)‖ = ‖z‖ by rfl]
  apply (div_le_iff₀ hden_pos).2
  nlinarith

/--
Global source-faithful logarithmic domination in the production Fourier
coordinate.  The explicit constant is analytic, not fitted or supplied as a
premise.
-/
theorem abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope
    (t : ℝ) :
    |sourceArchimedeanMultiplier t| ≤
      (|Real.log Real.pi| + Real.log 4 + 7) *
        vModeLogGrowthEnvelope t := by
  let z : ℂ :=
    (1 / 4 : ℂ) + Complex.I * ((Real.pi * t : ℝ) : ℂ)
  have hz : 0 < z.re := by simp [z]
  have hrem := Q3.re_digamma_remainder_bound_stieltjes z hz
  let E : ℝ :=
    (Q3.digamma z).re - Real.log ‖z‖ + z.re / (2 * ‖z‖ ^ 2)
  have hE : |E| ≤ 1 / (4 * ‖z‖ ^ 2) := by
    simpa [E] using hrem
  have hdecomp :
      sourceArchimedeanMultiplier t =
        -Real.log Real.pi + Real.log ‖z‖ -
          z.re / (2 * ‖z‖ ^ 2) + E := by
    simp only [sourceArchimedeanMultiplier, z, E]
    ring
  have hlog : |Real.log ‖z‖| ≤ Real.log 4 + Real.log (2 + |t|) := by
    simpa [z] using abs_log_norm_sourceArchimedeanArgument_le t
  have hcorr : |z.re / (2 * ‖z‖ ^ 2)| ≤ 2 := by
    simpa [z] using sourceArchimedeanStieltjesCorrection_le t
  have hrem4 : |E| ≤ 4 := by
    exact hE.trans (by
      simpa [z] using sourceArchimedeanStieltjesRemainder_le t)
  have hbase :
      |sourceArchimedeanMultiplier t| ≤
        |Real.log Real.pi| + Real.log 4 + Real.log (2 + |t|) + 6 := by
    rw [hdecomp]
    calc
      |-Real.log Real.pi + Real.log ‖z‖ -
          z.re / (2 * ‖z‖ ^ 2) + E|
          ≤ |-Real.log Real.pi| + |Real.log ‖z‖| +
              |z.re / (2 * ‖z‖ ^ 2)| + |E| := by
            calc
              |-Real.log Real.pi + Real.log ‖z‖ -
                  z.re / (2 * ‖z‖ ^ 2) + E|
                  ≤ |-Real.log Real.pi + Real.log ‖z‖ -
                      z.re / (2 * ‖z‖ ^ 2)| + |E| := abs_add_le _ _
              _ ≤ (|-Real.log Real.pi + Real.log ‖z‖| +
                    |z.re / (2 * ‖z‖ ^ 2)|) + |E| :=
                  by
                    have hsub :=
                      abs_sub
                        (-Real.log Real.pi + Real.log ‖z‖)
                        (z.re / (2 * ‖z‖ ^ 2))
                    linarith
              _ ≤ ((|-Real.log Real.pi| + |Real.log ‖z‖|) +
                    |z.re / (2 * ‖z‖ ^ 2)|) + |E| :=
                  by
                    have hfirst :=
                      abs_add_le (-Real.log Real.pi) (Real.log ‖z‖)
                    linarith
              _ = |-Real.log Real.pi| + |Real.log ‖z‖| +
                    |z.re / (2 * ‖z‖ ^ 2)| + |E| := by ring
      _ ≤ |Real.log Real.pi| +
            (Real.log 4 + Real.log (2 + |t|)) + 2 + 4 := by
          simp only [abs_neg]
          linarith
      _ = |Real.log Real.pi| + Real.log 4 +
            Real.log (2 + |t|) + 6 := by ring
  have hlog_nonneg : 0 ≤ Real.log (2 + |t|) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog_four_nonneg : 0 ≤ Real.log 4 :=
    Real.log_nonneg (by norm_num)
  have hconstant_ge_one :
      1 ≤ |Real.log Real.pi| + Real.log 4 + 7 := by
    linarith [abs_nonneg (Real.log Real.pi)]
  have habsorb :
      0 ≤
        ((|Real.log Real.pi| + Real.log 4 + 7) - 1) *
          Real.log (2 + |t|) :=
    mul_nonneg (sub_nonneg.mpr hconstant_ge_one) hlog_nonneg
  have henvelope :
      vModeLogGrowthEnvelope t = 1 + Real.log (2 + |t|) := rfl
  rw [henvelope]
  nlinarith

end Q3.RouteB.D0Pstar
