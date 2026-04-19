import Q3.Proofs.PO3Cert.FirstZetaPrefix2_2026_04_19

/-!
Honest theorem-level `prefix3` closure for the first decimal-28 zeta packet at
`a = 1`.

This is the direct three-mode extension of the already formalized `prefix2`
package: the third manuscript gap weight attached to `γ₂` is again a positive
real number, so the full three-term witness sum is nonzero.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge
open scoped Real

/-- Real form of the third decimal-28 zeta witness. -/
noncomputable def po3_first_zeta_gamma2_decimal28_real : ℝ :=
  (((250108575801456887632137909926 : ℚ) / (10 : ℚ) ^ 28 : ℚ) : ℝ)

lemma po3_first_zeta_gamma2_decimal28_eq_ofReal :
    po3_first_zeta_gamma2_decimal28 = (po3_first_zeta_gamma2_decimal28_real : ℂ) := by
  rw [po3_first_zeta_gamma2_decimal28_eq_rat, po3_first_zeta_gamma2_decimal28_real]
  rfl

lemma po3_first_zeta_gamma2_decimal28_real_gt_three_pi :
    3 * Real.pi < po3_first_zeta_gamma2_decimal28_real := by
  have hpi : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  unfold po3_first_zeta_gamma2_decimal28_real
  norm_num at hpi ⊢
  nlinarith

lemma po3_first_zeta_gamma2_decimal28_real_sin_ne_zero :
    Complex.sin (po3_first_zeta_gamma2_decimal28_real : ℂ) ≠ 0 := by
  simpa [one_mul, po3_first_zeta_gamma2_decimal28_eq_ofReal] using
    po3_first_zeta_gamma2_decimal28_sin_ne_zero

/-- Honest theorem-level nonvanishing of the concrete three-mode witness sum at
`a = 1`. -/
theorem po3_first_zeta_gap_sum3_a1_decimal28_ne_zero_honest :
    po3_first_zeta_gap_sum3_a1_decimal28 ≠ 0 := by
  let w0 : ℝ :=
    (2 * Real.pi ^ 2) * (Real.sin po3_first_zeta_gamma0_decimal28_real ^ 2) *
      po3_gap_term20_11_real_a1 po3_first_zeta_gamma0_decimal28_real
  let w1 : ℝ :=
    (2 * Real.pi ^ 2) * (Real.sin po3_first_zeta_gamma1_decimal28_real ^ 2) *
      po3_gap_term20_11_real_a1 po3_first_zeta_gamma1_decimal28_real
  let w2 : ℝ :=
    (2 * Real.pi ^ 2) * (Real.sin po3_first_zeta_gamma2_decimal28_real ^ 2) *
      po3_gap_term20_11_real_a1 po3_first_zeta_gamma2_decimal28_real
  have hw0 : 0 < w0 := by
    dsimp [w0]
    exact po3_suzuki_manuscript_gap_weight_a1_ofReal_pos
      po3_first_zeta_gamma0_decimal28_real_gt_three_pi
      po3_first_zeta_gamma0_decimal28_real_sin_ne_zero
  have hw1 : 0 < w1 := by
    dsimp [w1]
    exact po3_suzuki_manuscript_gap_weight_a1_ofReal_pos
      po3_first_zeta_gamma1_decimal28_real_gt_three_pi
      po3_first_zeta_gamma1_decimal28_real_sin_ne_zero
  have hw2 : 0 < w2 := by
    dsimp [w2]
    exact po3_suzuki_manuscript_gap_weight_a1_ofReal_pos
      po3_first_zeta_gamma2_decimal28_real_gt_three_pi
      po3_first_zeta_gamma2_decimal28_real_sin_ne_zero
  have hsum : 0 < w0 + w1 + w2 := by
    nlinarith
  rw [po3_first_zeta_gap_sum3_a1_decimal28, po3_suzuki_manuscript_gap_sum3,
    po3_first_zeta_gamma0_decimal28_eq_ofReal, po3_first_zeta_gamma1_decimal28_eq_ofReal,
    po3_first_zeta_gamma2_decimal28_eq_ofReal, po3_suzuki_manuscript_gap_weight_a1_ofReal,
    po3_suzuki_manuscript_gap_weight_a1_ofReal, po3_suzuki_manuscript_gap_weight_a1_ofReal]
  simpa [w0, w1, w2, add_assoc] using
    (show (((w0 + w1 + w2 : ℝ) : ℂ) ≠ 0) from by
      exact_mod_cast hsum.ne')

/-- Honest theorem-level `prefix3` closure at `a = 1` for the first three
decimal-28 zeta witnesses. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_sum3_honest :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix3
          (1 : ℂ)
          po3_first_zeta_gamma0_decimal28
          po3_first_zeta_gamma1_decimal28
          po3_first_zeta_gamma2_decimal28
        = po3_suzuki_filtered_pm_candidate u := by
  exact po3_no_suzuki_raw_gamma_pm_prefix3_of_first_zeta_decimal28_witness
    po3_first_zeta_gap_sum3_a1_decimal28_ne_zero_honest

end Q3.Proofs.PO3Cert
