import Q3.Proofs.PO3Cert.FirstZetaSingleton_2026_04_19
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Honest theorem-level `prefix2` closure for the first decimal-28 zeta packet at
`a = 1`.

The proof is still local and shell-facing, but it no longer uses the off-chain
certificate axiom from `FirstZetaGapWitness_2026_04_19_Data.lean`: both
manuscript gap weights are shown to be positive real numbers, so their sum is
nonzero.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge
open scoped Real

/-- Real-valued `(2,0) - (1,1)` six-pole gap term at `a = 1`, i.e. on the
literal affine step `π`. -/
noncomputable def po3_gap_term20_11_real_a1 (x : ℝ) : ℝ :=
  1 / (((x - 2 * Real.pi) * (x - 3 * Real.pi)) * (x * (x - Real.pi))) -
    1 / (((x - Real.pi) * (x - 2 * Real.pi)) * ((x - Real.pi) * (x - 2 * Real.pi)))

/-- Once `x` lies to the right of the first four affine poles `0, π, 2π, 3π`,
the real six-pole gap term is strictly positive. -/
lemma po3_gap_term20_11_real_a1_pos {x : ℝ} (hx : 3 * Real.pi < x) :
    0 < po3_gap_term20_11_real_a1 x := by
  have hx0 : 0 < x := by
    nlinarith [Real.pi_pos, hx]
  have hx1 : 0 < x - Real.pi := by
    nlinarith [Real.pi_pos, hx]
  have hx2 : 0 < x - 2 * Real.pi := by
    nlinarith [Real.pi_pos, hx]
  have hx3 : 0 < x - 3 * Real.pi := by
    nlinarith
  let A : ℝ := (((x - 2 * Real.pi) * (x - 3 * Real.pi)) * (x * (x - Real.pi)))
  let B : ℝ := (((x - Real.pi) * (x - 2 * Real.pi)) * ((x - Real.pi) * (x - 2 * Real.pi)))
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hBA : B - A = 2 * Real.pi ^ 2 * (x - Real.pi) * (x - 2 * Real.pi) := by
    dsimp [A, B]
    ring
  have hBgtA : 0 < B - A := by
    rw [hBA]
    positivity
  have hAltB : A < B := by
    nlinarith
  have hrecip : 1 / B < 1 / A :=
    one_div_lt_one_div_of_lt hApos hAltB
  unfold po3_gap_term20_11_real_a1
  dsimp [A, B] at hrecip
  nlinarith

/-- The complex six-pole gap term at `a = 1` and a real witness is just the
complexification of the corresponding real gap term. -/
lemma po3_suzuki_filtered_pm_gap_term_20_11_a1_ofReal (x : ℝ) :
    po3_suzuki_filtered_pm_gap_term_20_11 (Real.pi : ℂ) (x : ℂ) =
      (po3_gap_term20_11_real_a1 x : ℂ) := by
  unfold po3_gap_term20_11_real_a1
  simp [po3_suzuki_filtered_pm_gap_term_20_11]

/-- At `a = 1`, the manuscript gap weight of a real witness is itself a real
number with the expected factorization into prefactor, `sin²`, and the real
six-pole gap term. -/
lemma po3_suzuki_manuscript_gap_weight_a1_ofReal (x : ℝ) :
    po3_suzuki_manuscript_gap_weight (1 : ℂ) (x : ℂ) =
      (((2 * Real.pi ^ 2) * (Real.sin x ^ 2) * po3_gap_term20_11_real_a1 x : ℝ) : ℂ) := by
  simp [po3_suzuki_manuscript_gap_weight, po3_suzuki_manuscript_prefactor,
    po3_suzuki_manuscript_amp, po3_suzuki_manuscript_alpha_step,
    po3_suzuki_filtered_pm_gap_term_20_11_a1_ofReal, mul_assoc, mul_left_comm, mul_comm]

/-- The full manuscript gap weight at `a = 1` is strictly positive for every
real witness to the right of `3π`, as soon as the sine factor is nonzero. -/
lemma po3_suzuki_manuscript_gap_weight_a1_ofReal_pos
    {x : ℝ} (hx : 3 * Real.pi < x) (hsin : Complex.sin (x : ℂ) ≠ 0) :
    0 < (2 * Real.pi ^ 2) * (Real.sin x ^ 2) * po3_gap_term20_11_real_a1 x := by
  have hsinr : Real.sin x ≠ 0 := by
    intro hs
    apply hsin
    have hsinC : Complex.sin (x : ℂ) = (Real.sin x : ℂ) := by
      simp
    rw [hs] at hsinC
    simpa using hsinC
  have hsq : 0 < Real.sin x ^ 2 := by
    exact sq_pos_iff.mpr hsinr
  have hpi : 0 < 2 * Real.pi ^ 2 := by
    positivity
  have hgap : 0 < po3_gap_term20_11_real_a1 x :=
    po3_gap_term20_11_real_a1_pos hx
  exact mul_pos (mul_pos hpi hsq) hgap

/-- Real form of the first decimal-28 zeta witness. -/
noncomputable def po3_first_zeta_gamma0_decimal28_real : ℝ :=
  (((141347251417346937904572519836 : ℚ) / (10 : ℚ) ^ 28 : ℚ) : ℝ)

/-- Real form of the second decimal-28 zeta witness. -/
noncomputable def po3_first_zeta_gamma1_decimal28_real : ℝ :=
  (((210220396387715549926284795939 : ℚ) / (10 : ℚ) ^ 28 : ℚ) : ℝ)

lemma po3_first_zeta_gamma0_decimal28_eq_ofReal :
    po3_first_zeta_gamma0_decimal28 = (po3_first_zeta_gamma0_decimal28_real : ℂ) := by
  rw [po3_first_zeta_gamma0_decimal28_eq_rat, po3_first_zeta_gamma0_decimal28_real]
  rfl

lemma po3_first_zeta_gamma1_decimal28_eq_ofReal :
    po3_first_zeta_gamma1_decimal28 = (po3_first_zeta_gamma1_decimal28_real : ℂ) := by
  rw [po3_first_zeta_gamma1_decimal28_eq_rat, po3_first_zeta_gamma1_decimal28_real]
  rfl

lemma po3_first_zeta_gamma0_decimal28_real_gt_three_pi :
    3 * Real.pi < po3_first_zeta_gamma0_decimal28_real := by
  have hpi : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  unfold po3_first_zeta_gamma0_decimal28_real
  norm_num at hpi ⊢
  nlinarith

lemma po3_first_zeta_gamma1_decimal28_real_gt_three_pi :
    3 * Real.pi < po3_first_zeta_gamma1_decimal28_real := by
  have hpi : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  unfold po3_first_zeta_gamma1_decimal28_real
  norm_num at hpi ⊢
  nlinarith

lemma po3_first_zeta_gamma0_decimal28_real_sin_ne_zero :
    Complex.sin (po3_first_zeta_gamma0_decimal28_real : ℂ) ≠ 0 := by
  simpa [one_mul, po3_first_zeta_gamma0_decimal28_eq_ofReal] using
    po3_first_zeta_gamma0_decimal28_sin_ne_zero

lemma po3_first_zeta_gamma1_decimal28_real_sin_ne_zero :
    Complex.sin (po3_first_zeta_gamma1_decimal28_real : ℂ) ≠ 0 := by
  simpa [one_mul, po3_first_zeta_gamma1_decimal28_eq_ofReal] using
    po3_first_zeta_gamma1_decimal28_sin_ne_zero

/-- The concrete two-mode witness sum at `a = 1` is already a positive real
number, hence nonzero. This gives a theorem-level `prefix2` closure with no
external certificate axiom. -/
theorem po3_first_zeta_gap_sum2_a1_decimal28_ne_zero_honest :
    po3_first_zeta_gap_sum2_a1_decimal28 ≠ 0 := by
  let w0 : ℝ :=
    (2 * Real.pi ^ 2) * (Real.sin po3_first_zeta_gamma0_decimal28_real ^ 2) *
      po3_gap_term20_11_real_a1 po3_first_zeta_gamma0_decimal28_real
  let w1 : ℝ :=
    (2 * Real.pi ^ 2) * (Real.sin po3_first_zeta_gamma1_decimal28_real ^ 2) *
      po3_gap_term20_11_real_a1 po3_first_zeta_gamma1_decimal28_real
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
  have hsum : 0 < w0 + w1 := add_pos hw0 hw1
  rw [po3_first_zeta_gap_sum2_a1_decimal28, po3_suzuki_manuscript_gap_sum2,
    po3_first_zeta_gamma0_decimal28_eq_ofReal, po3_first_zeta_gamma1_decimal28_eq_ofReal,
    po3_suzuki_manuscript_gap_weight_a1_ofReal, po3_suzuki_manuscript_gap_weight_a1_ofReal]
  simpa [w0, w1] using (show (((w0 + w1 : ℝ) : ℂ) ≠ 0) from by
    exact_mod_cast hsum.ne')

/-- Honest theorem-level `prefix2` closure at `a = 1` for the first two
decimal-28 zeta witnesses. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix2_from_first_zeta_gap_sum2_honest :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix2
          (1 : ℂ)
          po3_first_zeta_gamma0_decimal28
          po3_first_zeta_gamma1_decimal28
        = po3_suzuki_filtered_pm_candidate u := by
  exact po3_no_suzuki_raw_gamma_pm_prefix2_of_first_zeta_decimal28_witness
    po3_first_zeta_gap_sum2_a1_decimal28_ne_zero_honest

end Q3.Proofs.PO3Cert
