import Q3.Proofs.HBridge_PO3_Shell
import Mathlib.Analysis.Real.Pi.Irrational

/-!
Concrete theorem-level singleton witness for the first decimal-28 zeta packet.

Unlike the off-chain `prefix2/prefix3` certificate layer, this file contains a
fully formal local obstruction: the first decimal witness `γ₀` is rational,
hence cannot lie on the affine `π`-lattice, so the singleton `(+, -)` packet
already has a nonzero anti-diagonal gap.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge

/-- Any nonzero rational witness cannot equal an integer multiple of `π`.
This is the common structural mechanism behind the concrete decimal-28
singleton obstructions below. -/
lemma po3_rational_complex_ne_int_mul_pi {q : ℚ} (hq0 : q ≠ 0) (m : ℤ) :
    (q : ℂ) ≠ (m : ℂ) * (Real.pi : ℂ) := by
  intro h
  have hre : (q : ℝ) = (m : ℝ) * Real.pi := by
    simpa using congrArg Complex.re h
  by_cases hm : m = 0
  · subst hm
    have hqre : (q : ℝ) = 0 := by
      simpa using hre
    exact hq0 (by exact_mod_cast hqre)
  · have him : Irrational ((m : ℝ) * Real.pi) := by
      simpa [mul_comm] using irrational_pi.intCast_mul hm
    exact (him.ne_rat q) hre.symm

/-- Any nonzero rational witness has nonvanishing complex sine. -/
lemma po3_rational_complex_sin_ne_zero {q : ℚ} (hq0 : q ≠ 0) :
    Complex.sin (q : ℂ) ≠ 0 := by
  intro h
  rcases (Complex.sin_eq_zero_iff.mp h) with ⟨m, hm⟩
  exact po3_rational_complex_ne_int_mul_pi hq0 m hm

/-- If a complex witness avoids all integer multiples of `π`, then its complex
sine is nonzero. This keeps the concrete singleton lemmas lightweight because
they can reuse the already-proved lattice exclusion directly. -/
lemma po3_complex_sin_ne_zero_of_ne_int_mul_pi {z : ℂ}
    (hz : ∀ m : ℤ, z ≠ (m : ℂ) * (Real.pi : ℂ)) :
    Complex.sin z ≠ 0 := by
  intro h
  rcases (Complex.sin_eq_zero_iff.mp h) with ⟨m, hm⟩
  exact hz m hm

/-- Rational form of the first decimal-28 zeta witness. -/
lemma po3_first_zeta_gamma0_decimal28_eq_rat :
    po3_first_zeta_gamma0_decimal28 =
      (((141347251417346937904572519836 : ℚ) / (10 : ℚ) ^ 28 : ℚ) : ℂ) := by
  norm_num [po3_first_zeta_gamma0_decimal28, po3_decimal28]

/-- Rational form of the second decimal-28 zeta witness. -/
lemma po3_first_zeta_gamma1_decimal28_eq_rat :
    po3_first_zeta_gamma1_decimal28 =
      (((210220396387715549926284795939 : ℚ) / (10 : ℚ) ^ 28 : ℚ) : ℂ) := by
  norm_num [po3_first_zeta_gamma1_decimal28, po3_decimal28]

/-- Rational form of the third decimal-28 zeta witness. -/
lemma po3_first_zeta_gamma2_decimal28_eq_rat :
    po3_first_zeta_gamma2_decimal28 =
      (((250108575801456887632137909926 : ℚ) / (10 : ℚ) ^ 28 : ℚ) : ℂ) := by
  norm_num [po3_first_zeta_gamma2_decimal28, po3_decimal28]

/-- The first decimal-28 witness value cannot equal an integer multiple of `π`.
The reason is structural, not numerical: the witness is rational while every
nonzero integer multiple of `π` is irrational. -/
lemma po3_first_zeta_gamma0_decimal28_ne_int_mul_pi (m : ℤ) :
    po3_first_zeta_gamma0_decimal28 ≠ (m : ℂ) * (Real.pi : ℂ) := by
  rw [po3_first_zeta_gamma0_decimal28_eq_rat]
  exact po3_rational_complex_ne_int_mul_pi (by norm_num) m

/-- The second decimal-28 witness value cannot equal an integer multiple of
`π` for the same structural reason. -/
lemma po3_first_zeta_gamma1_decimal28_ne_int_mul_pi (m : ℤ) :
    po3_first_zeta_gamma1_decimal28 ≠ (m : ℂ) * (Real.pi : ℂ) := by
  rw [po3_first_zeta_gamma1_decimal28_eq_rat]
  exact po3_rational_complex_ne_int_mul_pi (by norm_num) m

/-- The third decimal-28 witness value cannot equal an integer multiple of
`π` for the same structural reason. -/
lemma po3_first_zeta_gamma2_decimal28_ne_int_mul_pi (m : ℤ) :
    po3_first_zeta_gamma2_decimal28 ≠ (m : ℂ) * (Real.pi : ℂ) := by
  rw [po3_first_zeta_gamma2_decimal28_eq_rat]
  exact po3_rational_complex_ne_int_mul_pi (by norm_num) m

/-- The first decimal-28 zeta witness does not annihilate the manuscript
amplitude at `a = 1`. -/
lemma po3_first_zeta_gamma0_decimal28_sin_ne_zero :
    Complex.sin ((1 : ℂ) * po3_first_zeta_gamma0_decimal28) ≠ 0 := by
  simpa [one_mul] using
    (po3_complex_sin_ne_zero_of_ne_int_mul_pi
      (z := po3_first_zeta_gamma0_decimal28)
      po3_first_zeta_gamma0_decimal28_ne_int_mul_pi)

/-- The second decimal-28 zeta witness does not annihilate the manuscript
amplitude at `a = 1`. -/
lemma po3_first_zeta_gamma1_decimal28_sin_ne_zero :
    Complex.sin ((1 : ℂ) * po3_first_zeta_gamma1_decimal28) ≠ 0 := by
  simpa [one_mul] using
    (po3_complex_sin_ne_zero_of_ne_int_mul_pi
      (z := po3_first_zeta_gamma1_decimal28)
      po3_first_zeta_gamma1_decimal28_ne_int_mul_pi)

/-- The third decimal-28 zeta witness does not annihilate the manuscript
amplitude at `a = 1`. -/
lemma po3_first_zeta_gamma2_decimal28_sin_ne_zero :
    Complex.sin ((1 : ℂ) * po3_first_zeta_gamma2_decimal28) ≠ 0 := by
  simpa [one_mul] using
    (po3_complex_sin_ne_zero_of_ne_int_mul_pi
      (z := po3_first_zeta_gamma2_decimal28)
      po3_first_zeta_gamma2_decimal28_ne_int_mul_pi)

/-- Honest singleton obstruction for the first decimal-28 zeta witness at
`a = 1`: the raw manuscript singleton cannot come from a one-variable
`(+,-)` profile. -/
theorem po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma0_decimal28 :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_singleton
          (1 : ℂ)
          po3_first_zeta_gamma0_decimal28
        = po3_suzuki_filtered_pm_candidate u := by
  refine po3_no_suzuki_raw_gamma_pm_singleton_candidate_of_gap_20_11
    (1 : ℂ) po3_first_zeta_gamma0_decimal28 (by norm_num)
    po3_first_zeta_gamma0_decimal28_sin_ne_zero ?_ ?_ ?_ ?_
  · have h0 := po3_first_zeta_gamma0_decimal28_ne_int_mul_pi 0
    simpa using h0
  · have h1 := po3_first_zeta_gamma0_decimal28_ne_int_mul_pi 1
    norm_num [po3_suzuki_manuscript_alpha_step] at h1 ⊢
    exact h1
  · have h2 := po3_first_zeta_gamma0_decimal28_ne_int_mul_pi 2
    norm_num [po3_suzuki_manuscript_alpha_step] at h2 ⊢
    exact h2
  · have h3 := po3_first_zeta_gamma0_decimal28_ne_int_mul_pi 3
    norm_num [po3_suzuki_manuscript_alpha_step] at h3 ⊢
    exact h3

/-- Honest singleton obstruction for the second decimal-28 zeta witness at
`a = 1`. -/
theorem po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma1_decimal28 :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_singleton
          (1 : ℂ)
          po3_first_zeta_gamma1_decimal28
        = po3_suzuki_filtered_pm_candidate u := by
  refine po3_no_suzuki_raw_gamma_pm_singleton_candidate_of_gap_20_11
    (1 : ℂ) po3_first_zeta_gamma1_decimal28 (by norm_num)
    po3_first_zeta_gamma1_decimal28_sin_ne_zero ?_ ?_ ?_ ?_
  · have h0 := po3_first_zeta_gamma1_decimal28_ne_int_mul_pi 0
    simpa using h0
  · have h1 := po3_first_zeta_gamma1_decimal28_ne_int_mul_pi 1
    norm_num [po3_suzuki_manuscript_alpha_step] at h1 ⊢
    exact h1
  · have h2 := po3_first_zeta_gamma1_decimal28_ne_int_mul_pi 2
    norm_num [po3_suzuki_manuscript_alpha_step] at h2 ⊢
    exact h2
  · have h3 := po3_first_zeta_gamma1_decimal28_ne_int_mul_pi 3
    norm_num [po3_suzuki_manuscript_alpha_step] at h3 ⊢
    exact h3

/-- Honest singleton obstruction for the third decimal-28 zeta witness at
`a = 1`. -/
theorem po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma2_decimal28 :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_singleton
          (1 : ℂ)
          po3_first_zeta_gamma2_decimal28
        = po3_suzuki_filtered_pm_candidate u := by
  refine po3_no_suzuki_raw_gamma_pm_singleton_candidate_of_gap_20_11
    (1 : ℂ) po3_first_zeta_gamma2_decimal28 (by norm_num)
    po3_first_zeta_gamma2_decimal28_sin_ne_zero ?_ ?_ ?_ ?_
  · have h0 := po3_first_zeta_gamma2_decimal28_ne_int_mul_pi 0
    simpa using h0
  · have h1 := po3_first_zeta_gamma2_decimal28_ne_int_mul_pi 1
    norm_num [po3_suzuki_manuscript_alpha_step] at h1 ⊢
    exact h1
  · have h2 := po3_first_zeta_gamma2_decimal28_ne_int_mul_pi 2
    norm_num [po3_suzuki_manuscript_alpha_step] at h2 ⊢
    exact h2
  · have h3 := po3_first_zeta_gamma2_decimal28_ne_int_mul_pi 3
    norm_num [po3_suzuki_manuscript_alpha_step] at h3 ⊢
    exact h3

end Q3.Proofs.PO3Cert
