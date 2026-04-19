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

/-- The first decimal-28 witness value cannot equal an integer multiple of `π`.
The reason is structural, not numerical: the witness is rational while every
nonzero integer multiple of `π` is irrational. -/
lemma po3_first_zeta_gamma0_decimal28_ne_int_mul_pi (m : ℤ) :
    po3_first_zeta_gamma0_decimal28 ≠ (m : ℂ) * (Real.pi : ℂ) := by
  intro h
  let q : ℚ := (141347251417346937904572519836 : ℚ) / (10 : ℚ) ^ 28
  have hq : (po3_first_zeta_gamma0_decimal28).re = q := by
    norm_num [po3_first_zeta_gamma0_decimal28, po3_decimal28, q]
  have hre : (po3_first_zeta_gamma0_decimal28).re = (m : ℝ) * Real.pi := by
    simpa using congrArg Complex.re h
  by_cases hm : m = 0
  · subst hm
    have hqne : q ≠ 0 := by
      norm_num [q]
    exact hqne (by simpa [hq] using hre)
  · have him : Irrational ((m : ℝ) * Real.pi) := by
      simpa [mul_comm] using irrational_pi.intCast_mul hm
    have hmq : (m : ℝ) * Real.pi ≠ q := him.ne_rat q
    exact hmq (by
      calc
        (m : ℝ) * Real.pi = (po3_first_zeta_gamma0_decimal28).re := by
          simpa using hre.symm
        _ = q := hq)

/-- The first decimal-28 zeta witness does not annihilate the manuscript
amplitude at `a = 1`. -/
lemma po3_first_zeta_gamma0_decimal28_sin_ne_zero :
    Complex.sin ((1 : ℂ) * po3_first_zeta_gamma0_decimal28) ≠ 0 := by
  simpa using (show Complex.sin po3_first_zeta_gamma0_decimal28 ≠ 0 from by
    intro h
    rcases (Complex.sin_eq_zero_iff.mp h) with ⟨m, hm⟩
    exact po3_first_zeta_gamma0_decimal28_ne_int_mul_pi m hm)

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

end Q3.Proofs.PO3Cert
