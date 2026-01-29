import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows

/-!
Scaffold for a heat-weighted Lipschitz certificate on the prime/arch margin
at t_critical, tau = 0, over B ∈ [B_min, prime_cert_B_max].

This file introduces a structure that packages numeric constants and the
corresponding Lipschitz statements. It does **not** provide the certificate.

Numeric helper: `scripts/prime_brange_heat_lipschitz_cert.py`
- outputs `output/prime_cert_brange_heat_L_*.txt`
- intended to fill the constants below.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

/-- Shorthand for the test function at t_critical, tau = 0. -/
def phi_shift_critical_tau0 (B : ℝ) : ℝ → ℝ :=
  fun ξ => phi_shift B t_critical 0 ξ

/-- Margin function at t_critical, tau = 0. -/
def margin_tau0 (B : ℝ) : ℝ :=
  arch_term (phi_shift_critical_tau0 B) -
    prime_term (phi_shift_critical_tau0 B)

/--
Package for a heat-weighted Lipschitz certificate on the B-range.
Fill this with numeric bounds once the certificate is computed.
-/
structure PrimeMarginHeatLipschitzCert where
  /-- Lipschitz constant for the arch term on the B-range. -/
  L_arch : ℝ
  /-- Lipschitz constant for the prime term on the B-range. -/
  L_prime : ℝ
  /-- Certified arch-term Lipschitz bound. -/
  h_arch :
    ∀ B1 B2,
      B1 ∈ Set.Icc B_min prime_cert_B_max →
      B2 ∈ Set.Icc B_min prime_cert_B_max →
      |arch_term (phi_shift_critical_tau0 B1) -
        arch_term (phi_shift_critical_tau0 B2)| ≤
        L_arch * |B1 - B2|
  /-- Certified prime-term Lipschitz bound. -/
  h_prime :
    ∀ B1 B2,
      B1 ∈ Set.Icc B_min prime_cert_B_max →
      B2 ∈ Set.Icc B_min prime_cert_B_max →
      |prime_term (phi_shift_critical_tau0 B1) -
        prime_term (phi_shift_critical_tau0 B2)| ≤
        L_prime * |B1 - B2|

/--
Combine certified arch/prime bounds into a margin Lipschitz bound.
This is the intended replacement for the current `prime_margin_Lipschitz_on_Brange` axiom
once a `PrimeMarginHeatLipschitzCert` is instantiated.
-/
lemma margin_Lipschitz_of_cert (c : PrimeMarginHeatLipschitzCert)
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max) :
    |margin_tau0 B1 - margin_tau0 B2| ≤ (c.L_arch + c.L_prime) * |B1 - B2| := by
  have h_arch := c.h_arch B1 B2 hB1 hB2
  have h_prime := c.h_prime B1 B2 hB1 hB2
  have h_triangle :
      |margin_tau0 B1 - margin_tau0 B2| ≤
        |arch_term (phi_shift_critical_tau0 B1) -
          arch_term (phi_shift_critical_tau0 B2)| +
        |prime_term (phi_shift_critical_tau0 B1) -
          prime_term (phi_shift_critical_tau0 B2)| := by
    -- triangle inequality on (arch - prime)
    unfold margin_tau0
    have h :
        |(arch_term (phi_shift_critical_tau0 B1) -
            prime_term (phi_shift_critical_tau0 B1)) -
          (arch_term (phi_shift_critical_tau0 B2) -
            prime_term (phi_shift_critical_tau0 B2))|
          ≤
          |arch_term (phi_shift_critical_tau0 B1) -
              arch_term (phi_shift_critical_tau0 B2)| +
          |prime_term (phi_shift_critical_tau0 B1) -
              prime_term (phi_shift_critical_tau0 B2)| := by
      have h1 :
          |(arch_term (phi_shift_critical_tau0 B1) -
              arch_term (phi_shift_critical_tau0 B2)) +
            (-(prime_term (phi_shift_critical_tau0 B1) -
                prime_term (phi_shift_critical_tau0 B2)))|
            ≤
            |arch_term (phi_shift_critical_tau0 B1) -
                arch_term (phi_shift_critical_tau0 B2)| +
            |prime_term (phi_shift_critical_tau0 B1) -
                prime_term (phi_shift_critical_tau0 B2)| := by
        simpa [Real.norm_eq_abs, abs_neg, abs_sub_comm, add_comm, add_left_comm, add_assoc] using
          (norm_add_le
            (arch_term (phi_shift_critical_tau0 B1) -
              arch_term (phi_shift_critical_tau0 B2))
            (-(prime_term (phi_shift_critical_tau0 B1) -
                prime_term (phi_shift_critical_tau0 B2))))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hsum :
      |arch_term (phi_shift_critical_tau0 B1) -
          arch_term (phi_shift_critical_tau0 B2)| +
        |prime_term (phi_shift_critical_tau0 B1) -
          prime_term (phi_shift_critical_tau0 B2)| ≤
      (c.L_arch + c.L_prime) * |B1 - B2| := by
    nlinarith [h_arch, h_prime]
  exact le_trans h_triangle hsum

end Q3.Proofs.PrimeCert
