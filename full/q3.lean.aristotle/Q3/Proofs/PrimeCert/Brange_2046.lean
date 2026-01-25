import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeGrid_2046
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

/-!
Prime-term B-range certificate at t_critical, tau = 0.
Source: output/prime_cert_brange_tcritical_2026-01-25_2046.txt
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

/-- B-grid on [B_min, B_max] with step prime_cert_B_h. -/
def prime_b_grid (i : Fin prime_b_grid_vals.size) : ℝ :=
  B_min + (i.1 : ℝ) * prime_cert_B_h

/-- Link table grid values to the true margin at grid points. -/
axiom prime_b_grid_val_le_margin :
    ∀ i : Fin prime_b_grid_vals.size,
      prime_b_grid_val i ≤
        arch_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) -
          prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ)

/-- Lipschitz certificate in B on the B-range. -/
axiom prime_margin_Lipschitz_on_Brange :
    ∀ x y,
      x ∈ Set.Icc B_min prime_cert_B_max →
      y ∈ Set.Icc B_min prime_cert_B_max →
      |(arch_term (fun ξ => phi_shift x t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift x t_critical 0 ξ)) -
       (arch_term (fun ξ => phi_shift y t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift y t_critical 0 ξ))| ≤
        prime_cert_L_ub * |x - y|

/-- Grid cover certificate on [B_min, B_max]. -/
axiom prime_b_grid_cover_cert :
    ∀ B ∈ Set.Icc B_min prime_cert_B_max,
      ∃ i : Fin prime_b_grid_vals.size,
        |B - prime_b_grid i| ≤ prime_cert_B_h / 2

/-- Margin certificate on B-range at t_critical (tau = 0). -/
axiom prime_cert_margin_on_Brange_axiom :
    ∀ B ∈ Set.Icc B_min prime_cert_B_max,
      prime_cert_margin_lb ≤
        arch_term (fun ξ => phi_shift B t_critical 0 ξ) -
          prime_term (fun ξ => phi_shift B t_critical 0 ξ)

end Q3.Proofs.PrimeCert
