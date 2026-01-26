import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeGrid_2046
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

def prime_cert_brange_source : String :=
  "output/prime_cert_brange_tcritical_2026-01-26_0050.txt"

def prime_cert_brange_sha256 : String :=
  "a9d5303b2da81886cf64bfc5ee9b5b1ab85ce0b45067a8cd9b499d051a294230"

axiom prime_b_grid_val_le_margin :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_val i ≤
        arch_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) -
          prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ)

axiom prime_margin_Lipschitz_on_Brange :
    ∀ x y,
      x ∈ Set.Icc B_min prime_cert_B_max →
      y ∈ Set.Icc B_min prime_cert_B_max →
      |(arch_term (fun ξ => phi_shift x t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift x t_critical 0 ξ)) -
       (arch_term (fun ξ => phi_shift y t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift y t_critical 0 ξ))| ≤
        prime_cert_L_ub * |x - y|

end Q3.Proofs.PrimeCert
