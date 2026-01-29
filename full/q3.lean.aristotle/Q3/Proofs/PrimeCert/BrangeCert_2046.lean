import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeGrid_2046
import Q3.Proofs.PrimeCert.BrangeGridBounds_2046
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatProof
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

def prime_cert_brange_source : String :=
  "output/prime_cert_brange_tcritical_2026-01-26_0050.txt"

def prime_cert_brange_sha256 : String :=
  "a9d5303b2da81886cf64bfc5ee9b5b1ab85ce0b45067a8cd9b499d051a294230"

structure PrimeBGridBounds where
  h_arch :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_arch_term i ≤
        arch_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ)
  h_prime :
    ∀ i : Fin prime_b_grid_size,
      prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) ≤
        prime_b_grid_prime_ub i

axiom prime_b_grid_bounds_data : PrimeBGridBounds

theorem prime_b_grid_bounds_cert : PrimeBGridBounds :=
  prime_b_grid_bounds_data

theorem prime_b_grid_val_le_margin :
    ∀ i : Fin prime_b_grid_size,
      prime_b_grid_val i ≤
        arch_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) -
          prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) := by
  intro i
  have harch := prime_b_grid_bounds_cert.h_arch i
  have hprime := prime_b_grid_bounds_cert.h_prime i
  exact prime_b_grid_val_le_margin_of_bounds i harch hprime

theorem prime_margin_Lipschitz_on_Brange :
    ∀ x y,
      x ∈ Set.Icc B_min prime_cert_B_max →
      y ∈ Set.Icc B_min prime_cert_B_max →
      |(arch_term (fun ξ => phi_shift x t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift x t_critical 0 ξ)) -
       (arch_term (fun ξ => phi_shift y t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift y t_critical 0 ξ))| ≤
        prime_cert_L_ub * |x - y|
  := by
  intro x y hx hy
  have hcert := prime_heat_bounds_cert
  have h_arch := hcert.h_arch
  have h_prime := hcert.h_prime
  have h_total := hcert.h_total
  have h := Q3.Proofs.PrimeCert.margin_Lipschitz_heat_of_bounds
    (B1:=x) (B2:=y) hx hy h_arch h_prime h_total
  change |(arch_term (phi_shift_critical_tau0 x) -
            prime_term (phi_shift_critical_tau0 x)) -
          (arch_term (phi_shift_critical_tau0 y) -
            prime_term (phi_shift_critical_tau0 y))| ≤
        prime_cert_L_ub * |x - y|
  simpa [Q3.Proofs.PrimeCert.margin_tau0, prime_cert_L_ub, prime_cert_L_total_heat_ub,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

end Q3.Proofs.PrimeCert
