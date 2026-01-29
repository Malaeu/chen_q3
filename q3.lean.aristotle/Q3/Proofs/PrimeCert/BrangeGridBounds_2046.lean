import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_2046
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

lemma prime_b_grid_val_le_margin_of_bounds (i : Fin prime_b_grid_size)
    (harch :
      prime_b_grid_arch_term i ≤
        arch_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ))
    (hprime :
      prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) ≤
        prime_b_grid_prime_ub i) :
    prime_b_grid_val i ≤
      arch_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) := by
  have htable :=
    prime_b_grid_val_le_arch_sub_prime_ub i
  -- combine table arithmetic with external bounds
  nlinarith [htable, harch, hprime]

end Q3.Proofs.PrimeCert
