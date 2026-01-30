import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSumTail

/-!
Pilot: two grid points (B=3.0 and B=4.9) for the prime-term bound.

This file isolates the exact hypotheses needed to close the prime-term inequality
at the endpoints of the B-grid. The numeric hypotheses will be supplied by the
interval-certificate pipeline.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

abbrev pilot_i0 : Fin prime_b_grid_size := ⟨0, by decide⟩
abbrev pilot_i19 : Fin prime_b_grid_size := ⟨19, by decide⟩

/-- Hypotheses required to close the prime-term bound at grid point `i`. -/
structure PrimeBGridPilotHyp (i : Fin prime_b_grid_size) : Prop where
  hsum : Summable (prime_b_grid_weight_term i)
  h_sum : prime_b_grid_prime_sum_up_to i ≤ prime_b_grid_prime_sum i
  h_tail :
    (∑' n, prime_b_grid_weight_term i (n + (prime_cert_N + 1))) ≤
      prime_b_grid_tail_bound

lemma prime_b_grid_prime_term_le_prime_ub_of_pilot
    (i : Fin prime_b_grid_size) (h : PrimeBGridPilotHyp i) :
    prime_term (fun ξ => phi_shift (prime_b_grid i) t_critical 0 ξ) ≤
      prime_b_grid_prime_ub i := by
  exact prime_b_grid_prime_term_le_prime_ub_of_sum_tail i h.hsum h.h_sum h.h_tail

lemma prime_b_grid_prime_term_le_prime_ub_pilot_0
    (h : PrimeBGridPilotHyp pilot_i0) :
    prime_term (fun ξ => phi_shift (prime_b_grid pilot_i0) t_critical 0 ξ) ≤
      prime_b_grid_prime_ub pilot_i0 := by
  simpa using prime_b_grid_prime_term_le_prime_ub_of_pilot pilot_i0 h

lemma prime_b_grid_prime_term_le_prime_ub_pilot_19
    (h : PrimeBGridPilotHyp pilot_i19) :
    prime_term (fun ξ => phi_shift (prime_b_grid pilot_i19) t_critical 0 ξ) ≤
      prime_b_grid_prime_ub pilot_i19 := by
  simpa using prime_b_grid_prime_term_le_prime_ub_of_pilot pilot_i19 h

end Q3.Proofs.PrimeCert
