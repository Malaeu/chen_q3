import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Data

/-!
Prime-heat partial-sum scaffold (t_critical, tau = 0).

This file isolates the three numeric obligations needed to bound the
prime-heat sum via a finite partial sum plus a tail estimate.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

structure PrimeHeatSumData where
  hsum : Summable prime_heat_weight_term
  h_sum : prime_heat_prime_sum_up_to prime_cert_heat_N ≤ prime_cert_L_prime_heat_partial
  h_tail :
    ∑' n, prime_heat_weight_term (n + (prime_cert_heat_N + 1)) ≤
      prime_cert_heat_tail_bound

axiom prime_heat_sum_data : PrimeHeatSumData

lemma prime_heat_bounds_prime_data_of_data :
    ∑' n, (w_Q n * (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n|)) *
        (if |xi_n n| ≤ prime_cert_B_max then (1 : ℝ) else 0)
      ≤ prime_cert_L_prime_heat_raw := by
  exact prime_heat_bounds_prime_data_of_sum_tail
    prime_heat_sum_data.hsum
    prime_heat_sum_data.h_sum
    prime_heat_sum_data.h_tail

end Q3.Proofs.PrimeCert
