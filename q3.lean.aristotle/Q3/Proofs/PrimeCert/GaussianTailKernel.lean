import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Tail
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSumTail
import Q3.Proofs.PrimeCert.GaussianMajorant

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Unified analytic kernel for Gaussian-type tails used in the
tau0 Brange heat and grid routes. -/
structure GaussianTailKernel where
  heat_tail_bound :
    ∑' n, prime_heat_weight_term (n + (prime_cert_heat_N + 1)) ≤
      prime_cert_heat_tail_bound
  grid_tail_summable :
    Summable (fun n => prime_b_grid_tail_term (n + (prime_cert_N + 1)))
  grid_tail_bound :
    ∑' n, prime_b_grid_tail_term (n + (prime_cert_N + 1)) ≤
      prime_b_grid_tail_bound

/-- Canonical analytic tail witness used by certificate-free reductions. -/
def gaussianTailKernel : GaussianTailKernel :=
  { heat_tail_bound := prime_heat_tail_bound
    grid_tail_summable := prime_b_grid_tail_term_summable
    grid_tail_bound := prime_b_grid_tail_term_sum_le_bound }

theorem prime_heat_tail_bound_kernel :
    ∑' n, prime_heat_weight_term (n + (prime_cert_heat_N + 1)) ≤
      prime_cert_heat_tail_bound :=
  gaussianTailKernel.heat_tail_bound

theorem prime_b_grid_tail_summable_kernel :
    Summable (fun n => prime_b_grid_tail_term (n + (prime_cert_N + 1))) :=
  gaussianTailKernel.grid_tail_summable

theorem prime_b_grid_tail_bound_kernel :
    ∑' n, prime_b_grid_tail_term (n + (prime_cert_N + 1)) ≤
      prime_b_grid_tail_bound :=
  gaussianTailKernel.grid_tail_bound

/-- Unified majorant route for the shifted grid tail at a fixed grid point. -/
theorem prime_b_grid_weight_tail_bound_by_majorant
    (i : Fin prime_b_grid_size)
    (hsum : Summable (prime_b_grid_weight_term i)) :
    ∑' n, prime_b_grid_weight_term i (n + (prime_cert_N + 1)) ≤
      prime_b_grid_tail_bound := by
  exact shifted_tail_bound_of_pointwise_majorant
    (N0 := prime_cert_N + 1)
    (f := prime_b_grid_weight_term i)
    (g := prime_b_grid_tail_term)
    ((summable_nat_add_iff (f := prime_b_grid_weight_term i) (prime_cert_N + 1)).2 hsum)
    prime_b_grid_tail_summable_kernel
    (fun n => prime_b_grid_weight_term_shift_le_tail_term i n)
    prime_b_grid_tail_bound_kernel

end Q3.Proofs.PrimeCert
