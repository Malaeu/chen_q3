import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28
import Q3.Proofs.PrimeCert.Brange_Lipschitz_Analytic
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatScaffold

/-!
Target: heat-weighted Lipschitz proof on the B-range for t_critical, tau = 0.
This file is intended to close `prime_margin_Lipschitz_on_Brange` using the
heat-weighted numeric certificate from `BrangeHeatCert_2026_01_28.lean`.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

/-! ### Heat-weighted bounds (assumed inputs)

These are the two numeric inequalities produced by the script:
- arch integral bound
- prime sum bound

They should eventually be certified, but for now they are hypotheses in the
lemmas below so Aristotle can focus on the analytic reduction.
-/

def heat_weight (xi : ℝ) : ℝ :=
  Real.exp (-4 * Real.pi ^ 2 * t_critical * xi ^ 2) * |xi|

lemma arch_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight ξ ≤ prime_cert_L_arch_heat_raw) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  -- TODO: use phi_shift_lipschitz_B_exp + |∫ f| ≤ ∫ |f| + bound integrand
  sorry

lemma prime_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight (xi_n n) ≤ prime_cert_L_prime_heat_raw) :
    |prime_term (phi_shift_critical_tau0 B1) -
      prime_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  -- TODO: use phi_shift_lipschitz_B_exp + triangle inequality for tsum
  sorry

lemma margin_Lipschitz_heat_of_bounds
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight ξ ≤ prime_cert_L_arch_heat_raw)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight (xi_n n) ≤ prime_cert_L_prime_heat_raw)
    (h_total :
      (prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2) ≤
        prime_cert_L_total_heat_ub) :
    |margin_tau0 B1 - margin_tau0 B2| ≤
      prime_cert_L_total_heat_ub * |B1 - B2| := by
  -- TODO: combine the two Lipschitz bounds and apply h_total.
  sorry

end Q3.Proofs.PrimeCert
