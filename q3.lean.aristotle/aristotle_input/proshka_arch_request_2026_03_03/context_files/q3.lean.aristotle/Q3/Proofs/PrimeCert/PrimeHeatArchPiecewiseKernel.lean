import Mathlib
import Q3.Proofs.PrimeCert.ArchHeatMajorant

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Piecewise constant majorant template for arch heat bounds. -/
def arch_core_tail_majorant (r Mcore Mtail ξ : ℝ) : ℝ :=
  if |ξ| ≤ r then Mcore else Mtail

lemma prime_heat_bounds_arch_of_core_tail_majorant
    (r Mcore Mtail : ℝ)
    (h_int_f :
      MeasureTheory.IntegrableOn
        (fun ξ => |a_star ξ| * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_int_g :
      MeasureTheory.IntegrableOn
        (fun ξ => arch_core_tail_majorant r Mcore Mtail ξ * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_majorant :
      ∀ ξ, |a_star ξ| ≤ arch_core_tail_majorant r Mcore Mtail ξ)
    (h_integral_bound :
      (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
          arch_core_tail_majorant r Mcore Mtail ξ * arch_heat_kernel_tc ξ)
        ≤
        prime_cert_L_arch_heat_raw) :
    (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |a_star ξ| * arch_heat_kernel_tc ξ)
      ≤
      prime_cert_L_arch_heat_raw := by
  exact
    prime_heat_bounds_arch_of_majorant
      (g := arch_core_tail_majorant r Mcore Mtail)
      h_int_f h_int_g h_majorant h_integral_bound

end Q3.Proofs.PrimeCert
