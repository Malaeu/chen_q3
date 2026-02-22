import Q3.Axioms
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.PrimeCert.Defs

noncomputable section

namespace Q3.Proofs.PrimeCert

/-- Shared contract used by all Prime certificate pathways:
    pointwise lower bound on `arch_term - prime_term` on the `B`-range at `t_critical`.
-/
def PrimeCertMarginOnBrange : Prop :=
  ∀ B ∈ Set.Icc B_min prime_cert_B_max,
    prime_cert_margin_lb ≤
      arch_term (fun ξ => phi_shift B t_critical 0 ξ) -
        prime_term (fun ξ => phi_shift B t_critical 0 ξ)

end Q3.Proofs.PrimeCert

namespace Q3

/-- Compatibility alias kept for existing theorem signatures. -/
abbrev PrimeCertMarginOnBrange : Prop := Q3.Proofs.PrimeCert.PrimeCertMarginOnBrange

end Q3

