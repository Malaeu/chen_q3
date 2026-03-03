import Q3.Main
import Q3.Proofs.PrimeCert.Brange_2046

noncomputable section

namespace Q3.Main

open Q3.Proofs.PrimeCert

/-- Canonical PrimeCert margin witness from the current certificate route. -/
theorem prime_cert_margin_on_Brange_from_PrimeCert :
    Q3.PrimeCertMarginOnBrange := by
  intro B hB
  simpa [Q3.phi_shift_critical] using
    (Q3.Proofs.PrimeCert.prime_cert_margin_on_Brange_axiom B hB)

/-- RH route via the current PrimeCert B-range margin witness.
This profile is intentionally data-driven and kept separate from
the canonical mainline theorem chain. -/
theorem RH_of_Weil_and_Q3_via_margin_cert : Q3.RH := by
  exact RH_of_Weil_and_Q3_of_margin prime_cert_margin_on_Brange_from_PrimeCert

end Q3.Main

end
