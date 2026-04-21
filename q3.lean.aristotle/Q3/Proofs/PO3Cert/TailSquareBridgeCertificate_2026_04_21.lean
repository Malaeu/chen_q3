import Q3.Proofs.PO3Cert.WindowLawCertificate_2026_04_19

/-!
Real `PO3` certificate bridge from the new outer-transport window-law layer to
square-tail zero.

This file adds no new shell mathematics. Its role is to freeze the exact
Q3-side data package that the already-closed `PO3-tail.*`, `PO3-cauchy.1`, and
`PO3-cauchy.2` consumers need:

- an honest outer-transport window-law certificate;
- the unit-norm tail profile condition;
- decay of the value sequence;
- the nonvanishing sampling rescaling;
- the square repackaging.

Once that data is available, the shell already forces square-tail zero.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge

section

variable {𝕜 U₁ U₂ V₁ V₂ : Type*}
variable [NormedField 𝕜]
variable [AddCommGroup U₁] [Module 𝕜 U₁]
variable [AddCommGroup U₂] [Module 𝕜 U₂]
variable [AddCommGroup V₁] [Module 𝕜 V₁]
variable [AddCommGroup V₂] [Module 𝕜 V₂]

/-- Exact `PO3-tail.1-real` / `PO3-cauchy.*` certificate packet:
starting from the already-closed outer-transport window-law certificate, add
precisely the analytic tail data needed to reach square-tail zero. -/
structure PO3OuterTransportSquareTailCertificate where
  windowCert :
    PO3OuterTransportWindowCertificate
      (𝕜 := 𝕜) (ι := ℕ) (U₁ := U₁) (U₂ := U₂) (V₁ := V₁) (V₂ := V₂)
  N : ℕ
  profile_unit : ∀ r, N < r → ‖windowCert.profile r‖ = 1
  decay : ∀ ε > 0, ∃ R, ∀ r, R ≤ r → ‖windowCert.values r‖ < ε
  scale : ℕ → 𝕜
  samples : ℕ → 𝕜
  squareReceiver : ℕ → 𝕜
  rescaling : ∀ r, N < r → windowCert.values r = scale r * samples r
  scale_nonzero : ∀ r, N < r → scale r ≠ 0
  repackaging : ∀ r, samples r = squareReceiver (r ^ 2)

/-- Tail-law feeder extracted from the new real square-tail certificate:
the outer-transport window-law certificate already gives one global scalar
profile law, and hence in particular one strict-tail scalar law. -/
theorem po3_tail_scalar_law_of_outer_transport_square_tail_certificate
    (cert : PO3OuterTransportSquareTailCertificate
      (𝕜 := 𝕜) (U₁ := U₁) (U₂ := U₂) (V₁ := V₁) (V₂ := V₂)) :
    ∃ c : 𝕜, ∀ r, cert.N < r → cert.windowCert.values r = c * cert.windowCert.profile r := by
  rcases po3_window_scalar_law_of_outer_transport_certificate cert.windowCert with ⟨c, hc⟩
  exact ⟨c, fun r _ => hc r⟩

/-- Direct real certificate consumer:
outer-transport window law, decay, nonvanishing sampling rescaling, and square
repackaging already imply square-tail zero for the packaged receiver. -/
theorem po3_square_tail_zero_of_outer_transport_square_tail_certificate
    (cert : PO3OuterTransportSquareTailCertificate
      (𝕜 := 𝕜) (U₁ := U₁) (U₂ := U₂) (V₁ := V₁) (V₂ := V₂)) :
    ∀ r, cert.N < r → cert.squareReceiver (r ^ 2) = 0 := by
  rcases po3_tail_scalar_law_of_outer_transport_square_tail_certificate cert with ⟨c, hc⟩
  have hzeroValues :
      ∀ r, cert.N < r → cert.windowCert.values r = 0 :=
    po3_tail_zero_of_tail_scalar_law_of_decay hc cert.profile_unit cert.decay
  have hzeroSamples :
      ∀ r, cert.N < r → cert.samples r = 0 :=
    po3_tail_zero_of_nonvanishing_rescaling cert.rescaling cert.scale_nonzero hzeroValues
  exact po3_square_tail_zero_of_repackaging cert.repackaging hzeroSamples

end

end Q3.Proofs.PO3Cert
