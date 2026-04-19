import Q3.Proofs.HBridge_PO3_Shell

/-!
Certificate feeder for the closed `PO3-rig.1b` shell.

This file does not define the real Q3 objects `v_{a,N}` or `w_{r,0}(a)`.
Its role is narrower: it freezes the exact input contract that a future
Q3-side coefficient certificate must satisfy in order to trigger the already
formalized window-law shell.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge

section

variable {𝕜 ι V W : Type*}
variable [Field 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

/-- Target conclusion expected from a compressed zero-mode coordinate
certificate: the shared coordinate sequence is one scalar multiple of the fixed
window profile. -/
def po3_window_scalar_law (values profile : ι → 𝕜) : Prop :=
  ∃ c : 𝕜, ∀ i, values i = c * profile i

/-- Exact feeder contract for the still-missing Q3-side certificate behind
`PO3-rig.1b`.

The intended future specialization is:

- `plusPiece`, `minusPiece` are the compressed plus/minus parts of `v_{a,N}`;
- `values` is the common coordinate sequence `r ↦ w_{r,0}(a)` on the window;
- `profile` is the alternating endpoint profile `r ↦ (-1)^r` up to the fixed
  normalization factor. -/
structure PO3WindowCoordinateCertificate where
  coordsPlus : ι → V →ₗ[𝕜] 𝕜
  coordsMinus : ι → W →ₗ[𝕜] 𝕜
  plusPiece : V
  plusEndpoint : V
  minusPiece : W
  minusEndpoint : W
  values : ι → 𝕜
  profile : ι → 𝕜
  plus_mem : plusPiece ∈ 𝕜 ∙ plusEndpoint
  minus_mem : minusPiece ∈ 𝕜 ∙ minusEndpoint
  plus_endpoint_profile : ∀ i, coordsPlus i plusEndpoint = profile i
  minus_endpoint_profile : ∀ i, coordsMinus i minusEndpoint = profile i
  plus_values : ∀ i, coordsPlus i plusPiece = values i
  minus_values : ∀ i, coordsMinus i minusPiece = values i
  profile_nonzero : ∃ i, profile i ≠ 0

/-- Once the future Q3-side feeder certifies the compressed coordinate data,
the already-closed `PO3-rig.1b` shell immediately returns the one-scalar window
law needed by `PO3-tail.1`. -/
theorem po3_window_scalar_law_of_certificate
    (cert : PO3WindowCoordinateCertificate
      (𝕜 := 𝕜) (ι := ι) (V := V) (W := W)) :
    po3_window_scalar_law cert.values cert.profile := by
  rcases po3_shared_coordinate_profile_of_two_mem_span_singleton
      cert.coordsPlus
      cert.coordsMinus
      cert.plus_mem
      cert.minus_mem
      cert.plus_endpoint_profile
      cert.minus_endpoint_profile
      cert.plus_values
      cert.minus_values
      cert.profile_nonzero with ⟨c, hc⟩
  exact ⟨c, hc⟩

end

end Q3.Proofs.PO3Cert
