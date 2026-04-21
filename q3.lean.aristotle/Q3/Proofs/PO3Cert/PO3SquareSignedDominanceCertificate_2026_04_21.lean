import Q3.Proofs.HBridge_PO3_Shell

/-!
Certificate feeder for the current live transform-side wall `PO3-square.2d3`.

This file does not solve the real Gamma-tower mathematics.
Its role is narrower: it freezes the exact certificate shape that a future
Q3-side signed rightmost / top-cluster estimate must provide in order to
trigger the already-closed shell:

- one signed main tower;
- one dominant packet inside it;
- one controlled remainder;
- one mirror tower;
- the dominant-packet lower bound;
- the eventual relative remainder control;
- the mirror decay.

Once that data is available, the shell already returns the named
`PO3-square.2d2` contradiction target.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge

section

variable {𝕜 : Type*} [NormedField 𝕜]

/-- Exact feeder contract for the live `PO3-square.2d3` wall.

The intended future specialization is the transform-side Gamma tower:

- `mainTower` is the signed one-sided main tower on the `A_k` side;
- `dominantPacket` is the extracted top cluster / rightmost packet;
- `remainder` is the surviving lower tail;
- `mirrorTower` is the suppressed mirror-side contribution built from `B_k`. -/
structure PO3SquareDominantPacketCertificate where
  mainTower : ℕ → 𝕜
  dominantPacket : ℕ → 𝕜
  remainder : ℕ → 𝕜
  mirrorTower : ℕ → 𝕜
  split : ∀ k, mainTower k = dominantPacket k + remainder k
  dominant_lower_bound :
    po3_eventually_norm_bounded_below dominantPacket
  remainder_control :
    po3_eventually_dominates_remainder dominantPacket remainder
  mirror_decay :
    po3_norm_tends_to_zero mirrorTower

/-- Direct consumer for the new `PO3-square.2d3` certificate:
once the real Q3-side data certifies a dominant packet, the shell already
produces the exact signed-dominance target needed by `PO3-square.2d2`. -/
theorem po3_square_signed_dominance_target_of_certificate
    (cert : PO3SquareDominantPacketCertificate (𝕜 := 𝕜)) :
    po3_square_signed_dominance_target cert.mainTower cert.mirrorTower := by
  exact
    po3_square_signed_dominance_target_of_dominant_packet
      cert.split
      cert.dominant_lower_bound
      cert.remainder_control
      cert.mirror_decay

/-- Contradiction form of the same feeder:
if the transform-side wall identity still claims `main = mirror`, the
certificate already kills that wall. -/
theorem po3_square_false_of_wall_and_certificate
    (cert : PO3SquareDominantPacketCertificate (𝕜 := 𝕜))
    (hwall : ∀ k, cert.mainTower k = cert.mirrorTower k) :
    False := by
  exact
    po3_square_false_of_wall_and_signed_dominance_target
      hwall
      (po3_square_signed_dominance_target_of_certificate cert)

end

end Q3.Proofs.PO3Cert
