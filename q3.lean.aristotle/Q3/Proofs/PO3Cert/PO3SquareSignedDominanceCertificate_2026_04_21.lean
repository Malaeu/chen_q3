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
open scoped BigOperators

noncomputable section

/-! ## Transform-side landing surface -/

/-- Canonical Gamma-profile ancestor pinned by the current `PO3-square.2d3`
notes:

- the old `PO2` note records the exact profile
  `u_k(x) = (-1)^k Γ(N+1-x) / Γ(k+N+1-x)`;
- the live `PO3` route packages the real wall as a signed main `A_k` tower
  against a suppressed mirror `B_k` tower.

This definition does not solve the analytic wall. It only gives the future
transform-side packet estimate one fixed Lean name for the shared Gamma-profile
building block. -/
def po3_gamma_profile (N : ℕ) (x : ℂ) (k : ℕ) : ℂ :=
  ((-1 : ℂ) ^ k) * Complex.Gamma ((N + 1 : ℂ) - x) /
    Complex.Gamma ((k + N + 1 : ℂ) - x)

theorem po3_gamma_profile_zero (N : ℕ) (x : ℂ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) :
    po3_gamma_profile N x 0 = 1 := by
  have hΓ : Complex.Gamma ((N + 1 : ℂ) - x) ≠ 0 := Complex.Gamma_ne_zero hbase
  simp [po3_gamma_profile, hΓ]

/-- Exact one-step recurrence for the transform-side Gamma profile.

This is the clean algebraic bridge from the Gamma-quotient presentation to the
packet/product presentation used in the old `PO2` direct-receiver notes. -/
theorem po3_gamma_profile_succ (N : ℕ) (x : ℂ) (k : ℕ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) :
    po3_gamma_profile N x (k + 1) =
      (x - (N + k + 1 : ℕ) : ℂ)⁻¹ * po3_gamma_profile N x k := by
  let z : ℂ := (N + k + 1 : ℂ) - x
  have hshift : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    apply hbase (m + k)
    have hm' : z - (k : ℂ) = (-m : ℂ) - k := by
      simpa using congrArg (fun t : ℂ => t - k) hm
    dsimp [z] at hm' ⊢
    ring_nf at hm' ⊢
    norm_num at hm' ⊢
    exact hm'
  have hz0 : z ≠ 0 := by
    intro hz
    exact hshift 0 (by simpa using hz)
  have hGamma :
      (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹ :=
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z
  have hstep : (Complex.Gamma (z + 1))⁻¹ = z⁻¹ * (Complex.Gamma z)⁻¹ := by
    have htmp := congrArg (fun t : ℂ => z⁻¹ * t) hGamma
    simp [hz0] at htmp
    exact htmp.symm
  have hzneg : z⁻¹ = -((x - (N + k + 1 : ℕ) : ℂ)⁻¹) := by
    have hzrepr : z = -(x - (N + k + 1 : ℕ) : ℂ) := by
      dsimp [z]
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hzrepr, inv_neg]
  unfold po3_gamma_profile
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hden1 : Complex.Gamma (((k + 1 : ℕ) : ℂ) + ↑N + 1 - x) = Complex.Gamma (z + 1) := by
    congr 1
    dsimp [z]
    norm_num
    ring
  have hden0 : Complex.Gamma ((↑k : ℂ) + ↑N + 1 - x) = Complex.Gamma z := by
    congr 1
    dsimp [z]
    ring
  rw [hden1, hden0, hstep, hzneg]
  simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Exact finite-product form of the transform-side Gamma profile.

This is the real Lean bridge from the Gamma quotient
`(-1)^k Γ(N+1-x) / Γ(k+N+1-x)` to the packet form
`1 / ∏_{j=1}^k (x - (N+j))`
used in the old `PO2` notes. -/
theorem po3_gamma_profile_eq_prod (N : ℕ) (x : ℂ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) :
    ∀ k,
      po3_gamma_profile N x k =
        Finset.prod (Finset.range k) (fun j => (x - (N + j + 1 : ℕ) : ℂ)⁻¹) := by
  intro k
  induction k with
  | zero =>
      simpa using po3_gamma_profile_zero N x hbase
  | succ k ih =>
      rw [po3_gamma_profile_succ N x k hbase, ih, Finset.prod_range_succ]
      simp [mul_comm]

theorem po3_gamma_profile_factor_ne_zero (N : ℕ) (x : ℂ) (j : ℕ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) :
    (x - (N + j + 1 : ℕ) : ℂ) ≠ 0 := by
  intro hx
  apply hbase j
  have hx' : x = (N + j + 1 : ℕ) := sub_eq_zero.mp hx
  rw [hx']
  norm_num

/-- The reciprocal-product avatar is exact: after multiplying by the matching
finite denominator packet, one gets `1`. -/
theorem po3_gamma_profile_mul_prod_eq_one (N : ℕ) (x : ℂ)
    (hbase : ∀ m : ℕ, ((N + 1 : ℂ) - x) ≠ -m) (k : ℕ) :
    po3_gamma_profile N x k *
        Finset.prod (Finset.range k) (fun j => (x - (N + j + 1 : ℕ) : ℂ)) = 1 := by
  rw [po3_gamma_profile_eq_prod N x hbase k]
  calc
    (Finset.prod (Finset.range k) (fun j => (x - (N + j + 1 : ℕ) : ℂ)⁻¹)) *
        Finset.prod (Finset.range k) (fun j => (x - (N + j + 1 : ℕ) : ℂ))
        =
        Finset.prod (Finset.range k)
          (fun j => ((x - (N + j + 1 : ℕ) : ℂ)⁻¹ * (x - (N + j + 1 : ℕ) : ℂ))) := by
            symm
            exact Finset.prod_mul_distrib
    _ = Finset.prod (Finset.range k) (fun _ => (1 : ℂ)) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          exact inv_mul_cancel₀ (po3_gamma_profile_factor_ne_zero N x j hbase)
    _ = 1 := by simp

/-- Finite packet extracted from the transform-side Gamma profile ancestor. -/
def po3_gamma_packet {ι : Type*} (N : ℕ) (packet : Finset ι) (coeff : ι → ℂ)
    (support : ι → ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ packet, coeff i * po3_gamma_profile N (support i) k

/-- Exact rewrite of a finite Gamma packet into the reciprocal-product avatar.

This is the first honest Lean landing surface for a future top-cluster /
dominant-packet estimate: finite packets of the real transform-side tower can
now be stated directly as finite sums of reciprocal products. -/
theorem po3_gamma_packet_eq_sum_prod {ι : Type*} (N : ℕ) (packet : Finset ι)
    (coeff : ι → ℂ) (support : ι → ℂ)
    (hbase : ∀ i ∈ packet, ∀ m : ℕ, ((N + 1 : ℂ) - support i) ≠ -m) :
    ∀ k,
      po3_gamma_packet N packet coeff support k =
        ∑ i ∈ packet,
          coeff i * Finset.prod (Finset.range k)
            (fun j => (support i - (N + j + 1 : ℕ) : ℂ)⁻¹) := by
  intro k
  unfold po3_gamma_packet
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [po3_gamma_profile_eq_prod N (support i) (hbase i hi) k]

/-- Named transform-side data packet for the live `PO3-square.2d3` wall.

This is the first honest Lean-facing landing surface for the real formula map
already pinned in the repo:

- `Ya` is the one-sided paired support `Y_a = {x_γ, x_γ - 1}`;
- `Ak` is the signed main tower on the real transform side;
- `Bk` is the mirror tower;
- `po3_gamma_profile` is the common Gamma-profile ancestor from the old `PO2`
  direct-receiver notes.

The record stays intentionally weak: it names the real objects and their
support geometry, but it does not pretend that the signed rightmost estimate is
already proved. -/
structure PO3SquareTransformSideData (ι γ : Type*) where
  N : ℕ
  xGamma : γ → ℂ
  Ya : ι → ℂ
  Ak : ℕ → ℂ
  Bk : ℕ → ℂ
  paired_support : ∀ y, ∃ g, Ya y = xGamma g ∨ Ya y = xGamma g - 1

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

section

variable {ι γ : Type*}

/-- Honest transform-side specialization of the abstract dominant-packet feeder.

This wrapper does not add a lower-bound theorem. It only says:
the future real `PO3-square.2d3` certificate should name the actual transform-
side support/tower data (`Y_a`, `x_γ`, `A_k`, `B_k`) and then prove that this
data fits the already-frozen dominant-packet shell. -/
structure PO3SquareTransformPacketCertificate (ι γ : Type*)
    extends PO3SquareDominantPacketCertificate (𝕜 := ℂ) where
  transform : PO3SquareTransformSideData ι γ
  main_is_Ak : mainTower = transform.Ak
  mirror_is_Bk : mirrorTower = transform.Bk

/-- Direct transform-side consumer:
once the real `A_k/B_k` packet is packaged into the frozen dominant-packet
certificate, the existing shell already returns the exact
`PO3-square.2d2` target. -/
theorem po3_square_signed_dominance_target_of_transform_packet_certificate
    (cert : PO3SquareTransformPacketCertificate ι γ) :
    po3_square_signed_dominance_target cert.transform.Ak cert.transform.Bk := by
  have hbase :
      po3_square_signed_dominance_target cert.mainTower cert.mirrorTower :=
    po3_square_signed_dominance_target_of_certificate
      cert.toPO3SquareDominantPacketCertificate
  simpa [cert.main_is_Ak, cert.mirror_is_Bk] using hbase

/-- Contradiction form of the same transform-side feeder. -/
theorem po3_square_false_of_transform_wall_and_packet_certificate
    (cert : PO3SquareTransformPacketCertificate ι γ)
    (hwall : ∀ k, cert.transform.Ak k = cert.transform.Bk k) :
    False := by
  have hwall' : ∀ k, cert.mainTower k = cert.mirrorTower k := by
    intro k
    simpa [cert.main_is_Ak, cert.mirror_is_Bk] using hwall k
  exact
    po3_square_false_of_wall_and_certificate
      cert.toPO3SquareDominantPacketCertificate
      hwall'

end

end

end Q3.Proofs.PO3Cert
