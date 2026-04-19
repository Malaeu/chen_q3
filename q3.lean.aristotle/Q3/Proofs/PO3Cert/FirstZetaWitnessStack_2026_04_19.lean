import Q3.Proofs.PO3Cert.FirstZetaPrefix3_2026_04_19

/-!
Reusable honest witness-stack package for the first decimal-28 zeta packet.

This file does not add new witness mathematics. Its role is to expose the now
closed local `a = 1` packet as one named shell-facing object:

- singleton obstructions for `γ₀, γ₁, γ₂`,
- the honest `prefix2` obstruction,
- the honest `prefix3` obstruction.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge

/-- Shell-facing profile proposition for the first singleton witness `γ₀`. -/
abbrev po3_first_zeta_singleton_gamma0_profile : Prop :=
  ∃ u,
    po3_suzuki_raw_gamma_pm_singleton
        (1 : ℂ)
        po3_first_zeta_gamma0_decimal28
      = po3_suzuki_filtered_pm_candidate u

/-- Shell-facing profile proposition for the second singleton witness `γ₁`. -/
abbrev po3_first_zeta_singleton_gamma1_profile : Prop :=
  ∃ u,
    po3_suzuki_raw_gamma_pm_singleton
        (1 : ℂ)
        po3_first_zeta_gamma1_decimal28
      = po3_suzuki_filtered_pm_candidate u

/-- Shell-facing profile proposition for the third singleton witness `γ₂`. -/
abbrev po3_first_zeta_singleton_gamma2_profile : Prop :=
  ∃ u,
    po3_suzuki_raw_gamma_pm_singleton
        (1 : ℂ)
        po3_first_zeta_gamma2_decimal28
      = po3_suzuki_filtered_pm_candidate u

/-- Shell-facing profile proposition for the concrete first-zeta `prefix2`
packet at `a = 1`. -/
abbrev po3_first_zeta_prefix2_profile : Prop :=
  ∃ u,
    po3_suzuki_raw_gamma_pm_prefix2
        (1 : ℂ)
        po3_first_zeta_gamma0_decimal28
        po3_first_zeta_gamma1_decimal28
      = po3_suzuki_filtered_pm_candidate u

/-- Shell-facing profile proposition for the concrete first-zeta `prefix3`
packet at `a = 1`. -/
abbrev po3_first_zeta_prefix3_profile : Prop :=
  ∃ u,
    po3_suzuki_raw_gamma_pm_prefix3
        (1 : ℂ)
        po3_first_zeta_gamma0_decimal28
        po3_first_zeta_gamma1_decimal28
        po3_first_zeta_gamma2_decimal28
      = po3_suzuki_filtered_pm_candidate u

/-- Finite tag type for the initial local first-zeta packet stack at `a = 1`. -/
inductive po3_first_zeta_initial_packet_tag where
  | singletonGamma0
  | singletonGamma1
  | singletonGamma2
  | prefix2
  | prefix3
  deriving DecidableEq, Repr

/-- Raw shell packet attached to a given tag of the initial first-zeta stack. -/
noncomputable def po3_first_zeta_initial_packet_raw :
    po3_first_zeta_initial_packet_tag → ℕ → ℕ → ℂ
  | .singletonGamma0 =>
      po3_suzuki_raw_gamma_pm_singleton
        (1 : ℂ)
        po3_first_zeta_gamma0_decimal28
  | .singletonGamma1 =>
      po3_suzuki_raw_gamma_pm_singleton
        (1 : ℂ)
        po3_first_zeta_gamma1_decimal28
  | .singletonGamma2 =>
      po3_suzuki_raw_gamma_pm_singleton
        (1 : ℂ)
        po3_first_zeta_gamma2_decimal28
  | .prefix2 =>
      po3_suzuki_raw_gamma_pm_prefix2
        (1 : ℂ)
        po3_first_zeta_gamma0_decimal28
        po3_first_zeta_gamma1_decimal28
  | .prefix3 =>
      po3_suzuki_raw_gamma_pm_prefix3
        (1 : ℂ)
        po3_first_zeta_gamma0_decimal28
        po3_first_zeta_gamma1_decimal28
        po3_first_zeta_gamma2_decimal28

/-- Shell-facing candidate predicate for a tagged packet from the initial
first-zeta stack. -/
def po3_first_zeta_initial_packet_profile_of_tag
    (tag : po3_first_zeta_initial_packet_tag) : Prop :=
  ∃ u, po3_first_zeta_initial_packet_raw tag = po3_suzuki_filtered_pm_candidate u

/-- The reusable local kill-layer carried by the first decimal-28 zeta witness
stack at `a = 1`. -/
def po3_first_zeta_initial_packet_kill_layer : Prop :=
  ¬ po3_first_zeta_singleton_gamma0_profile ∧
    ¬ po3_first_zeta_singleton_gamma1_profile ∧
    ¬ po3_first_zeta_singleton_gamma2_profile ∧
    ¬ po3_first_zeta_prefix2_profile ∧
    ¬ po3_first_zeta_prefix3_profile

/-- Honest theorem-level realization of the full first-zeta local kill-layer. -/
theorem po3_first_zeta_initial_packet_kill_layer_honest :
    po3_first_zeta_initial_packet_kill_layer := by
  refine ⟨po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma0_decimal28, ?_⟩
  refine ⟨po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma1_decimal28, ?_⟩
  refine ⟨po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma2_decimal28, ?_⟩
  refine ⟨po3_no_suzuki_raw_gamma_pm_prefix2_from_first_zeta_gap_sum2_honest, ?_⟩
  exact po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_sum3_honest

/-- Direct shell-consumer theorem: no tagged packet in the initial first-zeta
stack can equal a one-variable `(+,-)` candidate. -/
theorem po3_no_suzuki_filtered_pm_candidate_of_first_zeta_initial_packet
    (tag : po3_first_zeta_initial_packet_tag) :
    ¬ po3_first_zeta_initial_packet_profile_of_tag tag := by
  cases tag
  · simpa [po3_first_zeta_initial_packet_profile_of_tag,
      po3_first_zeta_initial_packet_raw, po3_first_zeta_singleton_gamma0_profile] using
      po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma0_decimal28
  · simpa [po3_first_zeta_initial_packet_profile_of_tag,
      po3_first_zeta_initial_packet_raw, po3_first_zeta_singleton_gamma1_profile] using
      po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma1_decimal28
  · simpa [po3_first_zeta_initial_packet_profile_of_tag,
      po3_first_zeta_initial_packet_raw, po3_first_zeta_singleton_gamma2_profile] using
      po3_no_suzuki_raw_gamma_pm_singleton_from_first_zeta_gamma2_decimal28
  · simpa [po3_first_zeta_initial_packet_profile_of_tag,
      po3_first_zeta_initial_packet_raw, po3_first_zeta_prefix2_profile] using
      po3_no_suzuki_raw_gamma_pm_prefix2_from_first_zeta_gap_sum2_honest
  · simpa [po3_first_zeta_initial_packet_profile_of_tag,
      po3_first_zeta_initial_packet_raw, po3_first_zeta_prefix3_profile] using
      po3_no_suzuki_raw_gamma_pm_prefix3_from_first_zeta_gap_sum3_honest

/-- Direct pointwise shell bridge: each tagged raw packet from the initial
first-zeta stack differs from every one-variable `(+,-)` candidate. -/
theorem po3_first_zeta_initial_packet_raw_ne_filtered_candidate
    (tag : po3_first_zeta_initial_packet_tag)
    (u : ℕ → ℂ) :
    po3_first_zeta_initial_packet_raw tag ≠ po3_suzuki_filtered_pm_candidate u := by
  intro hEq
  exact
    po3_no_suzuki_filtered_pm_candidate_of_first_zeta_initial_packet tag
      ⟨u, hEq⟩

/-- Collapsed shell form of the same direct bridge: no tagged raw packet from
the initial first-zeta stack equals any one-variable `(+,-)` candidate. -/
theorem po3_no_tagged_first_zeta_initial_packet_eq_filtered_candidate :
    ¬ ∃ tag : po3_first_zeta_initial_packet_tag, ∃ u : ℕ → ℂ,
      po3_first_zeta_initial_packet_raw tag = po3_suzuki_filtered_pm_candidate u := by
  intro h
  rcases h with ⟨tag, u, hEq⟩
  exact po3_first_zeta_initial_packet_raw_ne_filtered_candidate tag u hEq

/-- Transport the direct raw-packet bridge to an arbitrary shell kernel `K`
once `K` is identified with a fixed tagged first-zeta packet. -/
theorem po3_no_filtered_candidate_of_eq_first_zeta_initial_packet_raw
    {K : ℕ → ℕ → ℂ}
    (tag : po3_first_zeta_initial_packet_tag)
    (hK : K = po3_first_zeta_initial_packet_raw tag) :
    ¬ ∃ u : ℕ → ℂ, K = po3_suzuki_filtered_pm_candidate u := by
  intro h
  rcases h with ⟨u, hu⟩
  rw [hK] at hu
  exact po3_first_zeta_initial_packet_raw_ne_filtered_candidate tag u hu

/-- Existential shell form of the same transport theorem: any kernel that is
one of the tagged first-zeta packets is automatically excluded from the
one-variable filtered `(+,-)` shell. -/
theorem po3_no_filtered_candidate_of_exists_eq_first_zeta_initial_packet_raw
    {K : ℕ → ℕ → ℂ}
    (hpacket : ∃ tag : po3_first_zeta_initial_packet_tag,
      K = po3_first_zeta_initial_packet_raw tag) :
    ¬ ∃ u : ℕ → ℂ, K = po3_suzuki_filtered_pm_candidate u := by
  intro h
  rcases hpacket with ⟨tag, hK⟩
  exact po3_no_filtered_candidate_of_eq_first_zeta_initial_packet_raw tag hK h

/-- Contradiction form for the same consumer layer on an arbitrary shell
kernel `K`. -/
theorem po3_false_of_exists_eq_first_zeta_initial_packet_raw_and_filtered_candidate
    {K : ℕ → ℕ → ℂ}
    (hpacket : ∃ tag : po3_first_zeta_initial_packet_tag,
      K = po3_first_zeta_initial_packet_raw tag)
    (hcand : ∃ u : ℕ → ℂ, K = po3_suzuki_filtered_pm_candidate u) :
    False := by
  exact po3_no_filtered_candidate_of_exists_eq_first_zeta_initial_packet_raw
    hpacket hcand

/-- Named shell predicate for the family of kernels carried by the initial
first-zeta packet stack. This is the kernel-level wrapper around the tagged raw
packet family. -/
def po3_first_zeta_initial_packet_kernel (K : ℕ → ℕ → ℂ) : Prop :=
  ∃ tag : po3_first_zeta_initial_packet_tag,
    K = po3_first_zeta_initial_packet_raw tag

/-- Pointwise consumer theorem on the named kernel family: a kernel from the
initial first-zeta family differs from every filtered `(+,-)` candidate. -/
theorem po3_first_zeta_initial_packet_kernel_ne_filtered_candidate
    {K : ℕ → ℕ → ℂ}
    (hK : po3_first_zeta_initial_packet_kernel K)
    (u : ℕ → ℂ) :
    K ≠ po3_suzuki_filtered_pm_candidate u := by
  intro hEq
  exact
    po3_no_filtered_candidate_of_exists_eq_first_zeta_initial_packet_raw hK
      ⟨u, hEq⟩

/-- Negated-existential shell theorem on the named first-zeta kernel family. -/
theorem po3_no_filtered_candidate_of_first_zeta_initial_packet_kernel
    {K : ℕ → ℕ → ℂ}
    (hK : po3_first_zeta_initial_packet_kernel K) :
    ¬ ∃ u : ℕ → ℂ, K = po3_suzuki_filtered_pm_candidate u := by
  exact po3_no_filtered_candidate_of_exists_eq_first_zeta_initial_packet_raw hK

/-- Contradiction form on the named first-zeta kernel family. -/
theorem po3_false_of_first_zeta_initial_packet_kernel_and_filtered_candidate
    {K : ℕ → ℕ → ℂ}
    (hK : po3_first_zeta_initial_packet_kernel K)
    (hcand : ∃ u : ℕ → ℂ, K = po3_suzuki_filtered_pm_candidate u) :
    False := by
  exact po3_no_filtered_candidate_of_first_zeta_initial_packet_kernel hK hcand

/-- Direct bridge from the named first-zeta kernel family to the generic shell
criterion: such a kernel cannot be anti-diagonally invariant. -/
theorem po3_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel
    {K : ℕ → ℕ → ℂ}
    (hK : po3_first_zeta_initial_packet_kernel K) :
    ¬ ∀ m n m' n', m + n = m' + n' → K m n = K m' n' := by
  intro hanti
  apply po3_no_filtered_candidate_of_first_zeta_initial_packet_kernel hK
  exact (po3_exists_suzuki_filtered_pm_candidate_iff K).2 hanti

/-- Contradiction form of the same shell bridge on the anti-diagonal-invariance
side. -/
theorem po3_false_of_first_zeta_initial_packet_kernel_and_antidiagonal_invariant
    {K : ℕ → ℕ → ℂ}
    (hK : po3_first_zeta_initial_packet_kernel K)
    (hanti : ∀ m n m' n', m + n = m' + n' → K m n = K m' n') :
    False := by
  exact po3_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel hK hanti

/-- No member of the initial first-zeta witness stack can come from a
one-variable `(+,-)` profile. This is the disjunctive shell-facing form of the
same local kill-layer. -/
def po3_first_zeta_some_initial_packet_profile : Prop :=
  ∃ tag : po3_first_zeta_initial_packet_tag,
    po3_first_zeta_initial_packet_profile_of_tag tag

theorem po3_first_zeta_some_initial_packet_profile_false_honest :
    ¬ po3_first_zeta_some_initial_packet_profile := by
  intro h
  rcases h with ⟨tag, htag⟩
  exact po3_no_suzuki_filtered_pm_candidate_of_first_zeta_initial_packet tag htag

end Q3.Proofs.PO3Cert
