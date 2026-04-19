import Q3.Proofs.PO3Cert.FirstZetaWitnessStack_2026_04_19

/-!
`PO3-square.1` bridge for the initial first-zeta witness stack at `a = 1`.

This file adds no new witness mathematics. Its role is to expose the already
closed `first-zeta` packet stack under the exact square-side shell shape needed
upstream:

- if a square-side kernel is one tagged raw packet from the initial stack, then
  it cannot equal any one-variable filtered `(+,-)` candidate;
- equivalently, it cannot be anti-diagonally invariant;
- hence any attempted `PO3-square.1` identification with that local packet is
  killed immediately.
-/

namespace Q3.Proofs.PO3Cert

open Q3.HBridge

/-- `PO3-square.1` shell form for a concrete tagged raw packet: it cannot come
from a one-variable filtered `(+,-)` candidate. -/
theorem po3_square1_no_filtered_candidate_of_first_zeta_initial_packet_tag
    (tag : po3_first_zeta_initial_packet_tag) :
    ¬ ∃ u : ℕ → ℂ,
      po3_first_zeta_initial_packet_raw tag = po3_suzuki_filtered_pm_candidate u := by
  exact po3_no_suzuki_filtered_pm_candidate_of_first_zeta_initial_packet tag

/-- `PO3-square.1` shell form for a concrete tagged raw packet: it cannot be
anti-diagonally invariant. -/
theorem po3_square1_no_antidiagonal_invariant_of_first_zeta_initial_packet_tag
    (tag : po3_first_zeta_initial_packet_tag) :
    ¬ ∀ m n m' n', m + n = m' + n' →
        po3_first_zeta_initial_packet_raw tag m n =
          po3_first_zeta_initial_packet_raw tag m' n' := by
  exact
    po3_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel
      ⟨tag, rfl⟩

/-- Transport the `PO3-square.1` filtered-candidate kill to an arbitrary
kernel once that kernel is identified with one tagged raw packet from the
initial first-zeta stack. -/
theorem po3_square1_no_filtered_candidate_of_eq_first_zeta_initial_packet_raw
    {K : ℕ → ℕ → ℂ}
    (tag : po3_first_zeta_initial_packet_tag)
    (hK : K = po3_first_zeta_initial_packet_raw tag) :
    ¬ ∃ u : ℕ → ℂ, K = po3_suzuki_filtered_pm_candidate u := by
  exact po3_no_filtered_candidate_of_eq_first_zeta_initial_packet_raw tag hK

/-- Transport the `PO3-square.1` anti-diagonal kill to an arbitrary kernel once
that kernel is identified with one tagged raw packet from the initial first-zeta
stack. -/
theorem po3_square1_no_antidiagonal_invariant_of_eq_first_zeta_initial_packet_raw
    {K : ℕ → ℕ → ℂ}
    (tag : po3_first_zeta_initial_packet_tag)
    (hK : K = po3_first_zeta_initial_packet_raw tag) :
    ¬ ∀ m n m' n', m + n = m' + n' → K m n = K m' n' := by
  exact
    po3_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel
      ⟨tag, hK⟩

/-- Contradiction form of the same `PO3-square.1` bridge for an arbitrary
kernel identified with one tagged raw packet from the initial first-zeta
stack. -/
theorem po3_square1_false_of_eq_first_zeta_initial_packet_raw_and_antidiagonal_invariant
    {K : ℕ → ℕ → ℂ}
    (tag : po3_first_zeta_initial_packet_tag)
    (hK : K = po3_first_zeta_initial_packet_raw tag)
    (hanti : ∀ m n m' n', m + n = m' + n' → K m n = K m' n') :
    False := by
  exact
    po3_square1_no_antidiagonal_invariant_of_eq_first_zeta_initial_packet_raw
      tag hK hanti

/-- Predicate-level `PO3-square.1` bridge: every kernel from the initial
first-zeta packet family already fails anti-diagonal invariance. -/
theorem po3_square1_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel
    {K : ℕ → ℕ → ℂ}
    (hK : po3_first_zeta_initial_packet_kernel K) :
    ¬ ∀ m n m' n', m + n = m' + n' → K m n = K m' n' := by
  exact po3_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel hK

/-- Predicate-level contradiction form for the same `PO3-square.1` bridge. -/
theorem po3_square1_false_of_first_zeta_initial_packet_kernel_and_antidiagonal_invariant
    {K : ℕ → ℕ → ℂ}
    (hK : po3_first_zeta_initial_packet_kernel K)
    (hanti : ∀ m n m' n', m + n = m' + n' → K m n = K m' n') :
    False := by
  exact
    po3_square1_no_antidiagonal_invariant_of_first_zeta_initial_packet_kernel
      hK hanti

end Q3.Proofs.PO3Cert
