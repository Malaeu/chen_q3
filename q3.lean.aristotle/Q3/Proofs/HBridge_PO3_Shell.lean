import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
import Q3.Basic.Defs

open scoped BigOperators

/-!
# H-bridge PO3 shell

This file records the smallest algebraic handoff behind the `PO3` packet.
It does **not** formalize the analytic content of cross-sign boundary
cancellation. Instead, it formalizes the logical shell consumed by the
downstream Door-2 / upper-bridge notes:

- `PO2_shell`: the mixed block has only boundary-plus-cap remainder;
- `PO3a`: the cross-sign boundary term cancels;
- therefore `PO3b`: the mixed block is cap-only;
- and by symmetry `PO3c`: the mirrored cross-sign boundary also cancels.

The point is to freeze the executable reduction before attaching the genuine Q3
objects.
-/

namespace Q3
namespace HBridge

section PO3Shell

variable {A : Type*} [AddGroup A]

/-- Abstract finite-matrix receiver for `PO3a`: if the boundary channel is
represented by a finite cancellation packet `A + B + M`, and that packet
vanishes, then the boundary channel itself vanishes. -/
theorem po3_boundary_zero_of_matrix_receiver
    (D_partial_pm receiver A_mat B_mat M_mat : A)
    (hreceiver : D_partial_pm = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_partial_pm = 0 := by
  calc
    D_partial_pm = receiver := hreceiver
    _ = A_mat + B_mat + M_mat := hmatrix
    _ = 0 := hcancel

/-- Abstract `PO2` shell: the mixed block splits into boundary plus cap. -/
theorem po3_cap_only_of_po2_shell
    (D_N_pm D_partial_pm D_cap_pm : A)
    (hpo2 : D_N_pm = D_partial_pm + D_cap_pm)
    (hpo3a : D_partial_pm = 0) :
    D_N_pm = D_cap_pm := by
  calc
    D_N_pm = D_partial_pm + D_cap_pm := hpo2
    _ = 0 + D_cap_pm := by simp [hpo3a]
    _ = D_cap_pm := zero_add _

/-- Combined shell: `PO2` plus the finite-matrix receiver already implies the
cap-only mixed block conclusion. -/
theorem po3_cap_only_of_po2_and_matrix_receiver
    (D_N_pm D_partial_pm D_cap_pm receiver A_mat B_mat M_mat : A)
    (hpo2 : D_N_pm = D_partial_pm + D_cap_pm)
    (hreceiver : D_partial_pm = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_N_pm = D_cap_pm := by
  apply po3_cap_only_of_po2_shell
  · exact hpo2
  · exact po3_boundary_zero_of_matrix_receiver
      D_partial_pm receiver A_mat B_mat M_mat hreceiver hmatrix hcancel

end PO3Shell

section PO3WeakerBridge

variable {A : Type*} [AddGroup A]

/-- Abstract weaker bridge (`PO3a-A + PO3a-B`):
if the genuine boundary packet splits into a zero-endpoint part and an
endpoint-word part, and the zero-endpoint packet cancels globally, then only
the endpoint-word packet remains. -/
theorem po3_endpoint_packet_of_weaker_bridge
    (D_partial_pm zero_endpoint_packet endpoint_word_packet : A)
    (hsplit : D_partial_pm = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0) :
    D_partial_pm = endpoint_word_packet := by
  calc
    D_partial_pm = zero_endpoint_packet + endpoint_word_packet := hsplit
    _ = 0 + endpoint_word_packet := by simp [hzero]
    _ = endpoint_word_packet := zero_add _

/-- Once the weaker bridge lands and the surviving endpoint-word packet enters
the finite receiver, the boundary channel already vanishes. -/
theorem po3_boundary_zero_of_weaker_bridge_and_matrix_receiver
    (D_partial_pm zero_endpoint_packet endpoint_word_packet receiver A_mat B_mat M_mat : A)
    (hsplit : D_partial_pm = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0)
    (hreceiver : endpoint_word_packet = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_partial_pm = 0 := by
  calc
    D_partial_pm = endpoint_word_packet := by
      exact po3_endpoint_packet_of_weaker_bridge
        D_partial_pm zero_endpoint_packet endpoint_word_packet hsplit hzero
    _ = receiver := hreceiver
    _ = A_mat + B_mat + M_mat := hmatrix
    _ = 0 := hcancel

/-- `PO2` plus the weaker bridge plus the finite receiver already imply the
cap-only conclusion. This is the exact shell needed before plugging in the real
Volterra/endpoint packet. -/
theorem po3_cap_only_of_po2_and_weaker_bridge
    (D_N_pm D_partial_pm D_cap_pm zero_endpoint_packet endpoint_word_packet
      receiver A_mat B_mat M_mat : A)
    (hpo2 : D_N_pm = D_partial_pm + D_cap_pm)
    (hsplit : D_partial_pm = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0)
    (hreceiver : endpoint_word_packet = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_N_pm = D_cap_pm := by
  apply po3_cap_only_of_po2_shell
  · exact hpo2
  · exact po3_boundary_zero_of_weaker_bridge_and_matrix_receiver
      D_partial_pm zero_endpoint_packet endpoint_word_packet
      receiver A_mat B_mat M_mat hsplit hzero hreceiver hmatrix hcancel

end PO3WeakerBridge

section PO3AntiderivativeTransport

variable {A : Type*} [AddGroup A]

/-- `PO3a-A` shell: once the genuine boundary packet is transported to the
Volterra-antiderivative side and expanded into a zero-endpoint part plus an
endpoint-word part, the active weaker bridge reduces immediately to the
endpoint packet. -/
theorem po3_endpoint_packet_of_antiderivative_transport
    (D_partial_pm antiderivative_packet zero_endpoint_packet endpoint_word_packet : A)
    (htransport : D_partial_pm = antiderivative_packet)
    (hexpand : antiderivative_packet = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0) :
    D_partial_pm = endpoint_word_packet := by
  calc
    D_partial_pm = antiderivative_packet := htransport
    _ = zero_endpoint_packet + endpoint_word_packet := hexpand
    _ = 0 + endpoint_word_packet := by simp [hzero]
    _ = endpoint_word_packet := zero_add _

/-- Combined `PO3a-A -> PO3a-B -> finite receiver` shell: once the
antiderivative transport packet collapses to the endpoint-word packet, the
already frozen finite receiver kills the cross-sign boundary channel. -/
theorem po3_boundary_zero_of_antiderivative_transport_and_matrix_receiver
    (D_partial_pm antiderivative_packet zero_endpoint_packet endpoint_word_packet
      receiver A_mat B_mat M_mat : A)
    (htransport : D_partial_pm = antiderivative_packet)
    (hexpand : antiderivative_packet = zero_endpoint_packet + endpoint_word_packet)
    (hzero : zero_endpoint_packet = 0)
    (hreceiver : endpoint_word_packet = receiver)
    (hmatrix : receiver = A_mat + B_mat + M_mat)
    (hcancel : A_mat + B_mat + M_mat = 0) :
    D_partial_pm = 0 := by
  calc
    D_partial_pm = endpoint_word_packet := by
      exact po3_endpoint_packet_of_antiderivative_transport
        D_partial_pm antiderivative_packet zero_endpoint_packet endpoint_word_packet
        htransport hexpand hzero
    _ = receiver := hreceiver
    _ = A_mat + B_mat + M_mat := hmatrix
    _ = 0 := hcancel

end PO3AntiderivativeTransport

section PO3RawSplitTransport

variable {A B : Type*} [AddGroup A] [AddGroup B]

/-- Early raw-defect bridge: if the raw defect already splits into bulk,
boundary, and cap channels, then any additive filtered pullback preserves that
split. This is the exact shell behind “first split the raw defect, then pull it
through `Δ_N`”. -/
theorem po3_filtered_split_of_raw_split
    (Φ : A →+ B)
    (R_raw R_bulk R_boundary R_cap : A) :
    R_raw = R_bulk + R_boundary + R_cap
      →
      Φ R_raw = Φ R_bulk + Φ R_boundary + Φ R_cap := by
  intro hsplit
  rw [hsplit, map_add, map_add]

/-- Packaged version of the same bridge with named filtered bulk/boundary/cap
channels. -/
theorem po3_filtered_named_split_of_raw_split
    (Φ : A →+ B)
    (R_raw R_bulk R_boundary R_cap : A)
    (D_filtered D_bulk D_boundary D_cap : B)
    (hsplit : R_raw = R_bulk + R_boundary + R_cap)
    (htransport : D_filtered = Φ R_raw)
    (hbulk : D_bulk = Φ R_bulk)
    (hboundary : D_boundary = Φ R_boundary)
    (hcap : D_cap = Φ R_cap) :
    D_filtered = D_bulk + D_boundary + D_cap := by
  calc
    D_filtered = Φ R_raw := htransport
    _ = Φ R_bulk + Φ R_boundary + Φ R_cap :=
      po3_filtered_split_of_raw_split Φ R_raw R_bulk R_boundary R_cap hsplit
    _ = D_bulk + D_boundary + D_cap := by
      rw [← hbulk, ← hboundary, ← hcap]

end PO3RawSplitTransport

section PO3EntrywiseRawSplit

variable {Coeff RawOp : Type*} [AddGroup Coeff] [AddGroup RawOp]

/-- Entrywise-to-operator packaging shell: if the raw coefficient defect has
already been split into bulk, boundary, and cap coefficient channels, and the
raw operator is additive in those coefficient packets, then the raw operator
inherits the same three-way split. This is the abstract `PO3a-A2` bridge. -/
theorem po3_raw_operator_split_of_entrywise_split
    (assemble : Coeff →+ RawOp)
    (δ rawBulk rawBoundary rawCap : Coeff) :
    δ = rawBulk + rawBoundary + rawCap
      →
      assemble δ = assemble rawBulk + assemble rawBoundary + assemble rawCap := by
  intro hsplit
  rw [hsplit, map_add, map_add]

end PO3EntrywiseRawSplit

section PO3CoefficientRewrites

variable {ι Δ A : Type*} [AddGroup A]

/-- If both pieces of the raw Q3 coefficient formula factor only through the
index difference, then their difference also factors through the same
difference. This is the abstract Toeplitz-persistence shell behind the raw
`q_{r,s}` formula. -/
theorem po3_difference_factorization_of_q_split
    (diff : ι → ι → Δ)
    (arch prime q : ι → ι → A)
    (archCoeff primeCoeff : Δ → A)
    (harch : ∀ r s, arch r s = archCoeff (diff r s))
    (hprime : ∀ r s, prime r s = primeCoeff (diff r s))
    (hq : ∀ r s, q r s = arch r s - prime r s) :
    ∃ qCoeff : Δ → A, ∀ r s, q r s = qCoeff (diff r s) := by
  refine ⟨fun k => archCoeff k - primeCoeff k, ?_⟩
  intro r s
  rw [hq r s, harch r s, hprime r s]

end PO3CoefficientRewrites

section PO3CoefficientRewritesCommRing

variable {ι A : Type*} [CommRing A]

/-- Once the model coefficients are rewritten as a Toeplitz packet minus a
Toeplitz prime packet, the raw defect rewrites as the archimedean mismatch plus
the prime packet. This isolates the only non-Toeplitz source on the raw side of
`PO3a-A2`. -/
theorem po3_delta_rewrite_of_q_split
    (w q toeplitz prime δ : ι → ι → A)
    (κ : A)
    (hδ : ∀ r s, δ r s = w r s - κ * q r s)
    (hq : ∀ r s, q r s = toeplitz r s - prime r s) :
    ∀ r s, δ r s = κ * prime r s + w r s - κ * toeplitz r s := by
  intro r s
  rw [hδ r s, hq r s]
  ring

/-- If the model-side packet takes the same value at two coefficient positions,
then the corresponding raw-defect difference is carried entirely by the Suzuki
side `w`. This records the coefficient-level fact that a Toeplitz model packet
cannot by itself generate raw boundary mismatch. -/
theorem po3_raw_defect_difference_of_equal_model_packet
    (w q δ : ι → ι → A)
    (κ : A)
    (r s r' s' : ι)
    (hδ : ∀ x y, δ x y = w x y - κ * q x y)
    (hq : q r s = q r' s') :
    δ r s - δ r' s' = w r s - w r' s' := by
  rw [hδ r s, hδ r' s', hq]
  ring

end PO3CoefficientRewritesCommRing

section PO3VolterraExtraction

variable {A : Type*} [Ring A]

/-- Algebraic two-endpoint expansion behind `PO3a-two-endpoint extraction`:
after expanding a left/right endpoint undoing defect, only the one-endpoint
left brick, the one-endpoint right brick, and the two-endpoint brick survive. -/
theorem po3_two_endpoint_expansion
    (L K R_left R_right N : A) :
    L * (((1 - R_left) * K * (1 - R_right)) - K) * N
      =
        -L * R_left * K * N
        - L * K * R_right * N
        + L * R_left * K * R_right * N := by
  noncomm_ring

end PO3VolterraExtraction

section PO3FiniteAntiderivativeMismatch

open Finset
open scoped BigOperators

variable {ι A : Type*} [Ring A]

/-- One summand of the finite antiderivative mismatch criterion: after
expanding `((1-R_left) K (1-R_right) - Lmid)`, one gets the zero-endpoint term,
the one-endpoint left/right bricks, and the two-endpoint brick. This is the
algebraic core behind the old `PO3a-finite antiderivative mismatch criterion`. -/
theorem po3_two_endpoint_mismatch_expansion
    (L K R_left R_right Lmid N : A) :
    L * (((1 - R_left) * K * (1 - R_right)) - Lmid) * N
      =
        L * (K - Lmid) * N
        - L * R_left * K * N
        - L * K * R_right * N
        + L * R_left * K * R_right * N := by
  noncomm_ring

/-- Finite-sum shell for `PO3a-A3`: if each summand has already been expanded
into zero-endpoint, one-endpoint, and two-endpoint packets, and the zero-endpoint
sum cancels globally, then the total defect is built only from endpoint words. -/
theorem po3_finite_antiderivative_mismatch_of_zero_endpoint_cancellation
    (s : Finset ι)
    (H zero left right two : ι → A)
    (hexpand : ∀ i, H i = zero i - left i - right i + two i)
    (hzero : Finset.sum s (fun i => zero i) = 0) :
    Finset.sum s (fun i => H i)
      =
        -(Finset.sum s (fun i => left i))
        - (Finset.sum s (fun i => right i))
        + Finset.sum s (fun i => two i) := by
  calc
    Finset.sum s (fun i => H i)
        = Finset.sum s (fun i => zero i - left i - right i + two i) := by
            simp [hexpand]
    _ = Finset.sum s (fun i => zero i)
          - Finset.sum s (fun i => left i)
          - Finset.sum s (fun i => right i)
          + Finset.sum s (fun i => two i) := by
            simp [Finset.sum_add_distrib, sub_eq_add_neg, add_assoc,
              add_left_comm, add_comm]
    _ = -(Finset.sum s (fun i => left i))
          - (Finset.sum s (fun i => right i))
          + Finset.sum s (fun i => two i) := by
          rw [hzero]
          abel_nf

/-- Finite-sum physical specialization of the mismatch shell: when the middle
kernel already equals the model kernel, the zero-endpoint packet vanishes
termwise and only endpoint words remain. This is the exact finite version of
the old one-kernel physical Volterra reduction. -/
theorem po3_finite_antiderivative_physical_specialization
    (s : Finset ι)
    (L K R_left R_right N : ι → A) :
    Finset.sum s (fun i => L i * (((1 - R_left i) * K i * (1 - R_right i)) - K i) * N i)
      =
        -(Finset.sum s (fun i => L i * R_left i * K i * N i))
        - (Finset.sum s (fun i => L i * K i * R_right i * N i))
        + Finset.sum s (fun i => L i * R_left i * K i * R_right i * N i) := by
  apply po3_finite_antiderivative_mismatch_of_zero_endpoint_cancellation
    (s := s)
    (H := fun i => L i * (((1 - R_left i) * K i * (1 - R_right i)) - K i) * N i)
    (zero := fun _ => 0)
    (left := fun i => L i * R_left i * K i * N i)
    (right := fun i => L i * K i * R_right i * N i)
    (two := fun i => L i * R_left i * K i * R_right i * N i)
  · intro i
    calc
      L i * (((1 - R_left i) * K i * (1 - R_right i)) - K i) * N i
          = -(L i * R_left i * K i * N i)
              - (L i * K i * R_right i * N i)
              + L i * R_left i * K i * R_right i * N i := by
                simpa using
                  (po3_two_endpoint_expansion
                    (L := L i) (K := K i) (R_left := R_left i)
                    (R_right := R_right i) (N := N i))
      _ = 0
            - (L i * R_left i * K i * N i)
            - (L i * K i * R_right i * N i)
            + L i * R_left i * K i * R_right i * N i := by
              abel_nf
  · simp

end PO3FiniteAntiderivativeMismatch

section PO3DoubleTelescoping

open Finset
open scoped BigOperators

variable {A : Type*} [AddCommGroup A]

/-- One-dimensional telescoping identity on a tail written in `range` form. -/
theorem po3_sum_range_succ_sub (F : ℕ → A) :
    ∀ m, (∑ i ∈ Finset.range m, (F (i + 1) - F i)) = F m - F 0
  | 0 => by simp
  | m + 1 => by
      rw [Finset.sum_range_succ, po3_sum_range_succ_sub F m]
      abel_nf

/-- One-dimensional Newton-Leibniz / telescoping form. -/
theorem po3_telescoping_one_variable (F : ℕ → A) (m : ℕ) :
    F m = F 0 + (∑ i ∈ Finset.range m, (F (i + 1) - F i)) := by
  calc
    F m = F 0 + (F m - F 0) := by abel_nf
    _ = F 0 + (∑ i ∈ Finset.range m, (F (i + 1) - F i)) := by
          rw [po3_sum_range_succ_sub]

/-- Two-variable discrete telescoping identity: any defect on the tail splits
into the corner term, the row strip, the column strip, and the bulk mixed
difference term. This is the abstract `PO3a-A0` packet. -/
theorem po3_double_telescoping
    (D : ℕ → ℕ → A) (N m n : ℕ) :
    D (N + m) (N + n)
      =
        D N N
        + (∑ i ∈ Finset.range m, (D (N + i + 1) N - D (N + i) N))
        + (∑ j ∈ Finset.range n, (D N (N + j + 1) - D N (N + j)))
        + (∑ i ∈ Finset.range m,
            ∑ j ∈ Finset.range n,
              ((D (N + i + 1) (N + j + 1) - D (N + i) (N + j + 1))
                - (D (N + i + 1) (N + j) - D (N + i) (N + j)))) := by
  have hrow :
      D (N + m) (N + n)
        =
          D N (N + n)
          + ∑ i ∈ Finset.range m,
              (D (N + i + 1) (N + n) - D (N + i) (N + n)) := by
    simpa [Nat.add_assoc] using
      (po3_telescoping_one_variable (fun i => D (N + i) (N + n)) m)
  have hcol :
      D N (N + n)
        =
          D N N
          + ∑ j ∈ Finset.range n, (D N (N + j + 1) - D N (N + j)) := by
    simpa [Nat.add_assoc] using
      (po3_telescoping_one_variable (fun j => D N (N + j)) n)
  have hbulk :
      ∀ i,
        D (N + i + 1) (N + n) - D (N + i) (N + n)
          =
            (D (N + i + 1) N - D (N + i) N)
            + ∑ j ∈ Finset.range n,
                ((D (N + i + 1) (N + j + 1) - D (N + i) (N + j + 1))
                  - (D (N + i + 1) (N + j) - D (N + i) (N + j))) := by
    intro i
    simpa [Nat.add_assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (po3_telescoping_one_variable
        (fun j => D (N + i + 1) (N + j) - D (N + i) (N + j)) n)
  calc
    D (N + m) (N + n)
        =
          D N (N + n)
          + ∑ i ∈ Finset.range m,
              (D (N + i + 1) (N + n) - D (N + i) (N + n)) := hrow
    _ =
          D N (N + n)
          + ∑ i ∈ Finset.range m,
              ((D (N + i + 1) N - D (N + i) N)
                + ∑ j ∈ Finset.range n,
                    ((D (N + i + 1) (N + j + 1) - D (N + i) (N + j + 1))
                      - (D (N + i + 1) (N + j) - D (N + i) (N + j)))) := by
          simp_rw [hbulk]
    _ =
          D N N
          + ∑ j ∈ Finset.range n, (D N (N + j + 1) - D N (N + j))
          + ∑ i ∈ Finset.range m,
              ((D (N + i + 1) N - D (N + i) N)
                + ∑ j ∈ Finset.range n,
                    ((D (N + i + 1) (N + j + 1) - D (N + i) (N + j + 1))
                      - (D (N + i + 1) (N + j) - D (N + i) (N + j)))) := by
          rw [hcol]
    _ =
          D N N
          + ∑ j ∈ Finset.range n, (D N (N + j + 1) - D N (N + j))
          + (∑ i ∈ Finset.range m, (D (N + i + 1) N - D (N + i) N)
            + ∑ i ∈ Finset.range m,
                ∑ j ∈ Finset.range n,
                  ((D (N + i + 1) (N + j + 1) - D (N + i) (N + j + 1))
                    - (D (N + i + 1) (N + j) - D (N + i) (N + j)))) := by
          rw [Finset.sum_add_distrib]
    _ =
          D N N
          + ∑ i ∈ Finset.range m, (D (N + i + 1) N - D (N + i) N)
          + ∑ j ∈ Finset.range n, (D N (N + j + 1) - D N (N + j))
          + ∑ i ∈ Finset.range m,
              ∑ j ∈ Finset.range n,
                ((D (N + i + 1) (N + j + 1) - D (N + i) (N + j + 1))
                  - (D (N + i + 1) (N + j) - D (N + i) (N + j))) := by
          simp [add_assoc, add_left_comm, add_comm]

/-- `PO3a-A1` shell: once the corner plus row/column strips are collected into a
single boundary packet and the mixed interior double sum is identified with the
transported bulk packet, the whole defect already has the form
`boundary + bulk`. -/
theorem po3_boundary_plus_bulk_of_double_telescoping
    (D : ℕ → ℕ → A) (N m n : ℕ)
    (boundaryPacket bulkPacket : A)
    (hboundary :
      boundaryPacket =
        D N N
        + (∑ i ∈ Finset.range m, (D (N + i + 1) N - D (N + i) N))
        + (∑ j ∈ Finset.range n, (D N (N + j + 1) - D N (N + j))))
    (hbulk :
      bulkPacket =
        ∑ i ∈ Finset.range m,
          ∑ j ∈ Finset.range n,
            ((D (N + i + 1) (N + j + 1) - D (N + i) (N + j + 1))
              - (D (N + i + 1) (N + j) - D (N + i) (N + j)))) :
    D (N + m) (N + n) = boundaryPacket + bulkPacket := by
  calc
    D (N + m) (N + n)
        =
          D N N
          + (∑ i ∈ Finset.range m, (D (N + i + 1) N - D (N + i) N))
          + (∑ j ∈ Finset.range n, (D N (N + j + 1) - D N (N + j)))
          + (∑ i ∈ Finset.range m,
              ∑ j ∈ Finset.range n,
                ((D (N + i + 1) (N + j + 1) - D (N + i) (N + j + 1))
                  - (D (N + i + 1) (N + j) - D (N + i) (N + j)))) := by
          exact po3_double_telescoping D N m n
    _ = boundaryPacket + bulkPacket := by
          rw [← hboundary, ← hbulk]

/-- `PO3a-A0` in named packet form with the user-facing notation
`corner = c`, `row trace = α`, `column trace = β`, `mixed difference = K`,
based at the tail origin `N+1`. -/
theorem po3_double_telescoping_named_packets
    (D : ℕ → ℕ → A) (N m n : ℕ)
    (c : A) (α β : ℕ → A) (K : ℕ → ℕ → A)
    (hc : c = D (N + 1) (N + 1))
    (hα : ∀ r, α r = D (r + 1) (N + 1) - D r (N + 1))
    (hβ : ∀ s, β s = D (N + 1) (s + 1) - D (N + 1) s)
    (hK :
      ∀ r s,
        K r s =
          D (r + 1) (s + 1) - D (r + 1) s - D r (s + 1) + D r s) :
    D (N + 1 + m) (N + 1 + n)
      =
        c
        + (∑ i ∈ Finset.range m, α (N + 1 + i))
        + (∑ j ∈ Finset.range n, β (N + 1 + j))
        + (∑ i ∈ Finset.range m,
            ∑ j ∈ Finset.range n, K (N + 1 + i) (N + 1 + j)) := by
  calc
    D (N + 1 + m) (N + 1 + n)
        =
          D (N + 1) (N + 1)
          + (∑ i ∈ Finset.range m,
              (D (N + 1 + i + 1) (N + 1) - D (N + 1 + i) (N + 1)))
          + (∑ j ∈ Finset.range n,
              (D (N + 1) (N + 1 + j + 1) - D (N + 1) (N + 1 + j)))
          + (∑ i ∈ Finset.range m,
              ∑ j ∈ Finset.range n,
                ((D (N + 1 + i + 1) (N + 1 + j + 1) - D (N + 1 + i) (N + 1 + j + 1))
                  - (D (N + 1 + i + 1) (N + 1 + j) - D (N + 1 + i) (N + 1 + j)))) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            po3_double_telescoping D (N + 1) m n
    _ =
          c
          + (∑ i ∈ Finset.range m, α (N + 1 + i))
          + (∑ j ∈ Finset.range n, β (N + 1 + j))
          + (∑ i ∈ Finset.range m,
              ∑ j ∈ Finset.range n, K (N + 1 + i) (N + 1 + j)) := by
          rw [← hc]
          have hrow :
              (∑ i ∈ Finset.range m,
                  (D (N + 1 + i + 1) (N + 1) - D (N + 1 + i) (N + 1)))
                =
              (∑ i ∈ Finset.range m, α (N + 1 + i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hα (N + 1 + i)]
          have hcol :
              (∑ j ∈ Finset.range n,
                  (D (N + 1) (N + 1 + j + 1) - D (N + 1) (N + 1 + j)))
                =
              (∑ j ∈ Finset.range n, β (N + 1 + j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hβ (N + 1 + j)]
          have hbulk' :
              (∑ i ∈ Finset.range m,
                  ∑ j ∈ Finset.range n,
                    ((D (N + 1 + i + 1) (N + 1 + j + 1) - D (N + 1 + i) (N + 1 + j + 1))
                      - (D (N + 1 + i + 1) (N + 1 + j) - D (N + 1 + i) (N + 1 + j))))
                =
              (∑ i ∈ Finset.range m,
                  ∑ j ∈ Finset.range n, K (N + 1 + i) (N + 1 + j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [hK (N + 1 + i) (N + 1 + j)]
            abel_nf
          rw [hrow, hcol, hbulk']

/-- `PO3a-A1` in the same named notation: once the corner plus strips are
grouped into one boundary packet and the mixed difference packet is identified
with one bulk packet, the defect has the form `boundary + bulk`. -/
theorem po3_boundary_plus_bulk_of_named_packets
    (D : ℕ → ℕ → A) (N m n : ℕ)
    (c : A) (α β : ℕ → A) (K : ℕ → ℕ → A)
    (boundaryPacket bulkPacket : A)
    (hc : c = D (N + 1) (N + 1))
    (hα : ∀ r, α r = D (r + 1) (N + 1) - D r (N + 1))
    (hβ : ∀ s, β s = D (N + 1) (s + 1) - D (N + 1) s)
    (hK :
      ∀ r s,
        K r s =
          D (r + 1) (s + 1) - D (r + 1) s - D r (s + 1) + D r s)
    (hboundary :
      boundaryPacket =
        c
        + (∑ i ∈ Finset.range m, α (N + 1 + i))
        + (∑ j ∈ Finset.range n, β (N + 1 + j)))
    (hbulk :
      bulkPacket =
        ∑ i ∈ Finset.range m,
          ∑ j ∈ Finset.range n, K (N + 1 + i) (N + 1 + j)) :
    D (N + 1 + m) (N + 1 + n) = boundaryPacket + bulkPacket := by
  calc
    D (N + 1 + m) (N + 1 + n)
        =
          c
          + (∑ i ∈ Finset.range m, α (N + 1 + i))
          + (∑ j ∈ Finset.range n, β (N + 1 + j))
          + (∑ i ∈ Finset.range m,
              ∑ j ∈ Finset.range n, K (N + 1 + i) (N + 1 + j)) :=
          po3_double_telescoping_named_packets D N m n c α β K hc hα hβ hK
    _ = boundaryPacket + bulkPacket := by rw [← hboundary, ← hbulk]

end PO3DoubleTelescoping

section PO3NamedPacketLinearity

variable {𝕜 A : Type*} [Ring 𝕜] [AddCommGroup A] [Module 𝕜 A]

/-- Named `PO3a-A0` packets for a two-variable defect based at `N+1`. -/
def po3_corner_packet (D : ℕ → ℕ → A) (N : ℕ) : A :=
  D (N + 1) (N + 1)

def po3_row_trace_packet (D : ℕ → ℕ → A) (N r : ℕ) : A :=
  D (r + 1) (N + 1) - D r (N + 1)

def po3_column_trace_packet (D : ℕ → ℕ → A) (N s : ℕ) : A :=
  D (N + 1) (s + 1) - D (N + 1) s

def po3_mixed_packet (D : ℕ → ℕ → A) (r s : ℕ) : A :=
  D (r + 1) (s + 1) - D (r + 1) s - D r (s + 1) + D r s

/-- The four named packets are linear for defects of the form `X - κ • Y`. -/
theorem po3_named_packets_of_sub_smul
    (X Y D : ℕ → ℕ → A) (κ : 𝕜)
    (hD : ∀ r s, D r s = X r s - κ • Y r s) :
    (∀ N,
      po3_corner_packet D N
        =
          po3_corner_packet X N
          - κ • po3_corner_packet Y N)
      ∧
    (∀ N r,
      po3_row_trace_packet D N r
        =
          po3_row_trace_packet X N r
          - κ • po3_row_trace_packet Y N r)
      ∧
    (∀ N s,
      po3_column_trace_packet D N s
        =
          po3_column_trace_packet X N s
          - κ • po3_column_trace_packet Y N s)
      ∧
    (∀ r s,
      po3_mixed_packet D r s
        =
          po3_mixed_packet X r s
          - κ • po3_mixed_packet Y r s) := by
  constructor
  · intro N
    simp [po3_corner_packet, hD]
  constructor
  · intro N r
    simp [po3_row_trace_packet, hD, sub_eq_add_neg, smul_add]
    abel_nf
  constructor
  · intro N s
    simp [po3_column_trace_packet, hD, sub_eq_add_neg, smul_add]
    abel_nf
  · intro r s
    simp [po3_mixed_packet, hD, sub_eq_add_neg, smul_add]
    abel_nf

end PO3NamedPacketLinearity

section PO3FourTermStencil

variable {A : Type*} [AddCommGroup A]

/-- Common four-term filtered stencil on raw two-variable entries. -/
def po3_four_term_stencil (D : ℕ → ℕ → A) : ℕ → ℕ → A :=
  fun m n => D m n + D (m + 1) n + D m (n + 1) + D (m + 1) (n + 1)

/-- Corner packet of the four-term stencil. -/
theorem po3_corner_packet_of_four_term_stencil
    (D : ℕ → ℕ → A) (N : ℕ) :
    po3_corner_packet (po3_four_term_stencil D) N
      =
        D (N + 1) (N + 1)
        + D (N + 2) (N + 1)
        + D (N + 1) (N + 2)
        + D (N + 2) (N + 2) := by
  simp [po3_corner_packet, po3_four_term_stencil, Nat.add_left_comm, Nat.add_comm]

/-- Row trace packet of the four-term stencil. -/
theorem po3_row_trace_packet_of_four_term_stencil
    (D : ℕ → ℕ → A) (N r : ℕ) :
    po3_row_trace_packet (po3_four_term_stencil D) N r
      =
        D (r + 2) (N + 1)
        + D (r + 2) (N + 2)
        - D r (N + 1)
        - D r (N + 2) := by
  simp [po3_row_trace_packet, po3_four_term_stencil, Nat.add_left_comm, Nat.add_comm]
  abel_nf

/-- Column trace packet of the four-term stencil. -/
theorem po3_column_trace_packet_of_four_term_stencil
    (D : ℕ → ℕ → A) (N s : ℕ) :
    po3_column_trace_packet (po3_four_term_stencil D) N s
      =
        D (N + 1) (s + 2)
        + D (N + 2) (s + 2)
        - D (N + 1) s
        - D (N + 2) s := by
  simp [po3_column_trace_packet, po3_four_term_stencil, Nat.add_left_comm, Nat.add_comm]
  abel_nf

/-- Mixed packet of the four-term stencil. -/
theorem po3_mixed_packet_of_four_term_stencil
    (D : ℕ → ℕ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil D) r s
      =
        D (r + 2) (s + 2)
        - D (r + 2) s
        - D r (s + 2)
        + D r s := by
  simp [po3_mixed_packet, po3_four_term_stencil, Nat.add_left_comm, Nat.add_comm]
  abel_nf

/-- The common four-term stencil commutes with taking a defect of the form
`X - κ • Y`. -/
theorem po3_four_term_stencil_of_sub_smul
    {𝕜 : Type*} [Ring 𝕜] [Module 𝕜 A]
    (X Y D : ℕ → ℕ → A) (κ : 𝕜)
    (hD : ∀ r s, D r s = X r s - κ • Y r s) :
    ∀ m n,
      po3_four_term_stencil D m n
        =
          po3_four_term_stencil X m n
          - κ • po3_four_term_stencil Y m n := by
  intro m n
  simp [po3_four_term_stencil, hD, sub_eq_add_neg, smul_add]
  abel_nf

/-- Hence the named packets of a filtered defect `stencil(X - κY)` can be read
off from the filtered packets of `X` and `Y` separately. This is the direct
substitution shell for `X = w`, `Y = q`. -/
theorem po3_named_packets_of_four_term_stencil_sub_smul
    {𝕜 : Type*} [Ring 𝕜] [Module 𝕜 A]
    (X Y D : ℕ → ℕ → A) (κ : 𝕜)
    (hD : ∀ r s, D r s = X r s - κ • Y r s) :
    (∀ N,
      po3_corner_packet (po3_four_term_stencil D) N
        =
          po3_corner_packet (po3_four_term_stencil X) N
          - κ • po3_corner_packet (po3_four_term_stencil Y) N)
      ∧
    (∀ N r,
      po3_row_trace_packet (po3_four_term_stencil D) N r
        =
          po3_row_trace_packet (po3_four_term_stencil X) N r
          - κ • po3_row_trace_packet (po3_four_term_stencil Y) N r)
      ∧
    (∀ N s,
      po3_column_trace_packet (po3_four_term_stencil D) N s
        =
          po3_column_trace_packet (po3_four_term_stencil X) N s
          - κ • po3_column_trace_packet (po3_four_term_stencil Y) N s)
      ∧
    (∀ r s,
      po3_mixed_packet (po3_four_term_stencil D) r s
        =
          po3_mixed_packet (po3_four_term_stencil X) r s
          - κ • po3_mixed_packet (po3_four_term_stencil Y) r s) := by
  apply po3_named_packets_of_sub_smul
    (X := po3_four_term_stencil X)
    (Y := po3_four_term_stencil Y)
    (D := po3_four_term_stencil D)
    (κ := κ)
  intro r s
  exact po3_four_term_stencil_of_sub_smul X Y D κ hD r s

end PO3FourTermStencil

section PO3OneDimensionalProfiles

variable {A : Type*} [AddCommGroup A]

/-- Sum-profile kernel `u(m+n)`, matching the filtered `(+,-)` Q-side shape. -/
def po3_sum_kernel (u : ℕ → A) : ℕ → ℕ → A :=
  fun m n => u (m + n)

/-- Difference-profile kernel `u(m-n)`, written on integer indices to match
the filtered `(+,+)` Q-side shape. -/
def po3_difference_kernel (u : ℤ → A) : ℕ → ℕ → A :=
  fun m n => u ((m : ℤ) - (n : ℤ))

/-- The same one-variable profile, but read on nonnegative indices only. This
is the natural way the raw difference packet restricts to the `(+,-)` block,
where the difference variable becomes the sum `m+n`. -/
def po3_nat_profile_of_int (u : ℤ → A) : ℕ → A :=
  fun t => u (t : ℤ)

/-- Raw signed Section 8 packet depending only on the index difference. -/
def po3_signed_difference_kernel (u : ℤ → A) : ℤ → ℤ → A :=
  fun r s => u (r - s)

/-- One-dimensional filtered profile for the `(+,-)` Q-side family. -/
def po3_filtered_sum_profile (u : ℕ → A) : ℕ → A :=
  fun t => u t + u (t + 1) + u (t + 1) + u (t + 2)

/-- One-dimensional filtered profile for the `(+,+)` Q-side family. -/
def po3_filtered_difference_profile (u : ℤ → A) : ℤ → A :=
  fun k => u k + u (k + 1) + u (k - 1) + u k

/-- One-dimensional forward second difference on the sum variable. -/
def po3_forward_second_difference (u : ℕ → A) : ℕ → A :=
  fun t => u (t + 2) - u (t + 1) - u (t + 1) + u t

/-- One-dimensional centered second difference on the difference variable. -/
def po3_centered_second_difference (u : ℤ → A) : ℤ → A :=
  fun k => u k - u (k + 1) - u (k - 1) + u k

/-- Raw `q^{++}` / `q^{--}` model kernel: a difference-profile packet
`a_k - p_k`. -/
def po3_q_pp_kernel (a p : ℤ → A) : ℕ → ℕ → A :=
  po3_difference_kernel (fun k => a k - p k)

/-- Raw `q^{+-}` / `q^{-+}` model kernel: a sum-profile packet
`a_t - p_t`. -/
def po3_q_pm_kernel (a p : ℕ → A) : ℕ → ℕ → A :=
  po3_sum_kernel (fun t => a t - p t)

/-- Raw `q^{+-}` / `q^{-+}` model kernel, read from integer-valued profiles by
restriction to the nonnegative sum variable. -/
def po3_q_pm_kernel_of_int (a p : ℤ → A) : ℕ → ℕ → A :=
  po3_q_pm_kernel (po3_nat_profile_of_int a) (po3_nat_profile_of_int p)

/-- Recover a candidate sum-profile from a two-index kernel by freezing the
second coordinate at `0`. -/
def po3_sum_profile_of_kernel (K : ℕ → ℕ → A) : ℕ → A :=
  fun t => K t 0

/-- Recover a candidate difference-profile from a two-index kernel by freezing
one coordinate on the appropriate side of `0`. -/
def po3_difference_profile_of_kernel (K : ℕ → ℕ → A) : ℤ → A
  | Int.ofNat n => K n 0
  | Int.negSucc n => K 0 (n + 1)

/-- The sum-profile kernel remembers its one-variable profile exactly. -/
theorem po3_sum_kernel_injective :
    Function.Injective (po3_sum_kernel (A := A)) := by
  intro u v h
  funext t
  have ht := congrFun (congrFun h t) 0
  simpa [po3_sum_kernel] using ht

/-- Equality of sum-profile kernels is equivalent to equality of the profiles. -/
theorem po3_sum_kernel_eq_iff
    (u v : ℕ → A) :
    po3_sum_kernel u = po3_sum_kernel v ↔ u = v := by
  constructor
  · intro h
    exact po3_sum_kernel_injective h
  · intro h
    simp [h]

/-- A kernel equals a sum-profile exactly when it is constant on anti-diagonals. -/
theorem po3_eq_sum_kernel_iff_antidiagonal_invariant
    (K : ℕ → ℕ → A) :
    (∃ u, K = po3_sum_kernel u)
      ↔
    ∀ m n m' n', m + n = m' + n' → K m n = K m' n' := by
  constructor
  · rintro ⟨u, rfl⟩
    intro m n m' n' hsum
    simp [po3_sum_kernel, hsum]
  · intro hK
    refine ⟨po3_sum_profile_of_kernel K, ?_⟩
    funext m n
    have hmn : K m n = K (m + n) 0 := hK m n (m + n) 0 (by simp)
    simpa [po3_sum_kernel, po3_sum_profile_of_kernel] using hmn

/-- The first adjacent anti-diagonal defect for a `(+,-)` kernel. If this
quantity is nonzero at some level, the kernel cannot come from a one-variable
sum-profile. -/
def po3_antidiagonal_adjacent_defect (K : ℕ → ℕ → A) (t : ℕ) : A :=
  K (t + 1) 0 - K t 1

/-- A nonzero adjacent anti-diagonal defect rules out any one-variable
`(+,-)` profile. -/
theorem po3_no_sum_profile_of_adjacent_antidiagonal_defect_ne_zero
    (K : ℕ → ℕ → A) (t : ℕ)
    (hdef : po3_antidiagonal_adjacent_defect K t ≠ 0) :
    ¬ ∃ u, K = po3_sum_kernel u := by
  intro hsum
  rcases (po3_eq_sum_kernel_iff_antidiagonal_invariant (K := K)).1 hsum with hK
  have hEq : K (t + 1) 0 = K t 1 := hK (t + 1) 0 t 1 (by simp)
  have hzero : po3_antidiagonal_adjacent_defect K t = 0 := by
    simp [po3_antidiagonal_adjacent_defect, hEq]
  exact hdef hzero

/-- The difference-profile kernel also remembers its one-variable profile
exactly. -/
theorem po3_difference_kernel_injective :
    Function.Injective (po3_difference_kernel (A := A)) := by
  intro u v h
  funext k
  cases k with
  | ofNat n =>
      have hn := congrFun (congrFun h n) 0
      simpa [po3_difference_kernel] using hn
  | negSucc n =>
      have hn := congrFun (congrFun h 0) (n + 1)
      change u (-((n + 1 : ℤ))) = v (-((n + 1 : ℤ)))
      simpa [po3_difference_kernel] using hn

/-- Equality of difference-profile kernels is equivalent to equality of the
profiles. -/
theorem po3_difference_kernel_eq_iff
    (u v : ℤ → A) :
    po3_difference_kernel u = po3_difference_kernel v ↔ u = v := by
  constructor
  · intro h
    exact po3_difference_kernel_injective h
  · intro h
    simp [h]

/-- A kernel equals a difference-profile exactly when it is constant on level
sets of the index difference. -/
theorem po3_eq_difference_kernel_iff_difference_invariant
    (K : ℕ → ℕ → A) :
    (∃ u, K = po3_difference_kernel u)
      ↔
    ∀ m n m' n' : ℕ,
      ((m : ℤ) - (n : ℤ)) = ((m' : ℤ) - (n' : ℤ)) → K m n = K m' n' := by
  constructor
  · rintro ⟨u, rfl⟩
    intro m n m' n' hdiff
    simp [po3_difference_kernel, hdiff]
  · intro hK
    refine ⟨po3_difference_profile_of_kernel K, ?_⟩
    funext m n
    cases hmn : ((m : ℤ) - (n : ℤ)) with
    | ofNat t =>
        have hEq : ((m : ℤ) - (n : ℤ)) = (((t : ℕ) : ℤ) - (((0 : ℕ) : ℤ))) := by
          simpa [hmn]
        have hval : K m n = K t 0 := hK m n t 0 hEq
        simpa [po3_difference_kernel, po3_difference_profile_of_kernel, hmn] using hval
    | negSucc t =>
        have hEq : ((m : ℤ) - (n : ℤ)) = ((((0 : ℕ) : ℤ)) - (((t + 1 : ℕ) : ℤ))) := by
          rw [hmn]
          change Int.negSucc t = -(((t + 1 : ℕ) : ℤ))
          rfl
        have hval : K m n = K 0 (t + 1) := hK m n 0 (t + 1) hEq
        simpa [po3_difference_kernel, po3_difference_profile_of_kernel, hmn] using hval

/-- The filtered `(+,-)` profile is additive with respect to subtraction. -/
theorem po3_filtered_sum_profile_sub
    (u v : ℕ → A) :
    po3_filtered_sum_profile (fun t => u t - v t)
      =
        fun t => po3_filtered_sum_profile u t - po3_filtered_sum_profile v t := by
  funext t
  simp [po3_filtered_sum_profile]
  abel_nf

/-- The filtered `(+,+)` profile is additive with respect to subtraction. -/
theorem po3_filtered_difference_profile_sub
    (u v : ℤ → A) :
    po3_filtered_difference_profile (fun k => u k - v k)
      =
        fun k => po3_filtered_difference_profile u k - po3_filtered_difference_profile v k := by
  funext k
  simp [po3_filtered_difference_profile]
  abel_nf

/-- The raw signed difference packet restricts to the `(++ )` block as the
usual difference-profile kernel. -/
theorem po3_signed_difference_kernel_pp
    (u : ℤ → A) (m n : ℕ) :
    po3_signed_difference_kernel u (m : ℤ) (n : ℤ)
      =
        po3_difference_kernel u m n := by
  simp [po3_signed_difference_kernel, po3_difference_kernel]

/-- The raw signed difference packet restricts to the `(+,-)` block as the
corresponding sum-profile kernel. -/
theorem po3_signed_difference_kernel_pm
    (u : ℤ → A) (m n : ℕ) :
    po3_signed_difference_kernel u (m : ℤ) (-(n : ℤ))
      =
        po3_sum_kernel (po3_nat_profile_of_int u) m n := by
  simp [po3_signed_difference_kernel, po3_sum_kernel, po3_nat_profile_of_int,
    Nat.cast_add]

/-- Manuscript-facing raw `q^{++}` shell: if the signed raw packet is
`a_{r-s}-p_{r-s}`, then its `(++ )` block is exactly `po3_q_pp_kernel`. -/
theorem po3_signed_difference_kernel_sub_pp
    (a p : ℤ → A) (m n : ℕ) :
    po3_signed_difference_kernel (fun k => a k - p k) (m : ℤ) (n : ℤ)
      =
        po3_q_pp_kernel a p m n := by
  simp [po3_signed_difference_kernel, po3_q_pp_kernel, po3_difference_kernel]

/-- Manuscript-facing raw `q^{+-}` shell: if the signed raw packet is
`a_{r-s}-p_{r-s}`, then its `(+,-)` block is exactly the restricted
sum-profile kernel. -/
theorem po3_signed_difference_kernel_sub_pm
    (a p : ℤ → A) (m n : ℕ) :
    po3_signed_difference_kernel (fun k => a k - p k) (m : ℤ) (-(n : ℤ))
      =
        po3_q_pm_kernel_of_int a p m n := by
  simp [po3_signed_difference_kernel, po3_q_pm_kernel_of_int, po3_q_pm_kernel,
    po3_sum_kernel, po3_nat_profile_of_int, Nat.cast_add]

/-- Filtered four-term stencil preserves the sum-profile shape. -/
theorem po3_four_term_stencil_sum_kernel
    (u : ℕ → A) (m n : ℕ) :
    po3_four_term_stencil (po3_sum_kernel u) m n
      =
        u (m + n)
        + u (m + n + 1)
        + u (m + n + 1)
        + u (m + n + 2) := by
  simp [po3_four_term_stencil, po3_sum_kernel, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The filtered `(+,-)` block is again a sum-profile kernel, now with the
explicit filtered one-dimensional profile. -/
theorem po3_four_term_stencil_sum_kernel_as_sum_kernel
    (u : ℕ → A) :
    po3_four_term_stencil (po3_sum_kernel u)
      =
        po3_sum_kernel (po3_filtered_sum_profile u) := by
  funext m n
  simp [po3_sum_kernel, po3_filtered_sum_profile, po3_four_term_stencil,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Filtered four-term stencil preserves the difference-profile shape. -/
theorem po3_four_term_stencil_difference_kernel
    (u : ℤ → A) (m n : ℕ) :
    po3_four_term_stencil (po3_difference_kernel u) m n
      =
        u ((m : ℤ) - (n : ℤ))
        + u (((m : ℤ) - (n : ℤ)) + 1)
        + u (((m : ℤ) - (n : ℤ)) - 1)
        + u ((m : ℤ) - (n : ℤ)) := by
  have h1 : ((m : ℤ) + 1 - (n : ℤ)) = ((m : ℤ) - (n : ℤ)) + 1 := by ring
  have h2 : ((m : ℤ) - ((n : ℤ) + 1)) = ((m : ℤ) - (n : ℤ)) - 1 := by ring
  simp [po3_four_term_stencil, po3_difference_kernel, h1, h2]

/-- The filtered `(+,+)` block is again a difference-profile kernel, now with
the explicit filtered one-dimensional profile. -/
theorem po3_four_term_stencil_difference_kernel_as_difference_kernel
    (u : ℤ → A) :
    po3_four_term_stencil (po3_difference_kernel u)
      =
        po3_difference_kernel (po3_filtered_difference_profile u) := by
  funext m n
  rw [po3_four_term_stencil_difference_kernel]
  simp [po3_difference_kernel, po3_filtered_difference_profile]

/-- Direct Q-side shell for the filtered `(+,-)` block: if the raw packet is a
sum-profile difference `a - p`, then the filtered packet is the corresponding
filtered sum-profile difference. -/
theorem po3_four_term_stencil_sum_kernel_sub
    (a p : ℕ → A) :
    po3_four_term_stencil (po3_sum_kernel (fun t => a t - p t))
      =
        po3_sum_kernel (fun t => po3_filtered_sum_profile a t - po3_filtered_sum_profile p t) := by
  rw [po3_four_term_stencil_sum_kernel_as_sum_kernel]
  simp [po3_filtered_sum_profile_sub]

/-- Direct Q-side shell for the filtered `(+,+)` block: if the raw packet is a
difference-profile difference `a - p`, then the filtered packet is the
corresponding filtered difference-profile difference. -/
theorem po3_four_term_stencil_difference_kernel_sub
    (a p : ℤ → A) :
    po3_four_term_stencil (po3_difference_kernel (fun k => a k - p k))
      =
        po3_difference_kernel
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k) := by
  rw [po3_four_term_stencil_difference_kernel_as_difference_kernel]
  simp [po3_filtered_difference_profile_sub]

/-- Mixed packet of a sum-profile kernel is the one-dimensional second forward
difference on the sum variable. -/
theorem po3_mixed_packet_of_sum_kernel
    (u : ℕ → A) (r s : ℕ) :
    po3_mixed_packet (po3_sum_kernel u) r s
      =
        u (r + s + 2)
        - u (r + s + 1)
        - u (r + s + 1)
        + u (r + s) := by
  simp [po3_mixed_packet, po3_sum_kernel, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- A sum-profile mixed packet is exactly the one-dimensional forward second
difference evaluated at the sum variable. -/
theorem po3_mixed_packet_of_sum_kernel_as_forward_second_difference
    (u : ℕ → A) (r s : ℕ) :
    po3_mixed_packet (po3_sum_kernel u) r s
      =
        po3_forward_second_difference u (r + s) := by
  simp [po3_forward_second_difference, po3_mixed_packet_of_sum_kernel,
    Nat.add_assoc]

/-- Mixed packet of a difference-profile kernel is the one-dimensional centered
second difference on the difference variable. -/
theorem po3_mixed_packet_of_difference_kernel
    (u : ℤ → A) (r s : ℕ) :
    po3_mixed_packet (po3_difference_kernel u) r s
      =
        u ((r : ℤ) - (s : ℤ))
        - u (((r : ℤ) - (s : ℤ)) + 1)
        - u (((r : ℤ) - (s : ℤ)) - 1)
        + u ((r : ℤ) - (s : ℤ)) := by
  have h1 : (((r : ℤ) + 1) - (s : ℤ)) = ((r : ℤ) - (s : ℤ)) + 1 := by ring
  have h2 : ((r : ℤ) - ((s : ℤ) + 1)) = ((r : ℤ) - (s : ℤ)) - 1 := by ring
  have h3 : (((r : ℤ) + 1) - ((s : ℤ) + 1)) = ((r : ℤ) - (s : ℤ)) := by ring
  simp [po3_mixed_packet, po3_difference_kernel, h1, h2, h3]

/-- A difference-profile mixed packet is exactly the one-dimensional centered
second difference evaluated at the difference variable. -/
theorem po3_mixed_packet_of_difference_kernel_as_centered_second_difference
    (u : ℤ → A) (r s : ℕ) :
    po3_mixed_packet (po3_difference_kernel u) r s
      =
        po3_centered_second_difference u ((r : ℤ) - (s : ℤ)) := by
  simp [po3_centered_second_difference, po3_mixed_packet_of_difference_kernel]

/-- After the common four-term stencil, a sum-profile mixed packet becomes the
step-`2` second difference on the sum variable. -/
theorem po3_mixed_packet_of_four_term_stencil_sum_kernel
    (u : ℕ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_sum_kernel u)) r s
      =
        u (r + s + 4)
        - u (r + s + 2)
        - u (r + s + 2)
        + u (r + s) := by
  calc
    po3_mixed_packet (po3_four_term_stencil (po3_sum_kernel u)) r s
        =
          po3_four_term_stencil (po3_sum_kernel u) (r + 1) (s + 1)
          - po3_four_term_stencil (po3_sum_kernel u) (r + 1) s
          - po3_four_term_stencil (po3_sum_kernel u) r (s + 1)
          + po3_four_term_stencil (po3_sum_kernel u) r s := by
          simp [po3_mixed_packet, sub_eq_add_neg]
    _ =
          (u (r + s + 2) + u (r + s + 3) + u (r + s + 3) + u (r + s + 4))
          - (u (r + s + 1) + u (r + s + 2) + u (r + s + 2) + u (r + s + 3))
          - (u (r + s + 1) + u (r + s + 2) + u (r + s + 2) + u (r + s + 3))
          + (u (r + s) + u (r + s + 1) + u (r + s + 1) + u (r + s + 2)) := by
          simp [po3_four_term_stencil_sum_kernel, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = u (r + s + 4) - u (r + s + 2) - u (r + s + 2) + u (r + s) := by
          abel_nf

/-- After filtering, the `(+,-)` mixed packet is the forward second difference
of the filtered one-dimensional profile. -/
theorem po3_mixed_packet_of_four_term_stencil_sum_kernel_as_forward_second_difference
    (u : ℕ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_sum_kernel u)) r s
      =
        po3_forward_second_difference (po3_filtered_sum_profile u) (r + s) := by
  rw [po3_four_term_stencil_sum_kernel_as_sum_kernel]
  simpa using
    po3_mixed_packet_of_sum_kernel_as_forward_second_difference
      (u := po3_filtered_sum_profile u) (r := r) (s := s)

/-- After the common four-term stencil, a difference-profile mixed packet
becomes the step-`2` centered second difference on the difference variable. -/
theorem po3_mixed_packet_of_four_term_stencil_difference_kernel
    (u : ℤ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_difference_kernel u)) r s
      =
        u ((r : ℤ) - (s : ℤ))
        + u ((r : ℤ) - (s : ℤ))
        - u (((r : ℤ) - (s : ℤ)) + 2)
        - u (((r : ℤ) - (s : ℤ)) - 2) := by
  have h1 : (((r : ℤ) + 1) - ((s : ℤ) + 1)) = ((r : ℤ) - (s : ℤ)) := by ring
  have h2 : (((r : ℤ) + 1) - (s : ℤ)) = ((r : ℤ) - (s : ℤ)) + 1 := by ring
  have h3 : ((r : ℤ) - ((s : ℤ) + 1)) = ((r : ℤ) - (s : ℤ)) - 1 := by ring
  have h4 : (((r : ℤ) - (s : ℤ)) + 1 + 1) = ((r : ℤ) - (s : ℤ)) + 2 := by ring
  have h5 : (((r : ℤ) - (s : ℤ)) - 1 - 1) = ((r : ℤ) - (s : ℤ)) - 2 := by ring
  calc
    po3_mixed_packet (po3_four_term_stencil (po3_difference_kernel u)) r s
        =
          po3_four_term_stencil (po3_difference_kernel u) (r + 1) (s + 1)
          - po3_four_term_stencil (po3_difference_kernel u) (r + 1) s
          - po3_four_term_stencil (po3_difference_kernel u) r (s + 1)
          + po3_four_term_stencil (po3_difference_kernel u) r s := by
          simp [po3_mixed_packet, sub_eq_add_neg]
    _ =
          (u (((r : ℤ) - (s : ℤ))) + u (((r : ℤ) - (s : ℤ)) + 1)
            + u (((r : ℤ) - (s : ℤ)) - 1) + u (((r : ℤ) - (s : ℤ))))
          - (u (((r : ℤ) - (s : ℤ)) + 1) + u (((r : ℤ) - (s : ℤ)) + 2)
            + u (((r : ℤ) - (s : ℤ))) + u (((r : ℤ) - (s : ℤ)) + 1))
          - (u (((r : ℤ) - (s : ℤ)) - 1) + u (((r : ℤ) - (s : ℤ)))
            + u (((r : ℤ) - (s : ℤ)) - 2) + u (((r : ℤ) - (s : ℤ)) - 1))
          + (u (((r : ℤ) - (s : ℤ))) + u (((r : ℤ) - (s : ℤ)) + 1)
            + u (((r : ℤ) - (s : ℤ)) - 1) + u (((r : ℤ) - (s : ℤ)))) := by
          simp [po3_four_term_stencil_difference_kernel, h1, h2, h3, h4, h5]
    _ =
          u ((r : ℤ) - (s : ℤ))
          + u ((r : ℤ) - (s : ℤ))
          - u (((r : ℤ) - (s : ℤ)) + 2)
          - u (((r : ℤ) - (s : ℤ)) - 2) := by
          abel_nf

/-- After filtering, the `(+,+)` mixed packet is the centered second
difference of the filtered one-dimensional profile. -/
theorem po3_mixed_packet_of_four_term_stencil_difference_kernel_as_centered_second_difference
    (u : ℤ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_difference_kernel u)) r s
      =
        po3_centered_second_difference (po3_filtered_difference_profile u)
          ((r : ℤ) - (s : ℤ)) := by
  rw [po3_four_term_stencil_difference_kernel_as_difference_kernel]
  simpa using
    po3_mixed_packet_of_difference_kernel_as_centered_second_difference
      (u := po3_filtered_difference_profile u) (r := r) (s := s)

/-- Direct filtered `(+,-)` shell for a raw profile difference `a - p`. -/
theorem po3_mixed_packet_of_four_term_stencil_sum_kernel_sub_as_forward_second_difference
    (a p : ℕ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_sum_kernel (fun t => a t - p t))) r s
      =
        po3_forward_second_difference
          (fun t => po3_filtered_sum_profile a t - po3_filtered_sum_profile p t) (r + s) := by
  rw [po3_four_term_stencil_sum_kernel_sub]
  simpa using
    po3_mixed_packet_of_sum_kernel_as_forward_second_difference
      (u := fun t => po3_filtered_sum_profile a t - po3_filtered_sum_profile p t)
      (r := r) (s := s)

/-- Direct filtered `(+,+)` shell for a raw profile difference `a - p`. -/
theorem po3_mixed_packet_of_four_term_stencil_difference_kernel_sub_as_centered_second_difference
    (a p : ℤ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_difference_kernel (fun k => a k - p k))) r s
      =
        po3_centered_second_difference
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k)
          ((r : ℤ) - (s : ℤ)) := by
  rw [po3_four_term_stencil_difference_kernel_sub]
  simpa using
    po3_mixed_packet_of_difference_kernel_as_centered_second_difference
      (u := fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k)
      (r := r) (s := s)

/-- Manuscript-facing shell: the filtered `q^{+-}` block remains a sum-profile
with filtered one-dimensional packet. -/
theorem po3_four_term_stencil_q_pm_kernel
    (a p : ℕ → A) :
    po3_four_term_stencil (po3_q_pm_kernel a p)
      =
        po3_sum_kernel
          (fun t => po3_filtered_sum_profile a t - po3_filtered_sum_profile p t) := by
  simpa [po3_q_pm_kernel] using po3_four_term_stencil_sum_kernel_sub (a := a) (p := p)

/-- Manuscript-facing shell: the filtered `q^{++}` block remains a
difference-profile with filtered one-dimensional packet. -/
theorem po3_four_term_stencil_q_pp_kernel
    (a p : ℤ → A) :
    po3_four_term_stencil (po3_q_pp_kernel a p)
      =
        po3_difference_kernel
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k) := by
  simpa [po3_q_pp_kernel] using
    po3_four_term_stencil_difference_kernel_sub (a := a) (p := p)

/-- Manuscript-facing shell: the filtered `q^{+-}` mixed packet is the forward
second difference of the filtered one-dimensional packet. -/
theorem po3_mixed_packet_of_four_term_stencil_q_pm_kernel
    (a p : ℕ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_q_pm_kernel a p)) r s
      =
        po3_forward_second_difference
          (fun t => po3_filtered_sum_profile a t - po3_filtered_sum_profile p t) (r + s) := by
  simpa [po3_q_pm_kernel] using
    po3_mixed_packet_of_four_term_stencil_sum_kernel_sub_as_forward_second_difference
      (a := a) (p := p) (r := r) (s := s)

/-- Manuscript-facing shell: the filtered `q^{++}` mixed packet is the centered
second difference of the filtered one-dimensional packet. -/
theorem po3_mixed_packet_of_four_term_stencil_q_pp_kernel
    (a p : ℤ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_q_pp_kernel a p)) r s
      =
        po3_centered_second_difference
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k)
          ((r : ℤ) - (s : ℤ)) := by
  simpa [po3_q_pp_kernel] using
    po3_mixed_packet_of_four_term_stencil_difference_kernel_sub_as_centered_second_difference
      (a := a) (p := p) (r := r) (s := s)

/-- Integer-profile version of the filtered `q^{+-}` shell. -/
theorem po3_four_term_stencil_q_pm_kernel_of_int
    (a p : ℤ → A) :
    po3_four_term_stencil (po3_q_pm_kernel_of_int a p)
      =
        po3_sum_kernel
          (fun t =>
            po3_filtered_sum_profile (po3_nat_profile_of_int a) t
              - po3_filtered_sum_profile (po3_nat_profile_of_int p) t) := by
  simpa [po3_q_pm_kernel_of_int] using
    po3_four_term_stencil_q_pm_kernel
      (a := po3_nat_profile_of_int a) (p := po3_nat_profile_of_int p)

/-- Integer-profile version of the filtered `q^{+-}` mixed-packet shell. -/
theorem po3_mixed_packet_of_four_term_stencil_q_pm_kernel_of_int
    (a p : ℤ → A) (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (po3_q_pm_kernel_of_int a p)) r s
      =
        po3_forward_second_difference
          (fun t =>
            po3_filtered_sum_profile (po3_nat_profile_of_int a) t
              - po3_filtered_sum_profile (po3_nat_profile_of_int p) t) (r + s) := by
  simpa [po3_q_pm_kernel_of_int] using
    po3_mixed_packet_of_four_term_stencil_q_pm_kernel
      (a := po3_nat_profile_of_int a) (p := po3_nat_profile_of_int p) (r := r) (s := s)

/-- If a raw Section 8 packet is given by the signed difference formula
`q_{rs}=a_{r-s}-p_{r-s}`, then its filtered `(++ )` block is exactly the
already packaged `q^{++}` kernel. -/
theorem po3_four_term_stencil_of_raw_q_pp_formula
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = po3_signed_difference_kernel (fun k => a k - p k) r s) :
    po3_four_term_stencil (fun m n => q (m : ℤ) (n : ℤ))
      =
        po3_difference_kernel
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k) := by
  have hpp : (fun m n : ℕ => q (m : ℤ) (n : ℤ)) = po3_q_pp_kernel a p := by
    funext m n
    rw [hq]
    exact po3_signed_difference_kernel_sub_pp (a := a) (p := p) (m := m) (n := n)
  rw [hpp]
  exact po3_four_term_stencil_q_pp_kernel (a := a) (p := p)

/-- If a raw Section 8 packet is given by the signed difference formula
`q_{rs}=a_{r-s}-p_{r-s}`, then its filtered `(+,-)` block is exactly the
already packaged `q^{+-}` kernel. -/
theorem po3_four_term_stencil_of_raw_q_pm_formula
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = po3_signed_difference_kernel (fun k => a k - p k) r s) :
    po3_four_term_stencil (fun m n => q (m : ℤ) (-(n : ℤ)))
      =
        po3_sum_kernel
          (fun t =>
            po3_filtered_sum_profile (po3_nat_profile_of_int a) t
              - po3_filtered_sum_profile (po3_nat_profile_of_int p) t) := by
  have hpm : (fun m n : ℕ => q (m : ℤ) (-(n : ℤ))) = po3_q_pm_kernel_of_int a p := by
    funext m n
    rw [hq]
    exact po3_signed_difference_kernel_sub_pm (a := a) (p := p) (m := m) (n := n)
  rw [hpm]
  exact po3_four_term_stencil_q_pm_kernel_of_int (a := a) (p := p)

/-- Mixed-packet bridge for the filtered raw `(++ )` Section 8 family. -/
theorem po3_mixed_packet_of_raw_q_pp_formula
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = po3_signed_difference_kernel (fun k => a k - p k) r s)
    (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (fun m n => q (m : ℤ) (n : ℤ))) r s
      =
        po3_centered_second_difference
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k)
          ((r : ℤ) - (s : ℤ)) := by
  rw [po3_four_term_stencil_of_raw_q_pp_formula (q := q) (a := a) (p := p) hq]
  exact po3_mixed_packet_of_difference_kernel_as_centered_second_difference
    (u := fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k)
    (r := r) (s := s)

/-- Mixed-packet bridge for the filtered raw `(+,-)` Section 8 family. -/
theorem po3_mixed_packet_of_raw_q_pm_formula
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = po3_signed_difference_kernel (fun k => a k - p k) r s)
    (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (fun m n => q (m : ℤ) (-(n : ℤ)))) r s
      =
        po3_forward_second_difference
          (fun t =>
            po3_filtered_sum_profile (po3_nat_profile_of_int a) t
              - po3_filtered_sum_profile (po3_nat_profile_of_int p) t) (r + s) := by
  rw [po3_four_term_stencil_of_raw_q_pm_formula (q := q) (a := a) (p := p) hq]
  exact po3_mixed_packet_of_sum_kernel_as_forward_second_difference
    (u := fun t =>
      po3_filtered_sum_profile (po3_nat_profile_of_int a) t
        - po3_filtered_sum_profile (po3_nat_profile_of_int p) t)
    (r := r) (s := s)

/-- Manuscript-entry rewrite: a raw formula of the form
`q_{rs}=a(r-s)-p(r-s)` is exactly the signed difference kernel shell used by
the Q-side bridge. -/
theorem po3_raw_q_difference_formula_as_signed_difference_kernel
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = a (r - s) - p (r - s)) :
    ∀ r s, q r s = po3_signed_difference_kernel (fun k => a k - p k) r s := by
  intro r s
  rw [hq r s]
  simp [po3_signed_difference_kernel]

/-- Direct manuscript-facing filtered `(++ )` shell from
`q_{rs}=a(r-s)-p(r-s)`. -/
theorem po3_four_term_stencil_of_raw_q_difference_formula_pp
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = a (r - s) - p (r - s)) :
    po3_four_term_stencil (fun m n => q (m : ℤ) (n : ℤ))
      =
        po3_difference_kernel
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k) := by
  exact po3_four_term_stencil_of_raw_q_pp_formula
    (q := q) (a := a) (p := p)
    (hq := po3_raw_q_difference_formula_as_signed_difference_kernel
      (q := q) (a := a) (p := p) hq)

/-- Direct manuscript-facing filtered `(+,-)` shell from
`q_{rs}=a(r-s)-p(r-s)`. -/
theorem po3_four_term_stencil_of_raw_q_difference_formula_pm
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = a (r - s) - p (r - s)) :
    po3_four_term_stencil (fun m n => q (m : ℤ) (-(n : ℤ)))
      =
        po3_sum_kernel
          (fun t =>
            po3_filtered_sum_profile (po3_nat_profile_of_int a) t
              - po3_filtered_sum_profile (po3_nat_profile_of_int p) t) := by
  exact po3_four_term_stencil_of_raw_q_pm_formula
    (q := q) (a := a) (p := p)
    (hq := po3_raw_q_difference_formula_as_signed_difference_kernel
      (q := q) (a := a) (p := p) hq)

/-- Direct manuscript-facing filtered mixed packet for the `(++ )` family from
`q_{rs}=a(r-s)-p(r-s)`. -/
theorem po3_mixed_packet_of_raw_q_difference_formula_pp
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = a (r - s) - p (r - s))
    (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (fun m n => q (m : ℤ) (n : ℤ))) r s
      =
        po3_centered_second_difference
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k)
          ((r : ℤ) - (s : ℤ)) := by
  exact po3_mixed_packet_of_raw_q_pp_formula
    (q := q) (a := a) (p := p)
    (hq := po3_raw_q_difference_formula_as_signed_difference_kernel
      (q := q) (a := a) (p := p) hq)
    (r := r) (s := s)

/-- Direct manuscript-facing filtered mixed packet for the `(+,-)` family from
`q_{rs}=a(r-s)-p(r-s)`. -/
theorem po3_mixed_packet_of_raw_q_difference_formula_pm
    (q : ℤ → ℤ → A) (a p : ℤ → A)
    (hq : ∀ r s, q r s = a (r - s) - p (r - s))
    (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (fun m n => q (m : ℤ) (-(n : ℤ)))) r s
      =
        po3_forward_second_difference
          (fun t =>
            po3_filtered_sum_profile (po3_nat_profile_of_int a) t
              - po3_filtered_sum_profile (po3_nat_profile_of_int p) t) (r + s) := by
  exact po3_mixed_packet_of_raw_q_pm_formula
    (q := q) (a := a) (p := p)
    (hq := po3_raw_q_difference_formula_as_signed_difference_kernel
      (q := q) (a := a) (p := p) hq)
    (r := r) (s := s)

/-- Raw Section 8 split written in manuscript form: if both pieces depend only
on the difference and `q = arch - prime`, then `q` itself has the one-variable
difference formula. -/
theorem po3_raw_q_difference_formula_of_split
    (arch prime q : ℤ → ℤ → A) (a p : ℤ → A)
    (harch : ∀ r s, arch r s = a (r - s))
    (hprime : ∀ r s, prime r s = p (r - s))
    (hq : ∀ r s, q r s = arch r s - prime r s) :
    ∀ r s, q r s = a (r - s) - p (r - s) := by
  intro r s
  rw [hq r s, harch r s, hprime r s]

/-- Filtered `(++ )` consequence of the manuscript raw split
`q = arch - prime`, once both pieces factor through `r-s`. -/
theorem po3_four_term_stencil_of_raw_q_split_formula_pp
    (arch prime q : ℤ → ℤ → A) (a p : ℤ → A)
    (harch : ∀ r s, arch r s = a (r - s))
    (hprime : ∀ r s, prime r s = p (r - s))
    (hq : ∀ r s, q r s = arch r s - prime r s) :
    po3_four_term_stencil (fun m n => q (m : ℤ) (n : ℤ))
      =
        po3_difference_kernel
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k) := by
  exact po3_four_term_stencil_of_raw_q_difference_formula_pp
    (q := q) (a := a) (p := p)
    (hq := po3_raw_q_difference_formula_of_split
      (arch := arch) (prime := prime) (q := q) (a := a) (p := p) harch hprime hq)

/-- Filtered `(+,-)` consequence of the manuscript raw split
`q = arch - prime`, once both pieces factor through `r-s`. -/
theorem po3_four_term_stencil_of_raw_q_split_formula_pm
    (arch prime q : ℤ → ℤ → A) (a p : ℤ → A)
    (harch : ∀ r s, arch r s = a (r - s))
    (hprime : ∀ r s, prime r s = p (r - s))
    (hq : ∀ r s, q r s = arch r s - prime r s) :
    po3_four_term_stencil (fun m n => q (m : ℤ) (-(n : ℤ)))
      =
        po3_sum_kernel
          (fun t =>
            po3_filtered_sum_profile (po3_nat_profile_of_int a) t
              - po3_filtered_sum_profile (po3_nat_profile_of_int p) t) := by
  exact po3_four_term_stencil_of_raw_q_difference_formula_pm
    (q := q) (a := a) (p := p)
    (hq := po3_raw_q_difference_formula_of_split
      (arch := arch) (prime := prime) (q := q) (a := a) (p := p) harch hprime hq)

/-- Filtered mixed packet of the raw `(++ )` family obtained from the split
`q = arch - prime`. -/
theorem po3_mixed_packet_of_raw_q_split_formula_pp
    (arch prime q : ℤ → ℤ → A) (a p : ℤ → A)
    (harch : ∀ r s, arch r s = a (r - s))
    (hprime : ∀ r s, prime r s = p (r - s))
    (hq : ∀ r s, q r s = arch r s - prime r s)
    (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (fun m n => q (m : ℤ) (n : ℤ))) r s
      =
        po3_centered_second_difference
          (fun k => po3_filtered_difference_profile a k - po3_filtered_difference_profile p k)
          ((r : ℤ) - (s : ℤ)) := by
  exact po3_mixed_packet_of_raw_q_difference_formula_pp
    (q := q) (a := a) (p := p)
    (hq := po3_raw_q_difference_formula_of_split
      (arch := arch) (prime := prime) (q := q) (a := a) (p := p) harch hprime hq)
    (r := r) (s := s)

/-- Filtered mixed packet of the raw `(+,-)` family obtained from the split
`q = arch - prime`. -/
theorem po3_mixed_packet_of_raw_q_split_formula_pm
    (arch prime q : ℤ → ℤ → A) (a p : ℤ → A)
    (harch : ∀ r s, arch r s = a (r - s))
    (hprime : ∀ r s, prime r s = p (r - s))
    (hq : ∀ r s, q r s = arch r s - prime r s)
    (r s : ℕ) :
    po3_mixed_packet (po3_four_term_stencil (fun m n => q (m : ℤ) (-(n : ℤ)))) r s
      =
        po3_forward_second_difference
          (fun t =>
            po3_filtered_sum_profile (po3_nat_profile_of_int a) t
              - po3_filtered_sum_profile (po3_nat_profile_of_int p) t) (r + s) := by
  exact po3_mixed_packet_of_raw_q_difference_formula_pm
    (q := q) (a := a) (p := p)
    (hq := po3_raw_q_difference_formula_of_split
      (arch := arch) (prime := prime) (q := q) (a := a) (p := p) harch hprime hq)
    (r := r) (s := s)

end PO3OneDimensionalProfiles

section PO3Section8Profiles

open MeasureTheory

/-- Common Fourier phase used in the raw Section 8 coefficient formulas. -/
noncomputable def po3_section8_phase (k : ℤ) (ξ : ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ))

/-- The one-variable archimedean profile from the raw Section 8 formula. -/
noncomputable def po3_section8_arch_profile (B t : ℝ) (k : ℤ) : ℂ :=
  ∫ ξ, (((Q3.a_star ξ) * Q3.fejer_heat_window B t ξ : ℝ) : ℂ) * po3_section8_phase k ξ

/-- The one-variable prime profile from the raw Section 8 formula. -/
noncomputable def po3_section8_prime_profile (B t : ℝ) (k : ℤ) : ℂ :=
  ∑' n : ℕ,
    (((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℝ) : ℂ) *
      po3_section8_phase k (Q3.xi_n n)

/-- The one-variable raw Section 8 profile `a_k - p_k`. -/
noncomputable def po3_section8_raw_profile (B t : ℝ) (k : ℤ) : ℂ :=
  po3_section8_arch_profile B t k - po3_section8_prime_profile B t k

/-- The raw archimedean kernel depends only on the index difference. -/
noncomputable def po3_section8_arch_kernel (B t : ℝ) : ℤ → ℤ → ℂ :=
  po3_signed_difference_kernel (po3_section8_arch_profile B t)

/-- The raw prime kernel depends only on the index difference. -/
noncomputable def po3_section8_prime_kernel (B t : ℝ) : ℤ → ℤ → ℂ :=
  po3_signed_difference_kernel (po3_section8_prime_profile B t)

/-- The raw Section 8 kernel is the signed difference packet attached to the
profile `a_k - p_k`. -/
noncomputable def po3_section8_raw_kernel (B t : ℝ) : ℤ → ℤ → ℂ :=
  po3_signed_difference_kernel (po3_section8_raw_profile B t)

/-- Candidate shape for a Suzuki `(+,-)` filtered block once it is shown to
depend only on the sum variable. -/
def po3_suzuki_filtered_pm_candidate (u : ℕ → ℂ) : ℕ → ℕ → ℂ :=
  po3_sum_kernel u

/-- Candidate shape for a Suzuki `(++ )` filtered block once it is shown to
depend only on the difference variable. -/
def po3_suzuki_filtered_pp_candidate (u : ℤ → ℂ) : ℕ → ℕ → ℂ :=
  po3_difference_kernel u

/-- A single manuscript-style `(+,-)` Suzuki atom:
the parity factor already depends only on `m+n`, while the denominator carries
the genuine two-variable geometry. -/
noncomputable def po3_suzuki_filtered_pm_atom
    (α : ℕ → ℂ) (γ : ℂ) : ℕ → ℕ → ℂ :=
  fun m n =>
    ((-1 : ℂ) ^ (m + n)) /
      (((γ - α m) * (γ - α (m + 1))) * ((γ - α n) * (γ - α (n + 1))))

/-- Finite packet model for the manuscript `(+,-)` Suzuki block. The global
prefactor and the `\sin^2(a\gamma)` weight can be absorbed into `weight`. -/
noncomputable def po3_suzuki_filtered_pm_finset
    {ι : Type*} (S : Finset ι) (weight : ι → ℂ) (γ : ι → ℂ) (α : ℕ → ℂ) :
    ℕ → ℕ → ℂ :=
  fun m n => Finset.sum S (fun i => weight i * po3_suzuki_filtered_pm_atom α (γ i) m n)

/-- The natural affine pole lattice `α_n = n c`. This is the literal pattern
from the manuscript, with `c = π / a`. -/
noncomputable def po3_affine_alpha (c : ℂ) : ℕ → ℂ :=
  fun n => (n : ℂ) * c

/-- The adjacent anti-diagonal defect of a finite Suzuki packet is the sum of
the atom-wise defects. -/
theorem po3_suzuki_filtered_pm_finset_adjacent_defect
    {ι : Type*} (S : Finset ι) (weight : ι → ℂ) (γ : ι → ℂ) (α : ℕ → ℂ)
    (t : ℕ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_filtered_pm_finset S weight γ α) t
      =
        Finset.sum S (fun i =>
          weight i * po3_antidiagonal_adjacent_defect
            (po3_suzuki_filtered_pm_atom α (γ i)) t) := by
  classical
  unfold po3_antidiagonal_adjacent_defect po3_suzuki_filtered_pm_finset
  rw [← Finset.sum_sub_distrib]
  congr with i
  ring

/-- The first nontrivial anti-diagonal gap for a single manuscript-style
`(+,-)` Suzuki atom on the affine pole lattice `α_n = n c`, comparing the
points `(2,0)` and `(1,1)`. -/
theorem po3_suzuki_filtered_pm_atom_antidiagonal_gap_20_11
    (c γ : ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_filtered_pm_atom (po3_affine_alpha c) γ) 1
      =
        1 / (((γ - 2 * c) * (γ - 3 * c)) * (γ * (γ - c))) -
          1 / (((γ - c) * (γ - 2 * c)) * ((γ - c) * (γ - 2 * c))) := by
  simp [po3_antidiagonal_adjacent_defect, po3_suzuki_filtered_pm_atom,
    po3_affine_alpha]

/-- The neighboring anti-diagonal defect contributed by one affine-lattice
Suzuki atom in the `(2,0)` vs `(1,1)` test. -/
noncomputable def po3_suzuki_filtered_pm_gap_term_20_11
    (c γ : ℂ) : ℂ :=
  1 / (((γ - 2 * c) * (γ - 3 * c)) * (γ * (γ - c))) -
    1 / (((γ - c) * (γ - 2 * c)) * ((γ - c) * (γ - 2 * c)))

/-- The six-pole gap term is genuinely nonzero away from the first affine
pole locations. -/
theorem po3_suzuki_filtered_pm_gap_term_20_11_ne_zero
    (c γ : ℂ)
    (hc : c ≠ 0)
    (hγ0 : γ ≠ 0)
    (hγ1 : γ ≠ c)
    (hγ2 : γ ≠ 2 * c)
    (hγ3 : γ ≠ 3 * c) :
    po3_suzuki_filtered_pm_gap_term_20_11 c γ ≠ 0 := by
  intro hgap
  let A : ℂ := (((γ - 2 * c) * (γ - 3 * c)) * (γ * (γ - c)))
  let B : ℂ := (((γ - c) * (γ - 2 * c)) * ((γ - c) * (γ - 2 * c)))
  have hdiv : 1 / A = 1 / B := by
    have := sub_eq_zero.mp hgap
    simpa [po3_suzuki_filtered_pm_gap_term_20_11, A, B] using this
  have hA0 : A ≠ 0 := by
    dsimp [A]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact sub_ne_zero.mpr hγ2
      · exact sub_ne_zero.mpr hγ3
    · apply mul_ne_zero
      · exact hγ0
      · exact sub_ne_zero.mpr hγ1
  have hB0 : B ≠ 0 := by
    dsimp [B]
    apply mul_ne_zero <;> apply mul_ne_zero
    · exact sub_ne_zero.mpr hγ1
    · exact sub_ne_zero.mpr hγ2
    · exact sub_ne_zero.mpr hγ1
    · exact sub_ne_zero.mpr hγ2
  field_simp [A, B, hA0, hB0] at hdiv
  dsimp [A, B] at hdiv
  have hsub :
      (((γ - c) * (γ - 2 * c)) * ((γ - c) * (γ - 2 * c)))
        - (((γ - 2 * c) * (γ - 3 * c)) * (γ * (γ - c))) = 0 := by
    exact sub_eq_zero.mpr hdiv
  have hfactor :
      (((γ - c) * (γ - 2 * c)) * ((γ - c) * (γ - 2 * c)))
        - (((γ - 2 * c) * (γ - 3 * c)) * (γ * (γ - c)))
          =
        2 * c ^ 2 * (γ - c) * (γ - 2 * c) := by
    ring
  rw [hfactor] at hsub
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hgc : (γ - c) * (γ - 2 * c) ≠ 0 := by
    exact mul_ne_zero (sub_ne_zero.mpr hγ1) (sub_ne_zero.mpr hγ2)
  have hmain : 2 * c ^ 2 * ((γ - c) * (γ - 2 * c)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hc2) hgc
  have hmain' : 2 * c ^ 2 * (γ - c) * (γ - 2 * c) ≠ 0 := by
    simpa [mul_assoc] using hmain
  exact hmain' hsub

/-- A single affine-lattice Suzuki atom cannot be a one-variable `(+,-)`
profile once the first anti-diagonal gap is genuinely nonzero. -/
theorem po3_no_suzuki_filtered_pm_atom_candidate_of_affine_gap_20_11
    (c γ : ℂ)
    (hc : c ≠ 0)
    (hγ0 : γ ≠ 0)
    (hγ1 : γ ≠ c)
    (hγ2 : γ ≠ 2 * c)
    (hγ3 : γ ≠ 3 * c) :
    ¬ ∃ u,
      po3_suzuki_filtered_pm_atom (po3_affine_alpha c) γ
        = po3_suzuki_filtered_pm_candidate u := by
  apply po3_no_sum_profile_of_adjacent_antidiagonal_defect_ne_zero
  rw [po3_suzuki_filtered_pm_atom_antidiagonal_gap_20_11]
  exact po3_suzuki_filtered_pm_gap_term_20_11_ne_zero c γ hc hγ0 hγ1 hγ2 hγ3

/-- The first anti-diagonal gap for a finite Suzuki `(+,-)` packet on the
affine pole lattice is the sum of the atom-wise gaps. This is the exact finite
`γ`-sum form of the neighboring anti-diagonal defect. -/
theorem po3_suzuki_filtered_pm_finset_antidiagonal_gap_20_11
    {ι : Type*} (S : Finset ι) (weight : ι → ℂ) (γ : ι → ℂ) (c : ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_filtered_pm_finset S weight γ (po3_affine_alpha c)) 1
      =
        Finset.sum S (fun i =>
          weight i * po3_suzuki_filtered_pm_gap_term_20_11 c (γ i)) := by
  rw [po3_suzuki_filtered_pm_finset_adjacent_defect]
  congr with i
  rw [po3_suzuki_filtered_pm_atom_antidiagonal_gap_20_11]
  simp [po3_suzuki_filtered_pm_gap_term_20_11]

/-- If the first anti-diagonal gap of a finite affine-lattice Suzuki packet is
already nonzero, then the packet cannot come from a one-variable `(+,-)`
profile. -/
theorem po3_no_suzuki_filtered_pm_finset_candidate_of_affine_gap_20_11
    {ι : Type*} (S : Finset ι) (weight : ι → ℂ) (γ : ι → ℂ) (c : ℂ)
    (hgap :
      Finset.sum S (fun i =>
        weight i * po3_suzuki_filtered_pm_gap_term_20_11 c (γ i)) ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_filtered_pm_finset S weight γ (po3_affine_alpha c)
        = po3_suzuki_filtered_pm_candidate u := by
  apply po3_no_sum_profile_of_adjacent_antidiagonal_defect_ne_zero
  rw [po3_suzuki_filtered_pm_finset_antidiagonal_gap_20_11]
  exact hgap

/-- Manuscript-shaped finite partial `γ`-sum for the Suzuki `(+,-)` block:
the global prefactor is `κ`, the oscillatory factor is absorbed into
`amp`, and the poles sit on the affine lattice `α_n = n c`. -/
noncomputable def po3_suzuki_filtered_pm_partial_sum
    {ι : Type*} (S : Finset ι) (κ : ℂ) (amp : ι → ℂ) (γ : ι → ℂ) (c : ℂ) :
    ℕ → ℕ → ℂ :=
  po3_suzuki_filtered_pm_finset S (fun i => κ * amp i) γ (po3_affine_alpha c)

/-- The global prefactor from the manuscript formula
`2 π^2 / a^3`. -/
noncomputable def po3_suzuki_manuscript_prefactor (a : ℂ) : ℂ :=
  2 * ((Real.pi : ℂ) ^ 2) / (a ^ 3)

/-- The affine step in the manuscript pole lattice `α_n = π n / a`. -/
noncomputable def po3_suzuki_manuscript_alpha_step (a : ℂ) : ℂ :=
  (Real.pi : ℂ) / a

/-- The oscillatory manuscript amplitude `sin^2(aγ)`. -/
noncomputable def po3_suzuki_manuscript_amp (a γ : ℂ) : ℂ :=
  Complex.sin (a * γ) ^ 2

/-- Direct finite manuscript partial `γ`-sum for the Suzuki `(+,-)` block. -/
noncomputable def po3_suzuki_filtered_pm_partial_sum_manuscript
    {ι : Type*} (S : Finset ι) (a : ℂ) (γ : ι → ℂ) :
    ℕ → ℕ → ℂ :=
  po3_suzuki_filtered_pm_partial_sum
    S
    (po3_suzuki_manuscript_prefactor a)
    (fun i => po3_suzuki_manuscript_amp a (γ i))
    γ
    (po3_suzuki_manuscript_alpha_step a)

/-- The direct raw manuscript finite `γ`-sum for the filtered `(+,-)` block,
written with the global prefactor outside the sum exactly as in the tex
formula for `M^{+-}`. -/
noncomputable def po3_suzuki_raw_gamma_pm_finset
    {ι : Type*} (S : Finset ι) (a : ℂ) (γ : ι → ℂ) :
    ℕ → ℕ → ℂ :=
  fun m n =>
    (po3_suzuki_manuscript_prefactor a * ((-1 : ℂ) ^ (m + n))) *
      Finset.sum S (fun i =>
        po3_suzuki_manuscript_amp a (γ i) /
          (((γ i - po3_affine_alpha (po3_suzuki_manuscript_alpha_step a) m) *
              (γ i - po3_affine_alpha (po3_suzuki_manuscript_alpha_step a) (m + 1))) *
            ((γ i - po3_affine_alpha (po3_suzuki_manuscript_alpha_step a) n) *
              (γ i - po3_affine_alpha (po3_suzuki_manuscript_alpha_step a) (n + 1)))))

/-- The direct raw manuscript finite `γ`-sum is judgmentally the same object as
the packaged manuscript partial sum already living in the Suzuki shell. -/
theorem po3_suzuki_raw_gamma_pm_finset_eq_partial_sum_manuscript
    {ι : Type*} (S : Finset ι) (a : ℂ) (γ : ι → ℂ) :
    po3_suzuki_raw_gamma_pm_finset S a γ
      = po3_suzuki_filtered_pm_partial_sum_manuscript S a γ := by
  funext m n
  simp [po3_suzuki_raw_gamma_pm_finset,
    po3_suzuki_filtered_pm_partial_sum_manuscript,
    po3_suzuki_filtered_pm_partial_sum, po3_suzuki_filtered_pm_finset,
    po3_suzuki_filtered_pm_atom, po3_affine_alpha,
    div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The direct manuscript singleton truncation. This is the first concrete
finite `γ`-packet with no remaining indexing overhead. -/
noncomputable def po3_suzuki_filtered_pm_singleton_manuscript
    (a γ : ℂ) : ℕ → ℕ → ℂ :=
  po3_suzuki_filtered_pm_partial_sum_manuscript ({()} : Finset Unit) a (fun _ => γ)

/-- The direct raw manuscript singleton truncation, written exactly as one
term of the raw `γ`-sum for `M^{+-}`. -/
noncomputable def po3_suzuki_raw_gamma_pm_singleton
    (a γ : ℂ) : ℕ → ℕ → ℂ :=
  po3_suzuki_raw_gamma_pm_finset ({()} : Finset Unit) a (fun _ => γ)

/-- The direct raw manuscript prefix truncation on the first `K` `γ`-modes.
This is the most convenient shell for plugging in a concrete enumeration of
zeros from the manuscript side. -/
noncomputable def po3_suzuki_raw_gamma_pm_prefix
    (K : ℕ) (a : ℂ) (γ : ℕ → ℂ) : ℕ → ℕ → ℂ :=
  po3_suzuki_raw_gamma_pm_finset (Finset.range K) a γ

/-- Explicit two-term `γ`-prefix. Outside the first two slots the sequence is
filled with `0`; this never matters once we truncate at `K = 2`. -/
def po3_gamma_prefix2 (γ0 γ1 : ℂ) : ℕ → ℂ
  | 0 => γ0
  | 1 => γ1
  | _ => 0

/-- Explicit three-term `γ`-prefix. Outside the first three slots the sequence
is filled with `0`; this never matters once we truncate at `K = 3`. -/
def po3_gamma_prefix3 (γ0 γ1 γ2 : ℂ) : ℕ → ℂ
  | 0 => γ0
  | 1 => γ1
  | 2 => γ2
  | _ => 0

/-- Explicit `K = 2` raw manuscript truncation. -/
noncomputable def po3_suzuki_raw_gamma_pm_prefix2
    (a γ0 γ1 : ℂ) : ℕ → ℕ → ℂ :=
  po3_suzuki_raw_gamma_pm_prefix 2 a (po3_gamma_prefix2 γ0 γ1)

/-- Explicit `K = 3` raw manuscript truncation. -/
noncomputable def po3_suzuki_raw_gamma_pm_prefix3
    (a γ0 γ1 γ2 : ℂ) : ℕ → ℕ → ℂ :=
  po3_suzuki_raw_gamma_pm_prefix 3 a (po3_gamma_prefix3 γ0 γ1 γ2)

/-- The packaged manuscript prefix truncation on the first `K` `γ`-modes. -/
noncomputable def po3_suzuki_filtered_pm_prefix_manuscript
    (K : ℕ) (a : ℂ) (γ : ℕ → ℂ) : ℕ → ℕ → ℂ :=
  po3_suzuki_filtered_pm_partial_sum_manuscript (Finset.range K) a γ

/-- The raw manuscript prefix is exactly the packaged manuscript prefix. -/
theorem po3_suzuki_raw_gamma_pm_prefix_eq_filtered_prefix_manuscript
    (K : ℕ) (a : ℂ) (γ : ℕ → ℂ) :
    po3_suzuki_raw_gamma_pm_prefix K a γ
      = po3_suzuki_filtered_pm_prefix_manuscript K a γ := by
  rw [po3_suzuki_raw_gamma_pm_prefix, po3_suzuki_filtered_pm_prefix_manuscript,
    po3_suzuki_raw_gamma_pm_finset_eq_partial_sum_manuscript]

/-- The weighted six-pole contribution of one manuscript `γ`-mode to the
neighboring anti-diagonal gap. -/
noncomputable def po3_suzuki_manuscript_gap_weight
    (a γ : ℂ) : ℂ :=
  (po3_suzuki_manuscript_prefactor a * po3_suzuki_manuscript_amp a γ) *
    po3_suzuki_filtered_pm_gap_term_20_11
      (po3_suzuki_manuscript_alpha_step a) γ

/-- Named two-mode manuscript gap sum for the explicit `prefix2` shell. This is
the object that an external numerical certificate has to show is nonzero. -/
noncomputable def po3_suzuki_manuscript_gap_sum2
    (a γ0 γ1 : ℂ) : ℂ :=
  po3_suzuki_manuscript_gap_weight a γ0 +
    po3_suzuki_manuscript_gap_weight a γ1

/-- Named three-mode manuscript gap sum for the explicit `prefix3` shell. This
is the clean interface between an external numerical witness and the formal
kill criterion. -/
noncomputable def po3_suzuki_manuscript_gap_sum3
    (a γ0 γ1 γ2 : ℂ) : ℂ :=
  po3_suzuki_manuscript_gap_weight a γ0 +
    po3_suzuki_manuscript_gap_weight a γ1 +
      po3_suzuki_manuscript_gap_weight a γ2

/-- The raw manuscript singleton is exactly the packaged manuscript singleton
already used by the shell. -/
theorem po3_suzuki_raw_gamma_pm_singleton_eq_filtered_singleton_manuscript
    (a γ : ℂ) :
    po3_suzuki_raw_gamma_pm_singleton a γ
      = po3_suzuki_filtered_pm_singleton_manuscript a γ := by
  rw [po3_suzuki_raw_gamma_pm_singleton, po3_suzuki_filtered_pm_singleton_manuscript,
    po3_suzuki_raw_gamma_pm_finset_eq_partial_sum_manuscript]

/-- The manuscript prefactor is nonzero once `a ≠ 0`. -/
theorem po3_suzuki_manuscript_prefactor_ne_zero
    {a : ℂ} (ha : a ≠ 0) :
    po3_suzuki_manuscript_prefactor a ≠ 0 := by
  unfold po3_suzuki_manuscript_prefactor
  apply div_ne_zero
  · apply mul_ne_zero
    · norm_num
    · exact pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
  · exact pow_ne_zero 3 ha

/-- The manuscript amplitude is nonzero as soon as `sin(aγ) ≠ 0`. -/
theorem po3_suzuki_manuscript_amp_ne_zero
    {a γ : ℂ} (hsin : Complex.sin (a * γ) ≠ 0) :
    po3_suzuki_manuscript_amp a γ ≠ 0 := by
  unfold po3_suzuki_manuscript_amp
  exact pow_ne_zero 2 hsin

/-- The first anti-diagonal gap for the manuscript-shaped finite partial
`γ`-sum is the same finite sum of six-pole defects, with the global prefactor
and amplitude carried pointwise. -/
theorem po3_suzuki_filtered_pm_partial_sum_antidiagonal_gap_20_11
    {ι : Type*} (S : Finset ι) (κ : ℂ) (amp : ι → ℂ) (γ : ι → ℂ) (c : ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_filtered_pm_partial_sum S κ amp γ c) 1
      =
        Finset.sum S (fun i =>
          (κ * amp i) * po3_suzuki_filtered_pm_gap_term_20_11 c (γ i)) := by
  rw [po3_suzuki_filtered_pm_partial_sum, po3_suzuki_filtered_pm_finset_antidiagonal_gap_20_11]

/-- If the first anti-diagonal gap of the manuscript-shaped finite partial
`γ`-sum is nonzero, then the Suzuki packet cannot come from a one-variable
`(+,-)` profile. -/
theorem po3_no_suzuki_filtered_pm_partial_sum_candidate_of_gap_20_11
    {ι : Type*} (S : Finset ι) (κ : ℂ) (amp : ι → ℂ) (γ : ι → ℂ) (c : ℂ)
    (hgap :
      Finset.sum S (fun i =>
        (κ * amp i) * po3_suzuki_filtered_pm_gap_term_20_11 c (γ i)) ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_filtered_pm_partial_sum S κ amp γ c
        = po3_suzuki_filtered_pm_candidate u := by
  apply po3_no_sum_profile_of_adjacent_antidiagonal_defect_ne_zero
  rw [po3_suzuki_filtered_pm_partial_sum_antidiagonal_gap_20_11]
  exact hgap

/-- The first anti-diagonal gap for the direct manuscript finite partial
`γ`-sum. This is the exact finite truncation of the raw manuscript formula in
the `(2,0)` vs `(1,1)` test. -/
theorem po3_suzuki_filtered_pm_partial_sum_manuscript_antidiagonal_gap_20_11
    {ι : Type*} (S : Finset ι) (a : ℂ) (γ : ι → ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_filtered_pm_partial_sum_manuscript S a γ) 1
      =
        Finset.sum S (fun i =>
          (po3_suzuki_manuscript_prefactor a * po3_suzuki_manuscript_amp a (γ i)) *
            po3_suzuki_filtered_pm_gap_term_20_11
              (po3_suzuki_manuscript_alpha_step a) (γ i)) := by
  rw [po3_suzuki_filtered_pm_partial_sum_manuscript,
    po3_suzuki_filtered_pm_partial_sum_antidiagonal_gap_20_11]

/-- The direct raw manuscript finite `γ`-sum has the same first anti-diagonal
gap as the packaged manuscript shell, namely the finite six-pole sum. -/
theorem po3_suzuki_raw_gamma_pm_finset_antidiagonal_gap_20_11
    {ι : Type*} (S : Finset ι) (a : ℂ) (γ : ι → ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_raw_gamma_pm_finset S a γ) 1
      =
        Finset.sum S (fun i =>
          (po3_suzuki_manuscript_prefactor a * po3_suzuki_manuscript_amp a (γ i)) *
            po3_suzuki_filtered_pm_gap_term_20_11
              (po3_suzuki_manuscript_alpha_step a) (γ i)) := by
  rw [po3_suzuki_raw_gamma_pm_finset_eq_partial_sum_manuscript]
  exact po3_suzuki_filtered_pm_partial_sum_manuscript_antidiagonal_gap_20_11 S a γ

/-- If the first anti-diagonal gap of the direct manuscript finite partial
`γ`-sum is nonzero, then the Suzuki packet cannot come from a one-variable
`(+,-)` profile. -/
theorem po3_no_suzuki_filtered_pm_partial_sum_manuscript_candidate_of_gap_20_11
    {ι : Type*} (S : Finset ι) (a : ℂ) (γ : ι → ℂ)
    (hgap :
      Finset.sum S (fun i =>
        (po3_suzuki_manuscript_prefactor a * po3_suzuki_manuscript_amp a (γ i)) *
          po3_suzuki_filtered_pm_gap_term_20_11
            (po3_suzuki_manuscript_alpha_step a) (γ i)) ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_filtered_pm_partial_sum_manuscript S a γ
        = po3_suzuki_filtered_pm_candidate u := by
  apply po3_no_sum_profile_of_adjacent_antidiagonal_defect_ne_zero
  rw [po3_suzuki_filtered_pm_partial_sum_manuscript_antidiagonal_gap_20_11]
  exact hgap

/-- If the first anti-diagonal gap of the direct raw manuscript finite
`γ`-sum is nonzero, then it cannot come from a one-variable `(+,-)` profile. -/
theorem po3_no_suzuki_raw_gamma_pm_finset_candidate_of_gap_20_11
    {ι : Type*} (S : Finset ι) (a : ℂ) (γ : ι → ℂ)
    (hgap :
      Finset.sum S (fun i =>
        (po3_suzuki_manuscript_prefactor a * po3_suzuki_manuscript_amp a (γ i)) *
          po3_suzuki_filtered_pm_gap_term_20_11
            (po3_suzuki_manuscript_alpha_step a) (γ i)) ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_finset S a γ
        = po3_suzuki_filtered_pm_candidate u := by
  rw [po3_suzuki_raw_gamma_pm_finset_eq_partial_sum_manuscript]
  exact po3_no_suzuki_filtered_pm_partial_sum_manuscript_candidate_of_gap_20_11
    S a γ hgap

/-- The neighboring anti-diagonal defect for the direct manuscript singleton
truncation is exactly one weighted six-pole gap term. -/
theorem po3_suzuki_filtered_pm_singleton_manuscript_antidiagonal_gap_20_11
    (a γ : ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_filtered_pm_singleton_manuscript a γ) 1
      =
        (po3_suzuki_manuscript_prefactor a * po3_suzuki_manuscript_amp a γ) *
          po3_suzuki_filtered_pm_gap_term_20_11
            (po3_suzuki_manuscript_alpha_step a) γ := by
  rw [po3_suzuki_filtered_pm_singleton_manuscript,
    po3_suzuki_filtered_pm_partial_sum_manuscript_antidiagonal_gap_20_11]
  simp

/-- The neighboring anti-diagonal defect for the raw manuscript singleton
truncation is exactly the same weighted six-pole gap term. -/
theorem po3_suzuki_raw_gamma_pm_singleton_antidiagonal_gap_20_11
    (a γ : ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_raw_gamma_pm_singleton a γ) 1
      =
        (po3_suzuki_manuscript_prefactor a * po3_suzuki_manuscript_amp a γ) *
          po3_suzuki_filtered_pm_gap_term_20_11
            (po3_suzuki_manuscript_alpha_step a) γ := by
  rw [po3_suzuki_raw_gamma_pm_singleton_eq_filtered_singleton_manuscript]
  exact po3_suzuki_filtered_pm_singleton_manuscript_antidiagonal_gap_20_11 a γ

/-- The first anti-diagonal gap for the direct raw manuscript prefix
truncation is the finite six-pole sum over the first `K` `γ`-modes. -/
theorem po3_suzuki_raw_gamma_pm_prefix_antidiagonal_gap_20_11
    (K : ℕ) (a : ℂ) (γ : ℕ → ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_raw_gamma_pm_prefix K a γ) 1
      =
        Finset.sum (Finset.range K) (fun i =>
          po3_suzuki_manuscript_gap_weight a (γ i)) := by
  rw [po3_suzuki_raw_gamma_pm_prefix, po3_suzuki_raw_gamma_pm_finset_antidiagonal_gap_20_11]
  simp [po3_suzuki_manuscript_gap_weight]

/-- If the first anti-diagonal gap of the raw manuscript prefix truncation is
nonzero, then the prefix cannot be a one-variable `(+,-)` profile. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix_candidate_of_gap_20_11
    (K : ℕ) (a : ℂ) (γ : ℕ → ℂ)
    (hgap :
      Finset.sum (Finset.range K) (fun i =>
        po3_suzuki_manuscript_gap_weight a (γ i)) ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix K a γ
        = po3_suzuki_filtered_pm_candidate u := by
  rw [po3_suzuki_raw_gamma_pm_prefix]
  exact po3_no_suzuki_raw_gamma_pm_finset_candidate_of_gap_20_11
    (Finset.range K) a γ (by simpa [po3_suzuki_manuscript_gap_weight] using hgap)

/-- Explicit two-term anti-diagonal gap formula. -/
theorem po3_suzuki_raw_gamma_pm_prefix2_antidiagonal_gap_20_11
    (a γ0 γ1 : ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_raw_gamma_pm_prefix2 a γ0 γ1) 1
      =
        po3_suzuki_manuscript_gap_sum2 a γ0 γ1 := by
  rw [po3_suzuki_raw_gamma_pm_prefix2,
    po3_suzuki_raw_gamma_pm_prefix_antidiagonal_gap_20_11]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [po3_gamma_prefix2, po3_suzuki_manuscript_gap_weight,
    po3_suzuki_manuscript_gap_sum2]

/-- Explicit three-term anti-diagonal gap formula. -/
theorem po3_suzuki_raw_gamma_pm_prefix3_antidiagonal_gap_20_11
    (a γ0 γ1 γ2 : ℂ) :
    po3_antidiagonal_adjacent_defect
        (po3_suzuki_raw_gamma_pm_prefix3 a γ0 γ1 γ2) 1
      =
        po3_suzuki_manuscript_gap_sum3 a γ0 γ1 γ2 := by
  rw [po3_suzuki_raw_gamma_pm_prefix3,
    po3_suzuki_raw_gamma_pm_prefix_antidiagonal_gap_20_11]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp [po3_gamma_prefix3, po3_suzuki_manuscript_gap_weight,
    po3_suzuki_manuscript_gap_sum3, add_assoc]

/-- Explicit `K = 2` kill criterion. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix2_candidate_of_gap_20_11
    (a γ0 γ1 : ℂ)
    (hgap : po3_suzuki_manuscript_gap_sum2 a γ0 γ1 ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix2 a γ0 γ1
        = po3_suzuki_filtered_pm_candidate u := by
  rw [po3_suzuki_raw_gamma_pm_prefix2]
  have hgap' :
      Finset.sum (Finset.range 2) (fun i =>
        po3_suzuki_manuscript_gap_weight a (po3_gamma_prefix2 γ0 γ1 i)) ≠ 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simpa [po3_gamma_prefix2, po3_suzuki_manuscript_gap_weight,
      po3_suzuki_manuscript_gap_sum2] using hgap
  exact po3_no_suzuki_raw_gamma_pm_prefix_candidate_of_gap_20_11
    2 a (po3_gamma_prefix2 γ0 γ1)
    hgap'

/-- Explicit `K = 3` kill criterion. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix3_candidate_of_gap_20_11
    (a γ0 γ1 γ2 : ℂ)
    (hgap : po3_suzuki_manuscript_gap_sum3 a γ0 γ1 γ2 ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix3 a γ0 γ1 γ2
        = po3_suzuki_filtered_pm_candidate u := by
  rw [po3_suzuki_raw_gamma_pm_prefix3]
  have hgap' :
      Finset.sum (Finset.range 3) (fun i =>
        po3_suzuki_manuscript_gap_weight a (po3_gamma_prefix3 γ0 γ1 γ2 i)) ≠ 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simpa [po3_gamma_prefix3, po3_suzuki_manuscript_gap_weight,
      po3_suzuki_manuscript_gap_sum3, add_assoc] using hgap
  exact po3_no_suzuki_raw_gamma_pm_prefix_candidate_of_gap_20_11
    3 a (po3_gamma_prefix3 γ0 γ1 γ2)
    hgap'

/-- Short bridge lemma for the external two-mode witness interface. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix2_of_gap_sum2_ne_zero
    (a γ0 γ1 : ℂ)
    (hgap : po3_suzuki_manuscript_gap_sum2 a γ0 γ1 ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix2 a γ0 γ1
        = po3_suzuki_filtered_pm_candidate u :=
  po3_no_suzuki_raw_gamma_pm_prefix2_candidate_of_gap_20_11 a γ0 γ1 hgap

/-- Short bridge lemma for the external three-mode witness interface. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix3_of_gap_sum3_ne_zero
    (a γ0 γ1 γ2 : ℂ)
    (hgap : po3_suzuki_manuscript_gap_sum3 a γ0 γ1 γ2 ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix3 a γ0 γ1 γ2
        = po3_suzuki_filtered_pm_candidate u :=
  po3_no_suzuki_raw_gamma_pm_prefix3_candidate_of_gap_20_11 a γ0 γ1 γ2 hgap

/-- Shared denominator used for the decimal `28` witness values imported from
the external zeta-zero scan. -/
noncomputable def po3_decimal28 (n : ℤ) : ℂ :=
  (n : ℂ) / ((10 : ℂ) ^ (28 : ℕ))

/-- Decimal-28 approximation of the first positive zeta ordinate, taken from
the external `mpmath.zetazero` witness scan. This is a numerical witness
candidate, not a formal theorem about the true zero set. -/
noncomputable def po3_first_zeta_gamma0_decimal28 : ℂ :=
  po3_decimal28 141347251417346937904572519836

/-- Decimal-28 approximation of the second positive zeta ordinate, used only as
an external witness placeholder. -/
noncomputable def po3_first_zeta_gamma1_decimal28 : ℂ :=
  po3_decimal28 210220396387715549926284795939

/-- Decimal-28 approximation of the third positive zeta ordinate, used only as
an external witness placeholder. -/
noncomputable def po3_first_zeta_gamma2_decimal28 : ℂ :=
  po3_decimal28 250108575801456887632137909926

/-- Named two-mode witness sum for the concrete `a = 1` decimal-zeta packet.
Once an external certificate proves this quantity nonzero, the `prefix2` shell
is killed immediately. -/
noncomputable def po3_first_zeta_gap_sum2_a1_decimal28 : ℂ :=
  po3_suzuki_manuscript_gap_sum2 (1 : ℂ)
    po3_first_zeta_gamma0_decimal28
    po3_first_zeta_gamma1_decimal28

/-- Named three-mode witness sum for the concrete `a = 1` decimal-zeta packet.
This is the main external certificate target for the current `prefix3` shell. -/
noncomputable def po3_first_zeta_gap_sum3_a1_decimal28 : ℂ :=
  po3_suzuki_manuscript_gap_sum3 (1 : ℂ)
    po3_first_zeta_gamma0_decimal28
    po3_first_zeta_gamma1_decimal28
    po3_first_zeta_gamma2_decimal28

/-- Concrete `prefix2` witness stub: once the external numerical certificate
shows the named decimal-zeta gap sum is nonzero, the `a = 1` two-mode packet
cannot come from a one-variable `(+,-)` profile. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix2_of_first_zeta_decimal28_witness
    (hgap : po3_first_zeta_gap_sum2_a1_decimal28 ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix2
          (1 : ℂ)
          po3_first_zeta_gamma0_decimal28
          po3_first_zeta_gamma1_decimal28
        = po3_suzuki_filtered_pm_candidate u := by
  exact po3_no_suzuki_raw_gamma_pm_prefix2_of_gap_sum2_ne_zero
    (1 : ℂ)
    po3_first_zeta_gamma0_decimal28
    po3_first_zeta_gamma1_decimal28
    hgap

/-- Concrete `prefix3` witness stub: once the external numerical certificate
shows the named decimal-zeta gap sum is nonzero, the `a = 1` three-mode packet
cannot come from a one-variable `(+,-)` profile. -/
theorem po3_no_suzuki_raw_gamma_pm_prefix3_of_first_zeta_decimal28_witness
    (hgap : po3_first_zeta_gap_sum3_a1_decimal28 ≠ 0) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_prefix3
          (1 : ℂ)
          po3_first_zeta_gamma0_decimal28
          po3_first_zeta_gamma1_decimal28
          po3_first_zeta_gamma2_decimal28
        = po3_suzuki_filtered_pm_candidate u := by
  exact po3_no_suzuki_raw_gamma_pm_prefix3_of_gap_sum3_ne_zero
    (1 : ℂ)
    po3_first_zeta_gamma0_decimal28
    po3_first_zeta_gamma1_decimal28
    po3_first_zeta_gamma2_decimal28
    hgap

/-- A direct manuscript singleton truncation already rules out a one-variable
`(+,-)` profile whenever its six-pole gap term is nonzero and the manuscript
weight does not vanish. -/
theorem po3_no_suzuki_filtered_pm_singleton_manuscript_candidate_of_gap_20_11
    (a γ : ℂ)
    (ha : a ≠ 0)
    (hsin : Complex.sin (a * γ) ≠ 0)
    (hγ0 : γ ≠ 0)
    (hγ1 : γ ≠ po3_suzuki_manuscript_alpha_step a)
    (hγ2 : γ ≠ 2 * po3_suzuki_manuscript_alpha_step a)
    (hγ3 : γ ≠ 3 * po3_suzuki_manuscript_alpha_step a) :
    ¬ ∃ u,
      po3_suzuki_filtered_pm_singleton_manuscript a γ
        = po3_suzuki_filtered_pm_candidate u := by
  apply po3_no_sum_profile_of_adjacent_antidiagonal_defect_ne_zero
  rw [po3_suzuki_filtered_pm_singleton_manuscript_antidiagonal_gap_20_11]
  apply mul_ne_zero
  · exact mul_ne_zero
      (po3_suzuki_manuscript_prefactor_ne_zero ha)
      (po3_suzuki_manuscript_amp_ne_zero hsin)
  · exact po3_suzuki_filtered_pm_gap_term_20_11_ne_zero
      (po3_suzuki_manuscript_alpha_step a) γ
      (by
        unfold po3_suzuki_manuscript_alpha_step
        exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) ha)
      hγ0 hγ1 hγ2 hγ3

/-- The same singleton kill, but now stated directly for the raw manuscript
`γ`-sum formula. -/
theorem po3_no_suzuki_raw_gamma_pm_singleton_candidate_of_gap_20_11
    (a γ : ℂ)
    (ha : a ≠ 0)
    (hsin : Complex.sin (a * γ) ≠ 0)
    (hγ0 : γ ≠ 0)
    (hγ1 : γ ≠ po3_suzuki_manuscript_alpha_step a)
    (hγ2 : γ ≠ 2 * po3_suzuki_manuscript_alpha_step a)
    (hγ3 : γ ≠ 3 * po3_suzuki_manuscript_alpha_step a) :
    ¬ ∃ u,
      po3_suzuki_raw_gamma_pm_singleton a γ
        = po3_suzuki_filtered_pm_candidate u := by
  rw [po3_suzuki_raw_gamma_pm_singleton_eq_filtered_singleton_manuscript]
  exact po3_no_suzuki_filtered_pm_singleton_manuscript_candidate_of_gap_20_11
    a γ ha hsin hγ0 hγ1 hγ2 hγ3

/-- Filtered one-variable profile for the concrete `(++ )` Section 8 block. -/
noncomputable def po3_section8_filtered_pp_profile (B t : ℝ) : ℤ → ℂ :=
  fun k =>
    po3_filtered_difference_profile (po3_section8_arch_profile B t) k
      - po3_filtered_difference_profile (po3_section8_prime_profile B t) k

/-- Filtered one-variable profile for the concrete `(+,-)` Section 8 block. -/
noncomputable def po3_section8_filtered_pm_profile (B t : ℝ) : ℕ → ℂ :=
  fun u =>
    po3_filtered_sum_profile (po3_nat_profile_of_int (po3_section8_arch_profile B t)) u
      - po3_filtered_sum_profile (po3_nat_profile_of_int (po3_section8_prime_profile B t)) u

/-- Pointwise raw split `q = arch - prime` for the manuscript Section 8
profiles. -/
theorem po3_section8_raw_kernel_split
    (B t : ℝ) :
    ∀ r s,
      po3_section8_raw_kernel B t r s
        = po3_section8_arch_kernel B t r s - po3_section8_prime_kernel B t r s := by
  intro r s
  simp [po3_section8_raw_kernel, po3_section8_arch_kernel, po3_section8_prime_kernel,
    po3_section8_raw_profile, po3_signed_difference_kernel]

/-- The raw Section 8 kernel in literal manuscript form `q_{rs}=a(r-s)-p(r-s)`. -/
theorem po3_section8_raw_kernel_difference_formula
    (B t : ℝ) :
    ∀ r s,
      po3_section8_raw_kernel B t r s
        =
          po3_section8_arch_profile B t (r - s)
          - po3_section8_prime_profile B t (r - s) := by
  intro r s
  simp [po3_section8_raw_kernel, po3_section8_raw_profile, po3_signed_difference_kernel]

/-- Filtered `(++ )` Section 8 block from the raw manuscript formula. -/
theorem po3_four_term_stencil_of_section8_raw_kernel_pp
    (B t : ℝ) :
    po3_four_term_stencil (fun m n => po3_section8_raw_kernel B t (m : ℤ) (n : ℤ))
      =
        po3_difference_kernel (po3_section8_filtered_pp_profile B t) := by
  exact po3_four_term_stencil_of_raw_q_difference_formula_pp
    (q := po3_section8_raw_kernel B t)
    (a := po3_section8_arch_profile B t)
    (p := po3_section8_prime_profile B t)
    (hq := po3_section8_raw_kernel_difference_formula B t)

/-- Filtered `(+,-)` Section 8 block from the raw manuscript formula. -/
theorem po3_four_term_stencil_of_section8_raw_kernel_pm
    (B t : ℝ) :
    po3_four_term_stencil (fun m n => po3_section8_raw_kernel B t (m : ℤ) (-(n : ℤ)))
      =
        po3_sum_kernel (po3_section8_filtered_pm_profile B t) := by
  exact po3_four_term_stencil_of_raw_q_difference_formula_pm
    (q := po3_section8_raw_kernel B t)
    (a := po3_section8_arch_profile B t)
    (p := po3_section8_prime_profile B t)
    (hq := po3_section8_raw_kernel_difference_formula B t)

/-- Mixed packet of the filtered raw `(++ )` Section 8 family. -/
theorem po3_mixed_packet_of_section8_raw_kernel_pp
    (B t : ℝ) (r s : ℕ) :
    po3_mixed_packet
        (po3_four_term_stencil (fun m n => po3_section8_raw_kernel B t (m : ℤ) (n : ℤ))) r s
      =
        po3_centered_second_difference (po3_section8_filtered_pp_profile B t)
          ((r : ℤ) - (s : ℤ)) := by
  exact po3_mixed_packet_of_raw_q_difference_formula_pp
    (q := po3_section8_raw_kernel B t)
    (a := po3_section8_arch_profile B t)
    (p := po3_section8_prime_profile B t)
    (hq := po3_section8_raw_kernel_difference_formula B t)
    (r := r) (s := s)

/-- Mixed packet of the filtered raw `(+,-)` Section 8 family. -/
theorem po3_mixed_packet_of_section8_raw_kernel_pm
    (B t : ℝ) (r s : ℕ) :
    po3_mixed_packet
        (po3_four_term_stencil (fun m n => po3_section8_raw_kernel B t (m : ℤ) (-(n : ℤ)))) r s
      =
        po3_forward_second_difference (po3_section8_filtered_pm_profile B t)
          (r + s) := by
  exact po3_mixed_packet_of_raw_q_difference_formula_pm
    (q := po3_section8_raw_kernel B t)
    (a := po3_section8_arch_profile B t)
    (p := po3_section8_prime_profile B t)
    (hq := po3_section8_raw_kernel_difference_formula B t)
    (r := r) (s := s)

/-- Once the Suzuki `(+,-)` block lands as a sum-profile candidate, equality
with the concrete Section 8 filtered block is exactly profile equality. -/
theorem po3_suzuki_filtered_pm_candidate_eq_section8_iff
    (u : ℕ → ℂ) (B t : ℝ) :
    po3_suzuki_filtered_pm_candidate u
      = po3_sum_kernel (po3_section8_filtered_pm_profile B t)
        ↔
      u = po3_section8_filtered_pm_profile B t := by
  exact po3_sum_kernel_eq_iff u (po3_section8_filtered_pm_profile B t)

/-- Existence of a one-variable `(+,-)` Suzuki profile is equivalent to
anti-diagonal invariance of the filtered block. -/
theorem po3_exists_suzuki_filtered_pm_candidate_iff
    (K : ℕ → ℕ → ℂ) :
    (∃ u, K = po3_suzuki_filtered_pm_candidate u)
      ↔
    ∀ m n m' n', m + n = m' + n' → K m n = K m' n' := by
  simpa [po3_suzuki_filtered_pm_candidate] using
    po3_eq_sum_kernel_iff_antidiagonal_invariant (K := K)

/-- Once the Suzuki `(++ )` block lands as a difference-profile candidate,
equality with the concrete Section 8 filtered block is exactly profile
equality. -/
theorem po3_suzuki_filtered_pp_candidate_eq_section8_iff
    (u : ℤ → ℂ) (B t : ℝ) :
    po3_suzuki_filtered_pp_candidate u
      = po3_difference_kernel (po3_section8_filtered_pp_profile B t)
        ↔
      u = po3_section8_filtered_pp_profile B t := by
  exact po3_difference_kernel_eq_iff u (po3_section8_filtered_pp_profile B t)

/-- Existence of a one-variable `(++ )` Suzuki profile is equivalent to
difference-level invariance of the filtered block. -/
theorem po3_exists_suzuki_filtered_pp_candidate_iff
    (K : ℕ → ℕ → ℂ) :
    (∃ u, K = po3_suzuki_filtered_pp_candidate u)
      ↔
    ∀ m n m' n' : ℕ,
      ((m : ℤ) - (n : ℤ)) = ((m' : ℤ) - (n' : ℤ)) → K m n = K m' n' := by
  simpa [po3_suzuki_filtered_pp_candidate] using
    po3_eq_difference_kernel_iff_difference_invariant (K := K)

end PO3Section8Profiles

section PO3Witness

variable {𝕜 V W : Type*}
variable [DivisionRing 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

/-- If the boundary-cap subspace already contains `h` but does not contain `v`,
then `v` cannot lie on the line generated by `h`. -/
theorem not_mem_span_singleton_of_mem_submodule_of_not_mem
    {E : Submodule 𝕜 V} {h v : V}
    (hhE : h ∈ E) (hvE : v ∉ E) :
    v ∉ 𝕜 ∙ h := by
  intro hvh
  have hline : 𝕜 ∙ h ≤ E := (Submodule.span_singleton_le_iff_mem h E).2 hhE
  exact hvE (hline hvh)

/-- Collinearity with a single vector is reflected by an injective linear map. -/
theorem mem_span_singleton_of_mem_span_singleton_map
    {f : V →ₗ[𝕜] W} (hf : Function.Injective f) {h v : V}
    (hfv : f v ∈ 𝕜 ∙ f h) :
    v ∈ 𝕜 ∙ h := by
  rcases Submodule.mem_span_singleton.mp hfv with ⟨a, ha⟩
  refine Submodule.mem_span_singleton.mpr ?_
  refine ⟨a, ?_⟩
  apply hf
  simpa using ha

/-- Hence non-collinearity also survives after applying an injective linear map. -/
theorem not_mem_span_singleton_map_of_injective
    {f : V →ₗ[𝕜] W} (hf : Function.Injective f) {h v : V}
    (hv : v ∉ 𝕜 ∙ h) :
    f v ∉ 𝕜 ∙ f h := by
  intro hfv
  exact hv (mem_span_singleton_of_mem_span_singleton_map hf hfv)

/-- Injective transport preserves and reflects collinearity with a fixed vector. -/
theorem mem_span_singleton_map_iff_of_injective
    {f : V →ₗ[𝕜] W} (hf : Function.Injective f) {h v : V} :
    f v ∈ 𝕜 ∙ f h ↔ v ∈ 𝕜 ∙ h := by
  constructor
  · exact mem_span_singleton_of_mem_span_singleton_map hf
  · intro hv
    rcases Submodule.mem_span_singleton.mp hv with ⟨a, ha⟩
    refine Submodule.mem_span_singleton.mpr ?_
    refine ⟨a, ?_⟩
    calc
      a • f h = f (a • h) := by simp
      _ = f v := by simp [ha]

/-- Hence non-collinearity is also reflected exactly by an injective transport. -/
theorem not_mem_span_singleton_map_iff_of_injective
    {f : V →ₗ[𝕜] W} (hf : Function.Injective f) {h v : V} :
    f v ∉ 𝕜 ∙ f h ↔ v ∉ 𝕜 ∙ h := by
  constructor
  · intro hfv hv
    exact hfv ((mem_span_singleton_map_iff_of_injective hf).2 hv)
  · exact not_mem_span_singleton_map_of_injective hf

/-- Dually, dependence of linear functionals also descends through a surjective
pullback. This is the minus-side outer-factor bridge behind `PO3a.4`. -/
theorem mem_span_singleton_of_comp_mem_span_singleton_of_surjective
    {V₁ V₂ : Type*}
    [Field 𝕜]
    [AddCommGroup V₁] [Module 𝕜 V₁]
    [AddCommGroup V₂] [Module 𝕜 V₂]
    {g : V₁ →ₗ[𝕜] V₂} (hg : Function.Surjective g)
    {φ ψ : V₂ →ₗ[𝕜] 𝕜}
    (hcomp : φ.comp g ∈ 𝕜 ∙ (ψ.comp g)) :
    φ ∈ 𝕜 ∙ ψ := by
  rcases Submodule.mem_span_singleton.mp hcomp with ⟨a, ha⟩
  refine Submodule.mem_span_singleton.mpr ?_
  refine ⟨a, ?_⟩
  ext y
  rcases hg y with ⟨x, rfl⟩
  have hx := LinearMap.congr_fun ha x
  simpa using hx

/-- Hence non-collinearity of functionals also survives pullback along a
surjective linear map. -/
theorem not_mem_span_singleton_comp_of_surjective
    {V₁ V₂ : Type*}
    [Field 𝕜]
    [AddCommGroup V₁] [Module 𝕜 V₁]
    [AddCommGroup V₂] [Module 𝕜 V₂]
    {g : V₁ →ₗ[𝕜] V₂} (hg : Function.Surjective g)
    {φ ψ : V₂ →ₗ[𝕜] 𝕜}
    (hφ : φ ∉ 𝕜 ∙ ψ) :
    φ.comp g ∉ 𝕜 ∙ (ψ.comp g) := by
  intro hcomp
  exact hφ (mem_span_singleton_of_comp_mem_span_singleton_of_surjective hg hcomp)

/-- Surjective pullback preserves and reflects collinearity of linear
functionals. -/
theorem mem_span_singleton_comp_iff_of_surjective
    {V₁ V₂ : Type*}
    [Field 𝕜]
    [AddCommGroup V₁] [Module 𝕜 V₁]
    [AddCommGroup V₂] [Module 𝕜 V₂]
    {g : V₁ →ₗ[𝕜] V₂} (hg : Function.Surjective g)
    {φ ψ : V₂ →ₗ[𝕜] 𝕜} :
    φ.comp g ∈ 𝕜 ∙ (ψ.comp g) ↔ φ ∈ 𝕜 ∙ ψ := by
  constructor
  · exact mem_span_singleton_of_comp_mem_span_singleton_of_surjective hg
  · intro hφ
    rcases Submodule.mem_span_singleton.mp hφ with ⟨a, ha⟩
    refine Submodule.mem_span_singleton.mpr ?_
    refine ⟨a, ?_⟩
    ext x
    have hx := LinearMap.congr_fun ha (g x)
    simpa using hx

/-- Hence non-collinearity of functionals is also reflected exactly by a
surjective pullback. -/
theorem not_mem_span_singleton_comp_iff_of_surjective
    {V₁ V₂ : Type*}
    [Field 𝕜]
    [AddCommGroup V₁] [Module 𝕜 V₁]
    [AddCommGroup V₂] [Module 𝕜 V₂]
    {g : V₁ →ₗ[𝕜] V₂} (hg : Function.Surjective g)
    {φ ψ : V₂ →ₗ[𝕜] 𝕜} :
    φ.comp g ∉ 𝕜 ∙ (ψ.comp g) ↔ φ ∉ 𝕜 ∙ ψ := by
  constructor
  · intro hcomp hφ
    exact hcomp ((mem_span_singleton_comp_iff_of_surjective hg).2 hφ)
  · exact not_mem_span_singleton_comp_of_surjective hg

/-- Practical `PO3a.3` receiver: once `h` lives inside the finite boundary-cap
space `E` but `v` does not, any injective transport keeps them non-collinear. -/
theorem not_mem_span_singleton_map_of_mem_submodule_of_not_mem
    {E : Submodule 𝕜 V} {f : V →ₗ[𝕜] W} (hf : Function.Injective f)
    {h v : V} (hhE : h ∈ E) (hvE : v ∉ E) :
    f v ∉ 𝕜 ∙ f h := by
  apply not_mem_span_singleton_map_of_injective hf
  exact not_mem_span_singleton_of_mem_submodule_of_not_mem hhE hvE

/-- Dual-witness version: a single linear functional annihilating the whole
boundary-cap subspace but not `v` already proves `v ∉ E`. -/
theorem not_mem_submodule_of_linearForm
    {E : Submodule 𝕜 V} {v : V} {φ : V →ₗ[𝕜] 𝕜}
    (hEφ : E ≤ LinearMap.ker φ) (hvφ : φ v ≠ 0) :
    v ∉ E := by
  intro hvE
  exact hvφ (show φ v = 0 from hEφ hvE)

/-- Abstract projector criterion: if a linear projector `Π` has range `E`, then
membership in `E` is equivalent to being fixed by `Π`. -/
theorem mem_submodule_iff_projector_eq_self
    {E : Submodule 𝕜 V} {Pproj : V →ₗ[𝕜] V}
    (hPproj_idem : Pproj.comp Pproj = Pproj) (hPproj_range : LinearMap.range Pproj = E)
    {w : V} :
    w ∈ E ↔ Pproj w = w := by
  constructor
  · intro hwE
    rw [← hPproj_range, LinearMap.mem_range] at hwE
    rcases hwE with ⟨u, rfl⟩
    simpa using LinearMap.congr_fun hPproj_idem u
  · intro hw
    rw [← hPproj_range, LinearMap.mem_range]
    exact ⟨w, hw⟩

/-- Hence a nonzero projector residual already proves that `w` is outside the
boundary-cap subspace. -/
theorem not_mem_submodule_of_projector_residual_ne_zero
    {E : Submodule 𝕜 V} {Pproj : V →ₗ[𝕜] V}
    (hPproj_idem : Pproj.comp Pproj = Pproj) (hPproj_range : LinearMap.range Pproj = E)
    {w : V} (hres : w - Pproj w ≠ 0) :
    w ∉ E := by
  intro hwE
  have hfix : Pproj w = w :=
    (mem_submodule_iff_projector_eq_self hPproj_idem hPproj_range).1 hwE
  exact hres (sub_eq_zero.mpr hfix.symm)

/-- Projector-witness version of the `PO3a.3` receiver: once `h` lies in the
boundary-cap subspace `E`, a nonzero projector residual for `v` excludes
collinearity after any injective transport. -/
theorem not_mem_span_singleton_map_of_projector_residual_ne_zero
    {E : Submodule 𝕜 V} {Pproj : V →ₗ[𝕜] V} {f : V →ₗ[𝕜] W}
    (hPproj_idem : Pproj.comp Pproj = Pproj) (hPproj_range : LinearMap.range Pproj = E)
    (hf : Function.Injective f)
    {h v : V} (hhE : h ∈ E) (hres : v - Pproj v ≠ 0) :
    f v ∉ 𝕜 ∙ f h := by
  apply not_mem_span_singleton_map_of_mem_submodule_of_not_mem hf hhE
  exact not_mem_submodule_of_projector_residual_ne_zero hPproj_idem hPproj_range hres

/-- Combined witness packet: if `h` lies in the boundary-cap subspace `E`, a
single linear functional separates `v` from `E`, and the transport is
injective, then the transported vectors are still non-collinear. -/
theorem not_mem_span_singleton_map_of_linearForm_witness
    {E : Submodule 𝕜 V} {f : V →ₗ[𝕜] W} (hf : Function.Injective f)
    {h v : V} {φ : V →ₗ[𝕜] 𝕜}
    (hhE : h ∈ E) (hEφ : E ≤ LinearMap.ker φ) (hvφ : φ v ≠ 0) :
    f v ∉ 𝕜 ∙ f h := by
  apply not_mem_span_singleton_map_of_mem_submodule_of_not_mem hf hhE
  exact not_mem_submodule_of_linearForm hEφ hvφ

end PO3Witness

section PO3Rigidity

variable {𝕜 U V : Type*}
variable [Field 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Abstract finite-window rigidity packet behind `PO3-rig.1a`:
if a sum of two rank-one maps vanishes, with one fixed nonzero functional leg
and one fixed nonzero vector leg, then the free vector factor and the free
functional factor are forced onto the corresponding singleton spans. -/
theorem po3_rankOne_companion_rigidity
    {x u : V} {φ ψ : U →ₗ[𝕜] 𝕜}
    (hφ : φ ≠ 0) (hu : u ≠ 0)
    (hzero : φ.smulRight x + ψ.smulRight u = 0) :
    x ∈ 𝕜 ∙ u ∧ ψ ∈ 𝕜 ∙ φ := by
  have hsurj : Function.Surjective φ := φ.surjective hφ
  have hx : x ∈ 𝕜 ∙ u := by
    obtain ⟨z, hz⟩ := hsurj (1 : 𝕜)
    have hz0 : x + ψ z • u = 0 := by
      simpa [LinearMap.smulRight_apply, hz] using LinearMap.congr_fun hzero z
    refine Submodule.mem_span_singleton.mpr ?_
    refine ⟨-(ψ z), ?_⟩
    simpa [neg_smul] using (eq_neg_of_add_eq_zero_left hz0).symm
  have hker : LinearMap.ker φ ≤ LinearMap.ker ψ := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have hzu : ψ z • u = 0 := by
      simpa [LinearMap.smulRight_apply, hz] using LinearMap.congr_fun hzero z
    exact (smul_eq_zero.mp hzu).resolve_right hu
  have hψ :
      ψ ∈ Submodule.span 𝕜 (Set.range fun _ : Unit => φ) := by
    apply mem_span_of_iInf_ker_le_ker
    simpa using hker
  exact ⟨hx, by simpa using hψ⟩

end PO3Rigidity

section PO3Symmetry

variable {A : Type*} [AddGroup A] [StarAddMonoid A]

/-- Abstract `PO3c`: if the `(-,+)` boundary channel is the star-symmetric
image of the `(+,-)` one, then `PO3a` forces the mirrored channel to vanish. -/
theorem po3_mirror_zero_of_symmetry
    (D_partial_pm D_partial_mp : A)
    (hsymm : D_partial_mp = star D_partial_pm)
    (hpo3a : D_partial_pm = 0) :
    D_partial_mp = 0 := by
  calc
    D_partial_mp = star D_partial_pm := hsymm
    _ = star (0 : A) := by simp [hpo3a]
    _ = 0 := by simp

/-- Filtered bulk symmetry shell: once the `(+,+)` and `(+,-)` packets are
identified, the `(-,-)` and `(-,+)` packets follow formally from star symmetry.
This is the abstract Lean version of the symmetry reduction in the filtered
bulk classifier. -/
theorem po3_filtered_bulk_symmetry_reduction
    (Mpp Mpm Mmp Mmm Qpp Qpm Qmp Qmm : A)
    (hMmm : Mmm = star Mpp)
    (hMmp : Mmp = star Mpm)
    (hQmm : Qmm = star Qpp)
    (hQmp : Qmp = star Qpm)
    (hpp : Mpp = Qpp)
    (hpm : Mpm = Qpm) :
    Mmm = Qmm ∧ Mmp = Qmp := by
  constructor
  · calc
      Mmm = star Mpp := hMmm
      _ = star Qpp := by simp [hpp]
      _ = star (star Qmm) := by simp [hQmm]
      _ = Qmm := by simp
  · calc
      Mmp = star Mpm := hMmp
      _ = star Qpm := by simp [hpm]
      _ = star (star Qmp) := by simp [hQmp]
      _ = Qmp := by simp

end PO3Symmetry

end HBridge
end Q3
