import Q3.Proofs.RouteB.ClassicalXiInterface
import Q3.Proofs.RouteB.GenericZeroTransfer
import Q3.Proofs.RouteB.SoftL2Round13Integration

set_option linter.mathlibStandardSet false

open Filter Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.CanonicalRHRoute

/-!
# Fail-closed canonical Route-B roof

This file repairs the quantifiers in the Aristotle draft recovered on 2026-07-22.
There is one fixed approximation family `Pstar`; none of the supply statements
is quantified over an arbitrary family.  `H2aAt` and `S1At` are deliberately
abstract predicates so that the logical roof can typecheck without pretending
that the concrete `(m,N)` instantiation has been proved.

The finite simple/even ground certificate and the real-zero conclusion are
separated by `Theorem510RealZeroBridge`.  In particular, evenness is not used as
a substitute for the determinant/self-adjoint factorization of Theorem 5.10.
-/

/-- The one approximation family selected by the construction. -/
structure ApproximationFamily (Index : Type*) where
  family : Index → ℂ → ℂ

/-- A fixed canonical family together with one parent cofinal path and the
nested extraction which `S2` is allowed to consume. -/
structure CanonicalApproximation (Index : Type*) where
  Pstar : ApproximationFamily Index
  parent : ℕ → Index
  parentCofinal : Prop
  parentCofinalProof : parentCofinal
  extract : ℕ → ℕ
  extractStrictMono : StrictMono extract

/-- The family on the single nested subsequence fixed by the construction. -/
def selectedFamily {Index : Type*} (C : CanonicalApproximation Index) : ℕ → ℂ → ℂ :=
  fun k => C.Pstar.family (C.parent (C.extract k))

/-- Entire holomorphy of the fixed family.  This stronger whole-plane form is
the exact input consumed by the already-checked generic Hurwitz theorem. -/
def SlotH1 {Index : Type*} (C : CanonicalApproximation Index) : Prop :=
  ∀ i, Differentiable ℂ (C.Pstar.family i)

/-- `H2a` lives only on the one parent cofinal path. -/
def SlotH2a {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt : Index → Prop) : Prop :=
  ∀ k, H2aAt (C.parent k)

/-- Anchor normalization for the fixed family. -/
def SlotAnchor {Index : Type*} (C : CanonicalApproximation Index)
    (anchor : ℂ) : Prop :=
  ∀ i, C.Pstar.family i anchor = centeredXi anchor

/-- `S1` is required on the same parent path as `H2a`. -/
def SlotS1 {Index : Type*} (C : CanonicalApproximation Index)
    (S1At : Index → Prop) : Prop :=
  ∀ k, S1At (C.parent k)

/-- Materialize the Round-13 same-subsequence guard from the two parent-path
slots.  The resulting S2 carrier is definitionally
`parent (extract k)`; no independent diagonal can enter. -/
def sameCofinalGuard {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop)
    (hH2a : SlotH2a C H2aAt) (hS1 : SlotS1 C S1At) :
    SoftSameCofinalSubsequence Index H2aAt S1At where
  parent := C.parent
  parentCofinal := C.parentCofinal
  h2aOnParent := hH2a
  s1OnParent := hS1
  extract := C.extract
  extractStrictMono := C.extractStrictMono

@[simp] theorem sameCofinalGuard_s2Sequence
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop)
    (hH2a : SlotH2a C H2aAt) (hS1 : SlotS1 C S1At) :
    (sameCofinalGuard C H2aAt S1At hH2a hS1).s2Sequence =
      fun k => C.parent (C.extract k) := rfl

/-- The centered critical strip is open. -/
theorem isOpen_centeredCriticalStrip : IsOpen centeredCriticalStrip := by
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-- Output of the Montel-plus-anchor gate on the guarded selected family.
Every analytic and convergence field is restricted to the only domain used by
the RH transfer.  `limitNonzero` is local nontriviality, the exact form needed
by isolated-zero theory on that domain. -/
structure ClusterData {Index : Type*} (C : CanonicalApproximation Index) where
  limit : ℂ → ℂ
  limitHolomorphicOn : DifferentiableOn ℂ limit centeredCriticalStrip
  convergence :
    TendstoLocallyUniformlyOn (selectedFamily C) limit atTop centeredCriticalStrip
  limitNonzero :
    ∀ z ∈ centeredCriticalStrip, ¬ ∀ᶠ w in 𝓝 z, limit w = 0

/-- The exact interface to be proved from `H1 + H2a + ANCHOR + S1`.
It returns a cluster only on the already-fixed nested sequence. -/
def MontelAnchorGate {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop) (anchor : ℂ) : Prop :=
  SlotH1 C → SlotH2a C H2aAt → SlotAnchor C anchor → SlotS1 C S1At →
    Nonempty (ClusterData C)

/-- Full Theorem-5.10 interface.  This is intentionally a separate input:
`H2aAt i` alone does not produce real zeros.  A concrete implementation must
contain the determinant identity, the modified-Hilbert self-adjoint descent,
the complement/lattice factor, and the nonvanishing phase. -/
def Theorem510RealZeroBridge {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt : Index → Prop) : Prop :=
  ∀ i, H2aAt i → Differentiable ℂ (C.Pstar.family i) →
    ZerosRealOn Set.univ (C.Pstar.family i)

/-- `S2` identifies the nonzero cluster produced on the same selected family.
The multiplier is a nonzero scalar times a zero-free gauge on the centered
critical strip. -/
def SlotS2 {Index : Type*} (C : CanonicalApproximation Index) : Prop :=
  ∀ D : ClusterData C,
    ∃ c : ℂ, ∃ gamma : ℂ → ℂ,
      c ≠ 0 ∧
      (∀ z ∈ centeredCriticalStrip, gamma z ≠ 0) ∧
      (∀ z ∈ centeredCriticalStrip,
        D.limit z = c * centeredXi z * gamma z)

/-- The derived H2b statement on the selected sequence. -/
theorem selectedFamily_realZeros
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt : Index → Prop)
    (hH1 : SlotH1 C)
    (hH2a : SlotH2a C H2aAt)
    (h510 : Theorem510RealZeroBridge C H2aAt) :
    ∀ k, ZerosRealOn Set.univ (selectedFamily C k) := by
  intro k
  exact h510 (C.parent (C.extract k)) (hH2a (C.extract k))
    (hH1 (C.parent (C.extract k)))

/-- Conditional roof assembly for the one canonical family.  All analytic
gaps occur as named inputs; the proof itself is hole-free and composes the
checked generic Hurwitz transfer with the classical Xi/RH interface. -/
theorem rh_of_canonical_strip_slots
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop) (anchor : ℂ)
    (hH1 : SlotH1 C)
    (hH2a : SlotH2a C H2aAt)
    (hanchor : SlotAnchor C anchor)
    (hS1 : SlotS1 C S1At)
    (hMontel : MontelAnchorGate C H2aAt S1At anchor)
    (h510 : Theorem510RealZeroBridge C H2aAt)
    (hS2 : SlotS2 C) :
    Q3.RH := by
  obtain ⟨D⟩ := hMontel hH1 hH2a hanchor hS1
  have hselectedZeros : ∀ k, ZerosRealOn Set.univ (selectedFamily C k) :=
    selectedFamily_realZeros C H2aAt hH1 hH2a h510
  have happroach :
      ZerosApproachOn centeredCriticalStrip (selectedFamily C) D.limit :=
    zerosApproachOn_of_tendstoLocallyUniformlyOn_local
      isOpen_centeredCriticalStrip (fun _ hz => hz)
      (fun k => hH1 (C.parent (C.extract k))) D.limitHolomorphicOn
      D.convergence D.limitNonzero
  have hlimitZeros : ZerosRealOn centeredCriticalStrip D.limit :=
    zerosRealOn_of_zerosApproachOn centeredCriticalStrip
      (selectedFamily C) D.limit hselectedZeros happroach
  rcases hS2 D with ⟨c, gamma, hc, hgamma, hidentify⟩
  apply rh_iff_centeredXi_zeros_real.mpr
  intro z hzXi hzstrip
  apply hlimitZeros z hzstrip
  rw [hidentify z hzstrip, hzXi]
  simp

/-- Compatibility name for older conditional consumers.  The implementation
is now strip-local; it does not restore a `Set.univ` convergence hypothesis. -/
theorem rh_of_canonical_slots
    {Index : Type*} (C : CanonicalApproximation Index)
    (H2aAt S1At : Index → Prop) (anchor : ℂ)
    (hH1 : SlotH1 C)
    (hH2a : SlotH2a C H2aAt)
    (hanchor : SlotAnchor C anchor)
    (hS1 : SlotS1 C S1At)
    (hMontel : MontelAnchorGate C H2aAt S1At anchor)
    (h510 : Theorem510RealZeroBridge C H2aAt)
    (hS2 : SlotS2 C) :
    Q3.RH :=
  rh_of_canonical_strip_slots C H2aAt S1At anchor hH1 hH2a hanchor hS1
    hMontel h510 hS2

/-! ## Plant: evenness is not the Theorem-5.10 bridge -/

/-- The standard even entire function with nonreal zeros. -/
def evenNonrealZeroPlant (z : ℂ) : ℂ := z ^ 2 + 1

theorem evenNonrealZeroPlant_even :
    ∀ z : ℂ, evenNonrealZeroPlant (-z) = evenNonrealZeroPlant z := by
  intro z
  simp [evenNonrealZeroPlant]

theorem evenNonrealZeroPlant_not_realZeros :
    ¬ ZerosRealOn Set.univ evenNonrealZeroPlant := by
  intro h
  have hI : evenNonrealZeroPlant Complex.I = 0 := by
    simp [evenNonrealZeroPlant, pow_two]
  have := h Complex.I (Set.mem_univ _) hI
  norm_num at this

theorem evenness_alone_does_not_imply_real_zeros :
    (∀ z : ℂ, evenNonrealZeroPlant (-z) = evenNonrealZeroPlant z) ∧
      ¬ ZerosRealOn Set.univ evenNonrealZeroPlant :=
  ⟨evenNonrealZeroPlant_even, evenNonrealZeroPlant_not_realZeros⟩

#check sameCofinalGuard
#check Theorem510RealZeroBridge
#check rh_of_canonical_strip_slots
#check rh_of_canonical_slots

#print axioms sameCofinalGuard_s2Sequence
#print axioms selectedFamily_realZeros
#print axioms rh_of_canonical_strip_slots
#print axioms rh_of_canonical_slots
#print axioms evenness_alone_does_not_imply_real_zeros

end Q3.RouteB.CanonicalRHRoute
