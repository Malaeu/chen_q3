import RequestProject.Main

open Complex Filter Topology

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace RHRoute.ProjectApprox

/-!
# Layer B: the one canonical approximation family

This statements-only file is the instantiation layer missing from `Main.lean`.
It does not quantify supply over an arbitrary `Approx`: every open supply leaf
below targets the single `Pstar D` built from source-locked D0 data.

The D0-to-Lean crosswalk is intentionally explicit data.  Constructing this
data from the concrete D0.1/D0.6/D0.7 objects is an open obligation and must
not be replaced by a second abstract approximation family.
-/

/-- The exact D0 ingredients needed to form the canonical roof family.

`rawTransform` is the D0.6 transform family, `completionGauge` is the fixed
zero-free SOFT completion, and `anchorScale` is the D0.7 central/anchor
normalizer. -/
structure D0CanonicalApproxData where
  rawTransform : ℕ → ℂ → ℂ
  completionGauge : ℕ → ℂ → ℂ
  anchorScale : ℕ → ℂ
  completionGaugeUnit : ∀ j, IsUnitOnS (completionGauge j)
  anchorScaleNe : ∀ j, anchorScale j ≠ 0

/-- The unique canonical approximation object selected before any supply
lemma is attempted. -/
def Pstar (D : D0CanonicalApproxData) : Approx where
  F := D.rawTransform
  gamma := D.completionGauge
  a := D.anchorScale
  gamma_unit := D.completionGaugeUnit
  a_ne := D.anchorScaleNe

/-- Exact penalty/coercivity pilots for every selected cell.  Each bundled
`PencilData` already contains its `β_j`, `τ_j`, strict `a_j < β_j`, and PSD
certificate; `bridge` pins it to the same `Pstar`. -/
structure PenaltyPilotFamily (D : D0CanonicalApproxData) where
  pencil : ℕ → PencilData
  bridge : ∀ j, Nonempty (PencilBridge (Pstar D) j (pencil j))

/-- Registered penalty threshold of the `j`-th pilot. -/
def penaltyBeta {D : D0CanonicalApproxData}
    (P : PenaltyPilotFamily D) (j : ℕ) : ℝ :=
  (P.pencil j).β

/-- Registered penalty weight of the `j`-th pilot. -/
def penaltyTau {D : D0CanonicalApproxData}
    (P : PenaltyPilotFamily D) (j : ℕ) : ℝ :=
  (P.pencil j).τ

/-- A complete penalty pilot supplies H2a for `Pstar` without any universal
`∀ P` statement. -/
theorem supply_H2a_Pstar_of_penaltyPilot
    (D : D0CanonicalApproxData) (P : PenaltyPilotFamily D) :
    SlotH2a (Pstar D) := by
  intro j
  exact ⟨P.pencil j, P.bridge j⟩

/-- Diagnostic schema only.  A numerical anchor probe is not a proof of the
exact anchor equation; promotion requires a separate exact theorem. -/
structure AnchorValueProbeRecord (D : D0CanonicalApproxData) where
  cell : ℕ
  observed : ℂ
  expected : ℂ
  absoluteError : ℝ
  tolerance : ℝ
  tolerancePos : 0 < tolerance
  observed_eq : observed = Hfam (Pstar D) cell anchor
  expected_eq : expected = Xi anchor
  diagnosticPass : absoluteError ≤ tolerance

/-! The four remaining leaves are frozen as one statements-only contract.

Crucially, this file does **not** assert that every value of
`D0CanonicalApproxData` satisfies the leaves.  An instance of this contract
must be constructed for the one source-locked D0 value.  The projection
lemmas below merely give stable names to the four fields.  S2 must retain the
Round-13 same-cofinal-subsequence guard in that eventual construction. -/

structure PstarSupplyContract (D : D0CanonicalApproxData) : Prop where
  h1 : SlotH1 (Pstar D)
  anchor : SlotAnchor (Pstar D)
  s1 : SlotS1 (Pstar D)
  s2 : SlotS2 (Pstar D)

theorem supply_H1_Pstar (D : D0CanonicalApproxData)
    (C : PstarSupplyContract D) : SlotH1 (Pstar D) :=
  C.h1

theorem supply_anchor_Pstar (D : D0CanonicalApproxData)
    (C : PstarSupplyContract D) : SlotAnchor (Pstar D) :=
  C.anchor

theorem supply_S1_Pstar (D : D0CanonicalApproxData)
    (C : PstarSupplyContract D) : SlotS1 (Pstar D) :=
  C.s1

theorem supply_S2_Pstar (D : D0CanonicalApproxData)
    (C : PstarSupplyContract D) : SlotS2 (Pstar D) :=
  C.s2

#check Pstar
#check supply_H2a_Pstar_of_penaltyPilot
#check AnchorValueProbeRecord
#check PstarSupplyContract

#print axioms supply_H2a_Pstar_of_penaltyPilot
#print axioms supply_H1_Pstar
#print axioms supply_anchor_Pstar
#print axioms supply_S1_Pstar
#print axioms supply_S2_Pstar

end RHRoute.ProjectApprox
