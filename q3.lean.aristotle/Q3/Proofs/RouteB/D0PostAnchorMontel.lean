import Q3.Proofs.RouteB.D0CanonicalApproximation
import Q3.Proofs.RouteB.MontelNormalFamilies

set_option linter.mathlibStandardSet false

open Complex Filter Function Set Topology Uniformity UniformConvergence
open scoped ENNReal NNReal Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB.CanonicalRHRoute

/-!
# Exact post-anchor Montel gate for the centered D0 family

Montel compactness selects a further subsequence.  The selected map is kept
inside the one canonical same-parent carrier by composing it with the existing
`CanonicalData.extract`; it is never discarded or replaced by an independent
parent path.
-/

/-- Uniform compact bounds for the raw D0 transforms on the already-selected
same-parent sequence. -/
def SelectedRawLocallyBounded
    (D : CanonicalData) : Prop :=
  ∀ K : Set ℂ, IsCompact K →
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ k : ℕ, ∀ z ∈ K,
        ‖rawFplus D.kTrial
          (D.parent (D.extract k)).1 z‖ ≤ M

/-- A uniform positive floor for the central denominators on the same selected
sequence.  Pointwise membership in `CentralIndex` alone does not give this
uniform inverse bound. -/
def SelectedCentralFloor
    (D : CanonicalData) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ k : ℕ,
      δ ≤
        ‖rawFplus D.kTrial
          (D.parent (D.extract k)).1 0‖

/-- Absorb Montel's strict subsequence into the existing extraction while
leaving the coefficient family, parent path, and its cofinality unchanged. -/
def montelRefinement
    (D : CanonicalData)
    (e : ℕ → ℕ)
    (he : StrictMono e) :
    CanonicalData :=
  { D with
    extract := D.extract ∘ e
    extractStrictMono := D.extractStrictMono.comp he }

/-- The final refined roof carrier is definitionally the Montel subsequence of
the original selected carrier. -/
@[simp] theorem selectedFamily_montelRefinement_apply
    (D : CanonicalData)
    (e : ℕ → ℕ)
    (he : StrictMono e)
    (k : ℕ)
    (z : ℂ) :
    selectedFamily
        (canonicalApproximation
          (montelRefinement D e he)) k z =
      selectedFamily
        (canonicalApproximation D) (e k) z := by
  rfl

/-- A raw compact bound and a uniform central floor give a compact bound for
the centered, central-normalized selected family. -/
theorem selectedFamily_locallyBounded_of_raw_bound_and_central_floor
    (D : CanonicalData)
    (hraw : SelectedRawLocallyBounded D)
    (hfloor : SelectedCentralFloor D) :
    ∀ K : Set ℂ, IsCompact K →
      ∃ M : ℝ, ∀ k : ℕ, ∀ z ∈ K,
        ‖selectedFamily (canonicalApproximation D) k z‖ ≤ M := by
  intro K hK
  obtain ⟨M, hMnonneg, hM⟩ := hraw K hK
  obtain ⟨δ, hδ, hδfloor⟩ := hfloor
  refine ⟨(‖centeredXi 0‖ / δ) * M, ?_⟩
  intro k z hz
  have hdenom :
      δ ≤ ‖rawFplus D.kTrial (D.parent (D.extract k)).1 0‖ :=
    hδfloor k
  have hratio :
      ‖centeredXi 0‖ /
          ‖rawFplus D.kTrial (D.parent (D.extract k)).1 0‖ ≤
        ‖centeredXi 0‖ / δ :=
    div_le_div_of_nonneg_left (norm_nonneg _) hδ hdenom
  calc
    ‖selectedFamily (canonicalApproximation D) k z‖ =
        (‖centeredXi 0‖ /
          ‖rawFplus D.kTrial (D.parent (D.extract k)).1 0‖) *
            ‖rawFplus D.kTrial (D.parent (D.extract k)).1 z‖ := by
      simp [selectedFamily, canonicalApproximation, centeredPstarFamily]
    _ ≤ (‖centeredXi 0‖ / δ) * M := by
      exact mul_le_mul hratio (hM k z hz) (norm_nonneg _)
        (div_nonneg (norm_nonneg _) hδ.le)

/-- Montel produces a nonzero strip-local cluster after its strict
subsequence is recorded in the canonical extraction itself. -/
theorem exists_refined_clusterData_of_raw_bounds
    (D : CanonicalData)
    (hXi : centeredXi 0 ≠ 0)
    (hraw : SelectedRawLocallyBounded D)
    (hfloor : SelectedCentralFloor D) :
    ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
      Nonempty
        (ClusterData
          (canonicalApproximation
            (montelRefinement D e he))) := by
  let C := canonicalApproximation D
  have hdiff : ∀ k, Differentiable ℂ (selectedFamily C k) := by
    intro k
    exact canonicalApproximation_slotH1 D (D.parent (D.extract k))
  have hbdd :
      ∀ K : Set ℂ, IsCompact K →
        ∃ M : ℝ, ∀ k : ℕ, ∀ z ∈ K,
          ‖selectedFamily C k z‖ ≤ M :=
    selectedFamily_locallyBounded_of_raw_bound_and_central_floor D hraw hfloor
  have hanchor : ∀ k, selectedFamily C k 0 = centeredXi 0 := by
    intro k
    exact centeredPstarFamily_zero D.kTrial (D.parent (D.extract k))
  obtain ⟨e, he, L, hLdiff, hconv, _hLzero, hLne⟩ :=
    Q3.RouteB.montel_anchor_nonzero_limit
      (selectedFamily C) 0 (centeredXi 0) hdiff hbdd hanchor hXi
  refine ⟨e, he, ⟨{
    limit := L
    limitHolomorphicOn := hLdiff.differentiableOn
    convergence := ?_
    limitNonzero := ?_
  }⟩⟩
  · simpa [C] using hconv.mono (subset_univ centeredCriticalStrip)
  · intro z _hz hzero
    have hLanalytic : AnalyticOnNhd ℂ L Set.univ :=
      hLdiff.differentiableOn.analyticOnNhd isOpen_univ
    have hEqOn : Set.EqOn L 0 Set.univ :=
      hLanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z) hzero
    apply hLne
    funext w
    exact hEqOn (Set.mem_univ w)

/-- Roof-facing form of the same-parent nested-extraction Montel gate.  It does
not supply `SlotS1`; it only packages the cluster after the four roof premises
are introduced. -/
theorem exists_refined_montelAnchorGate_of_raw_bounds
    (D : CanonicalData)
    (H2aAt S1At : CentralIndex D.kTrial → Prop)
    (hXi : centeredXi 0 ≠ 0)
    (hraw : SelectedRawLocallyBounded D)
    (hfloor : SelectedCentralFloor D) :
    ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
      MontelAnchorGate
        (canonicalApproximation
          (montelRefinement D e he))
        H2aAt S1At 0 := by
  obtain ⟨e, he, hcluster⟩ :=
    exists_refined_clusterData_of_raw_bounds D hXi hraw hfloor
  refine ⟨e, he, ?_⟩
  intro _hH1 _hH2a _hanchor _hS1
  exact hcluster

#print axioms selectedFamily_montelRefinement_apply
#print axioms selectedFamily_locallyBounded_of_raw_bound_and_central_floor
#print axioms exists_refined_clusterData_of_raw_bounds
#print axioms exists_refined_montelAnchorGate_of_raw_bounds

end Q3.RouteB.D0Pstar
