import Q3.Proofs.RouteB.G6N1SelectedFerrersTrackedGroundTransform

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 4000000

open Matrix Filter
open scoped BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Goal 058 — eventual floors to one precommitted tail reindex

Verdict of 2026-08-27 (`f4243db5`).  The source supplies the complement
floor, the odd-sector floor and `ratio < 1` only EVENTUALLY, while the tracked
constructions need them at the cell in hand.  A global floor family may not be
manufactured from an eventual one, and the finite prefix may not be dropped
silently.

This node closes exactly that API seam: it returns ONE precommitted additive
shift and, at every shifted index, both decisive finite conclusions for the
pointwise tracked transform.

No second diagonal, no independently selected subsequence, no alternate shell:
the index, pair and source scale are inherited from the same selected shell by
definitional equality.
-/

/-- **The eventual-to-tail receipt.**  One additive shift `φ n = n + k₀`,
strictly monotone and cofinal, along which every hypothesis of the pointwise
tracked node holds, so that at each `φ n` the tracked transform has real zeros
and satisfies the exact pointwise tracking bound. -/
theorem selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (beta0 beta : ℝ) (hbeta0 : 0 < beta0) (hbeta : 0 < beta)
    (hmN : ∀ᶠ j in atTop,
      2 ≤ ((selectedFerrersCofinalSourceData P).index j).m ∧ 1 ≤ ((selectedFerrersCofinalSourceData P).index j).N)
    (hfloorEv : ∀ᶠ j in atTop,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index j))
        (selectedFerrersFiniteCCMRow P j)
        ((selectedFerrersFiniteCCMRayleigh P j : ℝ) : ℂ) beta)
    (hoddEv : ∀ᶠ j in atTop,
      ∀ x : CCMModeFinite ((selectedFerrersCofinalSourceData P).index j).N → ℂ,
        ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index j).N *ᵥ x = -x →
        beta0 * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index j) -
              ((selectedFerrersFiniteCCMRayleigh P j : ℝ) : ℂ) •
                (1 : Matrix (CCMModeFinite ((selectedFerrersCofinalSourceData P).index j).N)
                  (CCMModeFinite ((selectedFerrersCofinalSourceData P).index j).N) ℂ)) *ᵥ x)).re)
    (hratioEv : ∀ᶠ j in atTop,
      selectedFerrersTrackedGroundResidualFloorRatio P beta j < 1) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto φ atTop atTop ∧
      (∀ n, (selectedFerrersCofinalSourceData P).index (φ n) = (selectedFerrersCofinalSourceData P).index (φ n)) ∧
      (∀ n, (selectedFerrersCofinalSourceData P).pair (φ n) =
        (selectedFerrersCofinalSourceData P).pair (φ n)) ∧
      (∀ n, (selectedFerrersCofinalSourceData P).sourceScale (φ n) =
        (selectedFerrersCofinalSourceData P).sourceScale (φ n)) ∧
      ∀ n,
        ∃ hfloorAt :
            complexTrialComplementFloor
              (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index (φ n)))
              (selectedFerrersFiniteCCMRow P (φ n))
              ((selectedFerrersFiniteCCMRayleigh P (φ n) : ℝ) : ℂ) beta,
          ZerosRealOn Set.univ
            (selectedFerrersTrackedGroundTransformAt P (φ n) beta hfloorAt) ∧
          ∀ z : ℂ,
            ‖selectedFerrersTrackedGroundTransformAt P (φ n) beta hfloorAt z -
                (selectedFerrersCofinalSourceData P).centeredPstar (φ n) z‖ ≤
              ‖centeredXi 0 /
                (selectedFerrersCofinalSourceData P).rawFplus (φ n) 0‖ *
                sourceOrderedCCMKernelL2
                  (logLength ((selectedFerrersCofinalSourceData P).index (φ n)))
                  ((selectedFerrersCofinalSourceData P).index (φ n)).N z *
                Real.sqrt
                  (selectedFerrersTrackedGroundResidualFloorRatio P beta (φ n)) := by
  classical
  obtain ⟨a1, h1⟩ := eventually_atTop.1 hmN
  obtain ⟨a2, h2⟩ := eventually_atTop.1 hfloorEv
  obtain ⟨a3, h3⟩ := eventually_atTop.1 hoddEv
  obtain ⟨a4, h4⟩ := eventually_atTop.1 hratioEv
  set k0 : ℕ := max (max a1 a2) (max a3 a4) with hk0
  refine ⟨fun n => n + k0, ?_, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro p q hpq
    exact Nat.add_lt_add_right hpq k0
  · exact Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n k0) tendsto_id
  · intro n
    have hge1 : a1 ≤ n + k0 := by
      have : a1 ≤ k0 := le_trans (le_max_left a1 a2) (le_max_left _ _)
      omega
    have hge2 : a2 ≤ n + k0 := by
      have : a2 ≤ k0 := le_trans (le_max_right a1 a2) (le_max_left _ _)
      omega
    have hge3 : a3 ≤ n + k0 := by
      have : a3 ≤ k0 := le_trans (le_max_left a3 a4) (le_max_right _ _)
      omega
    have hge4 : a4 ≤ n + k0 := by
      have : a4 ≤ k0 := le_trans (le_max_right a3 a4) (le_max_right _ _)
      omega
    obtain ⟨hm, hN⟩ := h1 (n + k0) hge1
    refine ⟨h2 (n + k0) hge2, ?_⟩
    exact
      selectedFerrersTrackedGroundTransformAt_realZeros_and_pointwiseTracking_of_sectorFloors
        P (n + k0) beta0 beta hbeta0 hbeta hm hN
        (h3 (n + k0) hge3) (h2 (n + k0) hge2) (h4 (n + k0) hge4)

#print axioms selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors

end Q3.RouteB.D0Pstar
