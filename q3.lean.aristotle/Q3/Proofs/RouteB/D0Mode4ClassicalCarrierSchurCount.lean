import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierFromFiniteLimit
import Q3.Proofs.RouteB.D0Mode4FiniteToLiteralNegativeCount

/-!
# Classical-carrier count transported to the literal Schur matrix

This file composes the finite DLMF count with the accepted finite-to-literal
Schur inertia transport.  Its hypotheses retain the strict carrier separator,
the finite-tail separation, the endpoint upper bound, and Schur
nonsingularity as distinct facts.  It supplies no endpoint count, no
semiclassical separator, and no differential-eigenfunction identification.
-/

open Filter Topology

noncomputable section

private abbrev mode4SchurDepth (K N : ℕ) := {d : ℕ // N < K + d}

private instance (K N : ℕ) : Nonempty (mode4SchurDepth K N) :=
  ⟨⟨N + 1, by omega⟩⟩

private theorem mode4SchurDepth_val_tendsto
    (K N : ℕ) :
    Filter.Tendsto (fun d : mode4SchurDepth K N => d.1)
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  let i : mode4SchurDepth K N :=
    ⟨max (N + 1) b, by omega⟩
  refine ⟨i, ?_⟩
  intro a ha
  change i.1 ≤ a.1 at ha
  exact le_trans (le_max_right (N + 1) b) ha

private def mode4SchurTotalDepth (K N : ℕ) :
    mode4SchurDepth K N → {D : ℕ // N < D} :=
  fun d => ⟨K + d.1, d.2⟩

private theorem mode4SchurTotalDepth_tendsto
    (K N : ℕ) :
    Filter.Tendsto (mode4SchurTotalDepth K N)
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  let i : mode4SchurDepth K N :=
    ⟨max (N + 1) b.1, by omega⟩
  refine ⟨i, ?_⟩
  intro a ha
  change i.1 ≤ a.1 at ha
  change b.1 ≤ K + a.1
  exact le_trans (le_max_right (N + 1) b.1) (le_trans ha (Nat.le_add_left _ _))

/-- Once the carrier threshold is separated, the literal Schur negative count
equals the corresponding finite classical-carrier head count.  This is the H6
composition seam; numerical endpoint counts remain downstream. -/
theorem mode4HermitianSchurMatrix_negativeCount_eq_classicalHeadCount
    (mProject K N : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hfiniteTail :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hdet : (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0)
    (hG : 0 < mode4JacobiG mProject)
    (hcarrierSep :
      ∀ p < N, mode4ClassicalEvenEigenvalue
        (mode4JacobiG mProject) p ≠ Λ)
    (hcarrierTail :
      Λ < mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) N) :
    mode4HermitianNegativeEigenvalueCount
        (mode4HermitianSchurMatrix mProject Λ K)
        (mode4HermitianSchurMatrix_isHermitian mProject K Λ) =
      ((Finset.range N).filter fun p =>
        mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p < Λ).card := by
  let S := mode4SchurDepth K N
  let carrierCount :=
    ((Finset.range N).filter fun p =>
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p < Λ).card
  let schurCount :=
    mode4HermitianNegativeEigenvalueCount
      (mode4HermitianSchurMatrix mProject Λ K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
  have hfinite :=
    mode4DLMFEvenFiniteCount_eventually_eq_classicalHeadCount
      (mode4JacobiG mProject) Λ N hG hcarrierSep hcarrierTail
  have hfinite' :
      ∀ᶠ d : S in Filter.atTop,
        (Finset.univ.filter fun p : Fin (K + d.1) =>
          mode4DLMFEvenFiniteEigenvalue
            (mode4JacobiG mProject) (K + d.1) p < Λ).card = carrierCount := by
    have hpulled :=
      (mode4SchurTotalDepth_tendsto K N).eventually hfinite
    simpa [S, mode4SchurTotalDepth, carrierCount] using hpulled
  have hactualCarrier :
      ∀ᶠ d : S in Filter.atTop,
        mode4HermitianNegativeEigenvalueCount
            (mode4ActualFiniteJacobiTruncation mProject Λ K d.1)
            (mode4ActualFiniteJacobiTruncation_isHermitian
              mProject Λ K d.1) = carrierCount := by
    filter_upwards [hfinite'] with d hd
    exact
      (mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
        mProject K d.1 Λ).trans hd
  have hschur :=
    mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
      mProject K Λ hm hK hfiniteTail hΛ hdet
  have hschur' :
      ∀ᶠ d : S in Filter.atTop,
        mode4HermitianNegativeEigenvalueCount
            (mode4ActualFiniteJacobiTruncation mProject Λ K d.1)
            (mode4ActualFiniteJacobiTruncation_isHermitian
              mProject Λ K d.1) = schurCount := by
    have hpulled := (mode4SchurDepth_val_tendsto K N).eventually hschur
    simpa [S, schurCount] using hpulled
  have heq : ∀ᶠ _d : S in Filter.atTop, schurCount = carrierCount := by
    filter_upwards [hactualCarrier, hschur'] with d hdCarrier hdSchur
    exact hdSchur.symm.trans hdCarrier
  simpa [schurCount, carrierCount] using heq.exists

/-- A strict carrier window turns the H6 head count into the literal natural
number `N`.  Both sides of the window remain explicit hypotheses; this lemma
does not manufacture a semiclassical separator. -/
theorem mode4HermitianSchurMatrix_negativeCount_eq_of_classicalWindow
    (mProject K N : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hfiniteTail :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hdet : (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0)
    (hG : 0 < mode4JacobiG mProject)
    (hhead :
      ∀ p < N, mode4ClassicalEvenEigenvalue
        (mode4JacobiG mProject) p < Λ)
    (htail :
      Λ < mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) N) :
    mode4HermitianNegativeEigenvalueCount
        (mode4HermitianSchurMatrix mProject Λ K)
        (mode4HermitianSchurMatrix_isHermitian mProject K Λ) = N := by
  have hcount :=
    mode4HermitianSchurMatrix_negativeCount_eq_classicalHeadCount
      mProject K N Λ hm hK hfiniteTail hΛ hdet hG
      (fun p hp => (hhead p hp).ne) htail
  have hfilter :
      (Finset.range N).filter (fun p =>
          mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) p < Λ) =
        Finset.range N := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact hhead p (Finset.mem_range.mp hp)
  rw [hcount, hfilter, Finset.card_range]

#print axioms mode4HermitianSchurMatrix_negativeCount_eq_classicalHeadCount
#print axioms mode4HermitianSchurMatrix_negativeCount_eq_of_classicalWindow

end
