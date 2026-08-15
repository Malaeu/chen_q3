import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenL2SolutionCrosswalk
import Q3.Proofs.RouteB.D0Mode4SchurRootInertiaLabel
import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierSchurCount
import Mathlib.Order.Interval.Set.Infinite

/-!
# A square-summable DLMF row lies on the finite-limit even spectrum

This leaf proves only the source-to-carrier direction selected by the
2026-08-15 Goal 058 Proshka judgment.  A normalized square-summable DLMF
30.3.5 even row gives the literal characteristic equation and hence an exact
Schur root.  The simple-root inertia jump, finite-to-literal count transport,
and fixed-index finite-spectrum convergence then force that root to equal one
entry of the finite-limit classical even carrier.

The proof does not assert the converse.  In particular, it does not turn an
arbitrary finite-limit carrier value into a square-summable row or a singular
literal Schur matrix.  It also supplies no endpoint count, degree-four mode
selection, Route B promotion, or RH claim.

Knowledge preflight receipt: the exact query `Goal058 mode4 l2 root finite
limit carrier local count pinching` exited with no hits.  Strict startup then
passed `P9_STRICT_PASS` at `c0f990a9` after the required machine-local semantic
receipt refresh.
-/

open Filter Topology

namespace Q3.RouteB

noncomputable section

private def mode4RootSet (mProject K : ℕ) : Set ℝ :=
  {Λ | Λ ≤ 20 ∧ mode4RootFunction mProject K Λ = 0}

private def mode4RootInertiaLabel
    (mProject K : ℕ) (Λ : ℝ) : ℕ :=
  mode4HermitianNegativeEigenvalueCount
    (mode4HermitianSchurMatrix mProject Λ K)
    (mode4HermitianSchurMatrix_isHermitian mProject K Λ)

private theorem mode4HermitianNegativeEigenvalueCount_le_fin
    {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (hA : A.IsHermitian) :
    mode4HermitianNegativeEigenvalueCount A hA ≤ K := by
  unfold mode4HermitianNegativeEigenvalueCount
  calc
    (Finset.univ.filter fun i => hA.eigenvalues i < 0).card ≤
        Finset.univ.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = K := Fintype.card_fin K

private theorem mode4RootSet_finite
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    (mode4RootSet mProject K).Finite := by
  apply Set.Finite.of_injOn
      (f := mode4RootInertiaLabel mProject K)
      (t := Set.Iic K)
  · intro Λ hΛ
    exact mode4HermitianNegativeEigenvalueCount_le_fin
      (mode4HermitianSchurMatrix mProject Λ K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
  · intro Λ₁ hΛ₁ Λ₂ hΛ₂ heq
    exact
      (mode4RootFunction_roots_eq_iff_negativeCount_eq
        mProject K Λ₁ Λ₂ hm hK hsep
        hΛ₁.1 hΛ₂.1 hΛ₁.2 hΛ₂.2).2 heq
  · exact Set.finite_Iic K

theorem exists_mode4HermitianSchurMatrix_det_ne_zero_between
    (mProject K : ℕ) (a b : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hab : a < b)
    (hb20 : b ≤ 20) :
    ∃ Λ, a < Λ ∧ Λ < b ∧
      (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0 := by
  obtain ⟨Λ, hΛ, hΛnot⟩ :=
    (Set.Ioo_infinite hab).exists_notMem_finite
      (mode4RootSet_finite mProject K hm hK hsep)
  have hΛ20 : Λ ≤ 20 := le_trans hΛ.2.le hb20
  have hroot : mode4RootFunction mProject K Λ ≠ 0 := by
    intro hzero
    apply hΛnot
    exact ⟨hΛ20, hzero⟩
  refine ⟨Λ, hΛ.1, hΛ.2, ?_⟩
  rw [det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det
      mProject K Λ hm (by omega),
    det_mode4SchurMatrix_eq_upperProd_mul_rootFunction
      mProject K Λ hm (by omega)]
  exact mul_ne_zero (ne_of_gt (mode4JacobiUpperProd_pos mProject K hm)) hroot

private def mode4CarrierTotalDepth
    (K r : ℕ) (hrK : r < K) (d : ℕ) : {D : ℕ // r < D} :=
  ⟨K + d, by omega⟩

private theorem mode4CarrierTotalDepth_tendsto
    (K r : ℕ) (hrK : r < K) :
    Filter.Tendsto (mode4CarrierTotalDepth K r hrK)
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b.1, ?_⟩
  intro d hd
  change b.1 ≤ K + d
  omega

private theorem mode4FiniteEigenvalueAtRootIndex_tendsto
    (G : ℝ) (K r : ℕ) (hrK : r < K) (hG : 0 < G) :
    Filter.Tendsto
      (fun d : ℕ =>
        mode4DLMFEvenFiniteEigenvalue G (K + d)
          ⟨r, by omega⟩)
      Filter.atTop (nhds (mode4ClassicalEvenEigenvalue G r)) := by
  simpa [mode4CarrierTotalDepth] using
    (mode4ClassicalEvenEigenvalue_tendsto G r hG).comp
      (mode4CarrierTotalDepth_tendsto K r hrK)

private theorem mode4Card_filter_lt_ge_succ_of_monotone
    {d : ℕ} (f : Fin d → ℝ) (hf : Monotone f)
    (p : Fin d) (t : ℝ) (hpt : f p < t) :
    p.val + 1 ≤ (Finset.univ.filter fun i => f i < t).card := by
  have hsub : Finset.Iic p ⊆ Finset.univ.filter (fun i => f i < t) := by
    intro i hi
    rw [Finset.mem_Iic] at hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_of_le_of_lt (hf hi) hpt⟩
  calc
    p.val + 1 = (Finset.Iic p).card := by rw [Fin.card_Iic]
    _ ≤ (Finset.univ.filter fun i => f i < t).card :=
      Finset.card_le_card hsub

private theorem mode4Card_filter_lt_le_of_monotone
    {d : ℕ} (f : Fin d → ℝ) (hf : Monotone f)
    (p : Fin d) (t : ℝ) (htp : t ≤ f p) :
    (Finset.univ.filter fun i => f i < t).card ≤ p.val := by
  have hsub : Finset.univ.filter (fun i => f i < t) ⊆ Finset.Iio p := by
    intro i hi
    have hit := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_Iio]
    by_contra hnot
    have hpi : p ≤ i := le_of_not_gt hnot
    exact (not_lt_of_ge (le_trans htp (hf hpi))) hit
  calc
    (Finset.univ.filter fun i => f i < t).card ≤ (Finset.Iio p).card :=
      Finset.card_le_card hsub
    _ = p.val := by rw [Fin.card_Iio]

/-- A normalized square-summable even DLMF 30.3.5 left row on the production
contraction domain equals one zero-based finite-limit classical even spectral
value.  This is only the root-to-carrier direction; the converse singular
endpoint bridge is not claimed here. -/
theorem
    mode4DLMF3035EvenLeftCoefficient_sqSummable_imp_exists_finiteLimitSpectrum
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ < 20)
    (hL2 :
      Summable
        (fun q : ℕ =>
          ‖mode4DLMF3035EvenLeftCoefficient
              (mode4JacobiG mProject) Λ q‖ ^ 2)) :
    ∃ j : ℕ,
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) j = Λ := by
  let G := mode4JacobiG mProject
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  have hΛ20 : Λ ≤ 20 := hΛ.le
  have hcharacteristic :
      mode4DLMF3035EvenCharacteristicEquation G Λ (2 * (K - 1)) :=
    (mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable
      mProject K Λ hm hK hsep hΛ20).2 hL2
  have hroot : mode4RootFunction mProject K Λ = 0 :=
    (mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero
      mProject K Λ hm hK hsep hΛ20).1 hcharacteristic
  let r := mode4RootInertiaLabel mProject K Λ
  have hrK : r < K := by
    let Λhi := (Λ + 20) / 2
    have hhi : Λ < Λhi := by dsimp [Λhi]; linarith
    have hhi20 : Λhi ≤ 20 := by dsimp [Λhi]; linarith
    have hjump :=
      mode4HermitianSchurMatrix_negativeCount_succ_le_above_root
        mProject K Λ Λhi hm hK hsep hhi hhi20 hroot
    have hupper := mode4HermitianNegativeEigenvalueCount_le_fin
      (mode4HermitianSchurMatrix mProject Λhi K)
      (mode4HermitianSchurMatrix_isHermitian mProject K Λhi)
    change r + 1 ≤
      mode4HermitianNegativeEigenvalueCount
        (mode4HermitianSchurMatrix mProject Λhi K)
        (mode4HermitianSchurMatrix_isHermitian mProject K Λhi) at hjump
    omega
  refine ⟨r, le_antisymm ?_ ?_⟩
  · by_contra hnot
    have hΛcarrier : Λ < mode4ClassicalEvenEigenvalue G r :=
      lt_of_not_ge hnot
    let b := min (mode4ClassicalEvenEigenvalue G r) 20
    have hΛb : Λ < b := by
      dsimp [b]
      exact lt_min hΛcarrier hΛ
    obtain ⟨Λhi, hhi, hhib, hdet⟩ :=
      exists_mode4HermitianSchurMatrix_det_ne_zero_between
        mProject K Λ b hm hK hsep hΛb (min_le_right _ _)
    have hhi20 : Λhi ≤ 20 := le_trans hhib.le (min_le_right _ _)
    have hhiCarrier : Λhi < mode4ClassicalEvenEigenvalue G r :=
      lt_of_lt_of_le hhib (min_le_left _ _)
    have hjump :
        r + 1 ≤
          mode4HermitianNegativeEigenvalueCount
            (mode4HermitianSchurMatrix mProject Λhi K)
            (mode4HermitianSchurMatrix_isHermitian mProject K Λhi) := by
      change mode4RootInertiaLabel mProject K Λ + 1 ≤ _
      exact mode4HermitianSchurMatrix_negativeCount_succ_le_above_root
        mProject K Λ Λhi hm hK hsep hhi hhi20 hroot
    have htransport :=
      mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
        mProject K Λhi hm hK hsep hhi20 hdet
    have hfiniteCount :
        ∀ᶠ d : ℕ in Filter.atTop,
          (Finset.univ.filter fun p : Fin (K + d) =>
            mode4DLMFEvenFiniteEigenvalue G (K + d) p < Λhi).card =
          mode4HermitianNegativeEigenvalueCount
            (mode4HermitianSchurMatrix mProject Λhi K)
            (mode4HermitianSchurMatrix_isHermitian mProject K Λhi) := by
      filter_upwards [htransport] with d hd
      exact
        (mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
          mProject K d Λhi).symm.trans hd
    have hconv :=
      mode4FiniteEigenvalueAtRootIndex_tendsto G K r hrK hG
    have habove :
        ∀ᶠ d : ℕ in Filter.atTop,
          Λhi < mode4DLMFEvenFiniteEigenvalue G (K + d) ⟨r, by omega⟩ :=
      hconv.eventually_const_lt hhiCarrier
    obtain ⟨d, hdCount, hdAbove⟩ := (hfiniteCount.and habove).exists
    have hcardUpper := mode4Card_filter_lt_le_of_monotone
      (mode4DLMFEvenFiniteEigenvalue G (K + d))
      (mode4DLMFEvenFiniteEigenvalue_monotone G (K + d))
      (⟨r, by omega⟩ : Fin (K + d)) Λhi hdAbove.le
    rw [hdCount] at hcardUpper
    have hcardUpper' :
        mode4HermitianNegativeEigenvalueCount
            (mode4HermitianSchurMatrix mProject Λhi K)
            (mode4HermitianSchurMatrix_isHermitian mProject K Λhi) ≤ r := by
      simpa using hcardUpper
    omega
  · by_contra hnot
    have hcarrierΛ : mode4ClassicalEvenEigenvalue G r < Λ :=
      lt_of_not_ge hnot
    obtain ⟨Λlo, hcarrierLo, hlo, hdet⟩ :=
      exists_mode4HermitianSchurMatrix_det_ne_zero_between
        mProject K (mode4ClassicalEvenEigenvalue G r) Λ
        hm hK hsep hcarrierΛ hΛ20
    have hlo20 : Λlo ≤ 20 := le_trans hlo.le hΛ20
    have hcountLe :
        mode4HermitianNegativeEigenvalueCount
            (mode4HermitianSchurMatrix mProject Λlo K)
            (mode4HermitianSchurMatrix_isHermitian mProject K Λlo) ≤ r := by
      have hmono :=
        mode4HermitianSchurMatrix_negativeCount_add_nullity_le_of_lt
          mProject K Λlo Λ hm hK hsep hlo hΛ20
      have hmono' :
          mode4HermitianNegativeEigenvalueCount
                (mode4HermitianSchurMatrix mProject Λlo K)
                (mode4HermitianSchurMatrix_isHermitian mProject K Λlo) +
              Module.finrank ℝ
                (LinearMap.ker
                  (mode4HermitianSchurMatrix mProject Λlo K).mulVecLin) ≤ r := by
        simpa [r, mode4RootInertiaLabel] using hmono
      omega
    have htransport :=
      mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
        mProject K Λlo hm hK hsep hlo20 hdet
    have hfiniteCount :
        ∀ᶠ d : ℕ in Filter.atTop,
          (Finset.univ.filter fun p : Fin (K + d) =>
            mode4DLMFEvenFiniteEigenvalue G (K + d) p < Λlo).card =
          mode4HermitianNegativeEigenvalueCount
            (mode4HermitianSchurMatrix mProject Λlo K)
            (mode4HermitianSchurMatrix_isHermitian mProject K Λlo) := by
      filter_upwards [htransport] with d hd
      exact
        (mode4ActualFiniteJacobiTruncation_negativeCount_eq_finiteCount
          mProject K d Λlo).symm.trans hd
    have hconv :=
      mode4FiniteEigenvalueAtRootIndex_tendsto G K r hrK hG
    have hbelow :
        ∀ᶠ d : ℕ in Filter.atTop,
          mode4DLMFEvenFiniteEigenvalue G (K + d) ⟨r, by omega⟩ < Λlo :=
      hconv.eventually_lt_const hcarrierLo
    obtain ⟨d, hdCount, hdBelow⟩ := (hfiniteCount.and hbelow).exists
    have hcardLower := mode4Card_filter_lt_ge_succ_of_monotone
      (mode4DLMFEvenFiniteEigenvalue G (K + d))
      (mode4DLMFEvenFiniteEigenvalue_monotone G (K + d))
      (⟨r, by omega⟩ : Fin (K + d)) Λlo hdBelow
    rw [hdCount] at hcardLower
    have hcardLower' :
        r + 1 ≤
          mode4HermitianNegativeEigenvalueCount
            (mode4HermitianSchurMatrix mProject Λlo K)
            (mode4HermitianSchurMatrix_isHermitian mProject K Λlo) := by
      simpa using hcardLower
    omega

#print axioms
  mode4DLMF3035EvenLeftCoefficient_sqSummable_imp_exists_finiteLimitSpectrum

end

end Q3.RouteB
