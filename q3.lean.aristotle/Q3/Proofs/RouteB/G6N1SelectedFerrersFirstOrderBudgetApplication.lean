import Q3.Proofs.RouteB.G6N1SelectedFerrersMidpointDeltaEnvelope
import Q3.Proofs.RouteB.G6N1SelectedFerrersW5DerivativeBudgetRate
import Q3.Proofs.RouteB.D0PstarFirstOrderProjectionTailReceiver

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Complex Filter MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Application: selected projection-tail decay from the W5 first-order budget

Ratified shape (verdict d00dbbbb, option b1): the family identification is an
EXPLICIT owner contract, never a schedule-notation pun and never a second
constructed source.  Everything else is already kernel-green: the generic
receiver (1d9caa75), the universal coefficient crosswalk and W4-fed envelope
(c082e070), and the midpoint-delta envelope (26d0449f).
-/

/--
**The explicit owner family contract** (b1).  Exactly the equalities needed
to transport the W5 first-order envelope to the production consumer: the
selected index and the selected trial agree, eventually in `k`.
-/
def SelectedFerrersPreAnchorProductionFamilyCrosswalk
    (S : ProlateCanonicalSourceData) : Prop :=
  ∀ᶠ k : ℕ in atTop,
    selectedPairIndex S k = selectedFerrersPreAnchorIndex k ∧
    selectedProlateTrial S k =
      prolateCombination (selectedFerrersPreAnchorPair k)

private theorem w5a_coeff_transport
    {i i' : PairIndex} (hii : i = i')
    {h h' : ℝ → ℂ} (hhh : h = h')
    (w : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (w' : MemLp (E_star h') 2 (dStar.restrict (I_m i')))
    (n : ℤ) :
    physicalFourierCoefficient i (gTrial_m i h w) n =
      physicalFourierCoefficient i' (gTrial_m i' h' w') n := by
  subst hii
  subst hhh
  rfl

private theorem w5a_eStar_scale (k : ℕ) (u : ℝ) :
    E_star (selectedFerrersLemma73SourcePacket k) u =
      selectedFerrersLemma73SourceScale k *
        E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u := by
  unfold E_star selectedFerrersLemma73SourcePacket
  rw [tsum_mul_left]
  ring

private theorem w5a_gTrial_eq_smul (k : ℕ) :
    gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k) =
      (selectedFerrersLemma73SourceScale k)⁻¹ • selectedFerrersEStarHm k := by
  set i := selectedFerrersPreAnchorIndex k with hi
  have hcne : selectedFerrersLemma73SourceScale k ≠ 0 :=
    selectedFerrersLemma73SourceScale_ne k
  apply MeasureTheory.Lp.ext
  have h1 : (gTrial_m i
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
      E_star (prolateCombination (selectedFerrersPreAnchorPair k)) :=
    MemLp.coeFn_toLp _
  have h2 : (selectedFerrersEStarHm k : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
      E_star (selectedFerrersLemma73SourcePacket k) :=
    MemLp.coeFn_toLp (w5m_eStar_memLp k)
  have hsmul := MeasureTheory.Lp.coeFn_smul
    ((selectedFerrersLemma73SourceScale k)⁻¹) (selectedFerrersEStarHm k)
  filter_upwards [h1, h2, hsmul] with u hu1 hu2 hu3
  rw [hu1, hu3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hu2, w5a_eStar_scale k u]
  field_simp

/-- Local clone of the private center bound: `H(0) = 0`, so the F72.6 window
rate at the origin bounds the packet's central value. -/
private theorem w5a_center_bound
    {C : ℝ}
    (hrate : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) x -
          (4 : ℂ) * explicitCCMLimitH x‖ ≤
            C / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k in Filter.atTop,
      ‖selectedFerrersLemma73SourcePacket k 0‖ ≤
        C / (selectedFerrersPaperLambda k) ^ 2 := by
  filter_upwards [hrate] with k hk
  have hlam : 0 ≤ selectedFerrersPaperLambda k := Real.sqrt_nonneg _
  have hmem : (0 : ℝ) ∈ Set.Icc (-(selectedFerrersPaperLambda k))
      (selectedFerrersPaperLambda k) := ⟨by linarith, hlam⟩
  have h := hk 0 hmem
  have hH0 : explicitCCMLimitH 0 = 0 := by
    rw [explicitCCMLimitH]
    norm_num
  rw [hH0, mul_zero, sub_zero] at h
  exact h

private theorem w5a_paperLambda_one_le (k : ℕ) :
    (1 : ℝ) ≤ selectedFerrersPaperLambda k := by
  apply Real.one_le_sqrt.mpr
  have : (1 : ℕ) ≤ k + 2 := Nat.le_add_left 1 (k + 1)
  exact_mod_cast this

/--
**The b1 application theorem.**  Given the explicit family contract, the
F72.6 mode/chi rates, the open derivative-budget supplier, the scale
inverse bound and cofinal bandwidth, the production selected projection
tail decays.  `SelectedPhysicalFourierEnergyControl` is nowhere required.
-/
theorem selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget
    (S : ProlateCanonicalSourceData)
    (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S)
    (C0 C4 Cχ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hmode :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 x -
            ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hD : ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ k in Filter.atTop,
        selectedFerrersAbelLogDerivativeBudget k ≤ D)
    (hScale : ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ k in Filter.atTop,
        ‖(selectedFerrersLemma73SourceScale k)⁻¹‖ ≤ M)
    (hBandwidth : SelectedPhysicalBandwidthCofinal S) :
    SelectedProjectionTailDecay S := by
  obtain ⟨Cb, hCb0, hCb⟩ :=
    selectedFerrersAbelFourierDecayBudget_bounded_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ hD
  obtain ⟨Cp, hCp0, hCpRate⟩ :=
    selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hCenter := w5a_center_bound hCpRate
  obtain ⟨M, hM0, hM⟩ := hScale
  have hpi := Real.pi_pos
  apply selectedProjectionTailDecay_of_firstOrderCoefficientBudgetAndBandwidth
    S ?_ hBandwidth
  refine ⟨M * (Cb + Cp / (4 * Real.pi)), by positivity, ?_⟩
  filter_upwards [hFamily, hCb, hCenter, hM] with k hkF hkB hkC hkM
  obtain ⟨hidx, htrial⟩ := hkF
  intro n hn
  set i' := selectedFerrersPreAnchorIndex k with hi'
  have hnPre : n ∉ modeSet i' := by
    rw [← hidx]
    exact hn
  have hn0 : n ≠ 0 := by
    intro h0
    apply hnPre
    rw [h0]
    simp only [modeSet, Finset.mem_Icc]
    omega
  have hL' : 0 < L_m i' := logLength_pos i'
  have hLeq : L_m (selectedPairIndex S k) = L_m i' := by
    rw [hidx]
  have hcoeffEq :
      physicalFourierCoefficient (selectedPairIndex S k)
        (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
          (S.source.eStar_memLp (selectedPairIndex S k))) n =
      physicalFourierCoefficient i'
        (gTrial_m i' (prolateCombination (selectedFerrersPreAnchorPair k))
          (selectedFerrersPreAnchorPair_eStar_memLp k)) n :=
    w5a_coeff_transport hidx htrial _ _ n
  have hnormEq :
      ‖physicalFourierCoefficient i'
        (gTrial_m i' (prolateCombination (selectedFerrersPreAnchorPair k))
          (selectedFerrersPreAnchorPair_eStar_memLp k)) n‖ =
      ‖(selectedFerrersLemma73SourceScale k)⁻¹‖ *
        ‖physicalFourierCoefficient i' (selectedFerrersEStarHm k) n‖ := by
    rw [w5a_gTrial_eq_smul k]
    simp only [physicalFourierCoefficient]
    rw [inner_smul_right, norm_mul]
  have henv := selectedFerrersEStarHm_physicalCoefficient_le k n hn0
  -- combined-constant bound
  have hlameq := selectedFerrersPaperLambda_eq_lambda_m k
  have hlam1 := w5a_paperLambda_one_le k
  have hlam0 : (0 : ℝ) < selectedFerrersPaperLambda k := by linarith
  have hsqrt_le :
      Real.sqrt (lambda_m i') ≤ (selectedFerrersPaperLambda k) ^ 2 := by
    rw [← hlameq]
    have h1 : Real.sqrt (selectedFerrersPaperLambda k) ≤
        Real.sqrt ((selectedFerrersPaperLambda k) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [Real.sqrt_sq hlam0.le] at h1
    calc
      Real.sqrt (selectedFerrersPaperLambda k) ≤
          selectedFerrersPaperLambda k := h1
      _ ≤ (selectedFerrersPaperLambda k) ^ 2 := by nlinarith
  have hcenterProd :
      ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m i') ≤ Cp := by
    calc
      ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m i') ≤
        (Cp / (selectedFerrersPaperLambda k) ^ 2) *
          (selectedFerrersPaperLambda k) ^ 2 := by
          apply mul_le_mul hkC hsqrt_le (Real.sqrt_nonneg _)
          positivity
      _ = Cp := by
          field_simp
  have hcomb :
      selectedFerrersAbelFourierDecayBudget k +
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m i') / (4 * Real.pi) ≤
      Cb + Cp / (4 * Real.pi) := by
    apply add_le_add hkB
    apply div_le_div_of_nonneg_right hcenterProd
    positivity
  have hcombNonneg :
      (0 : ℝ) ≤ selectedFerrersAbelFourierDecayBudget k +
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m i') / (4 * Real.pi) := by
    have := selectedFerrersAbelFourierDecayBudget_nonneg k
    positivity
  have hnabs : (0 : ℝ) < |(n : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hn0
  -- norm-level chain
  have hnormFinal :
      ‖physicalFourierCoefficient (selectedPairIndex S k)
        (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
          (S.source.eStar_memLp (selectedPairIndex S k))) n‖ ≤
      M * (Cb + Cp / (4 * Real.pi)) * Real.sqrt (L_m i') / |(n : ℝ)| := by
    rw [hcoeffEq, hnormEq]
    calc
      ‖(selectedFerrersLemma73SourceScale k)⁻¹‖ *
          ‖physicalFourierCoefficient i' (selectedFerrersEStarHm k) n‖
          ≤ M * ((selectedFerrersAbelFourierDecayBudget k +
              ‖selectedFerrersLemma73SourcePacket k 0‖ *
                Real.sqrt (lambda_m i') / (4 * Real.pi)) *
              Real.sqrt (L_m i') / |(n : ℝ)|) := by
            apply mul_le_mul hkM henv (norm_nonneg _) hM0
      _ ≤ M * ((Cb + Cp / (4 * Real.pi)) *
              Real.sqrt (L_m i') / |(n : ℝ)|) := by
            apply mul_le_mul_of_nonneg_left _ hM0
            apply div_le_div_of_nonneg_right _ hnabs.le
            exact mul_le_mul_of_nonneg_right hcomb (Real.sqrt_nonneg _)
      _ = M * (Cb + Cp / (4 * Real.pi)) * Real.sqrt (L_m i') / |(n : ℝ)| := by
            ring
  -- squared receiver form
  have hCfin0 : (0 : ℝ) ≤ M * (Cb + Cp / (4 * Real.pi)) := by positivity
  rw [hLeq]
  calc
    ‖physicalFourierCoefficient (selectedPairIndex S k)
        (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
          (S.source.eStar_memLp (selectedPairIndex S k))) n‖ ^ 2
        ≤ (M * (Cb + Cp / (4 * Real.pi)) *
            Real.sqrt (L_m i') / |(n : ℝ)|) ^ 2 := by
          apply sq_le_sq' _ hnormFinal
          have : (0 : ℝ) ≤ M * (Cb + Cp / (4 * Real.pi)) *
              Real.sqrt (L_m i') / |(n : ℝ)| := by positivity
          have hnn : (0 : ℝ) ≤ ‖physicalFourierCoefficient (selectedPairIndex S k)
              (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
                (S.source.eStar_memLp (selectedPairIndex S k))) n‖ :=
            norm_nonneg _
          linarith
    _ = (M * (Cb + Cp / (4 * Real.pi))) ^ 2 * L_m i' / (n : ℝ) ^ 2 := by
          rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hL'.le, sq_abs]

#print axioms selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget

end Q3.RouteB.D0Pstar
