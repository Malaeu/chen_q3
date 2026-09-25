import Q3.Proofs.RouteB.G6N1SelectedFerrersJointGreenRowBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

private theorem gwin_eq_windowedMellin
    (i : PairIndex) (h : ℝ → ℂ) (s : ℂ) :
    preAnchorGwinTransformCoordinate i h s =
      windowedMellin (lambda_m i) (E_star h) (-Complex.I * s) := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  have hlam : 1 < lambda_m i := by
    simpa [lambda_m] using
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
        Real.sqrt 1 < Real.sqrt i.m)
  have hlam0 : 0 < lambda_m i := zero_lt_one.trans hlam
  unfold preAnchorGwinTransformCoordinate EStarMuntzZeroMassContinuation.Gwin
    windowedMellin sourceWindow mellin
  rw [← integral_Icc_eq_integral_Ioo]
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  have hlaminv : 0 < (lambda_m i)⁻¹ := inv_pos.mpr hlam0
  by_cases hwin : u ∈ Set.Icc (lambda_m i)⁻¹ (lambda_m i)
  · have hu0 : 0 < u := hlaminv.trans_le hwin.1
    simp [hwin, hu0, EStarMuntzZeroMassContinuation.Estar,
      E_star, smul_eq_mul, mul_comm]
  · by_cases hu0 : 0 < u
    · simp [hwin, hu0]
    · simp [hwin, hu0]

#print axioms gwin_eq_windowedMellin

/-- The exact finite paired-window integral for the selected CCM row, subject
to the finite term Mellin convergence required by the window crosswalk. -/
theorem selectedFerrersFiniteCCMRow_eq_pairedWindowIntegral
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ)
    (j : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N)
    (hconv :
      ∀ r ∈ sourcePositiveIndexFinset ((selectedFerrersCofinalSourceData P).index k),
        MellinConvergent
          ((scaledSourceWindow
            (lambda_m ((selectedFerrersCofinalSourceData P).index k)) r).indicator
              (prolateCombination ((selectedFerrersCofinalSourceData P).pair k)))
          ((-Complex.I *
            ((((2 * Real.pi *
              (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j : ℝ)) /
              L_m ((selectedFerrersCofinalSourceData P).index k)) : ℝ) : ℂ)) + 1 / 2)) :
    selectedFerrersFiniteCCMRow P k j =
      ((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) *
        ((-1 : ℂ) ^ ccmModeFinite
          ((selectedFerrersCofinalSourceData P).index k).N j) *
        ((Real.sqrt (L_m ((selectedFerrersCofinalSourceData P).index k)) : ℝ)⁻¹ : ℂ) *
        weightedDirichletWindowIntegral
          (lambda_m ((selectedFerrersCofinalSourceData P).index k))
          (sourcePositiveIndexFinset ((selectedFerrersCofinalSourceData P).index k))
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((-Complex.I *
            ((((2 * Real.pi *
              (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j : ℝ)) /
              L_m ((selectedFerrersCofinalSourceData P).index k)) : ℝ) : ℂ)) + 1 / 2) := by
  let D := selectedFerrersCofinalSourceData P
  let i := D.index k
  let h := prolateCombination (D.pair k)
  let n := ccmModeFinite i.N j
  let s : ℂ := -Complex.I * ((((2 * Real.pi * (n : ℝ)) / L_m i : ℝ) : ℂ))
  have hfinite :
      WindowFiniteSupport (lambda_m i) (sourcePositiveIndexFinset i) h :=
    prolateCombination_windowFiniteSupport i (D.pair k) (D.lambda_eq k)
  have hlam : 0 < lambda_m i := by
    unfold lambda_m
    apply Real.sqrt_pos.mpr
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  have hconv' :
      ∀ r ∈ sourcePositiveIndexFinset i,
        MellinConvergent
          ((scaledSourceWindow (lambda_m i) r).indicator h)
          (s + 1 / 2) := by
    simpa only [D, i, h, n, s] using hconv
  rw [selectedFerrersFiniteCCMRow_eq_normalizedMellinSample]
  rw [gwin_eq_windowedMellin]
  rw [windowedMellin_E_star_eq_weightedDirichletWindowIntegral
    hlam hfinite hconv']

#print axioms selectedFerrersFiniteCCMRow_eq_pairedWindowIntegral

end Q3.RouteB.D0Pstar
