import Q3.Proofs.RouteB.G6N1FuchsSelectedEigenvalueDefectRate

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.4 — the center-anchored integral rate from the chi defect

Floor `F72_4_CENTER_INTEGRAL_RATE_FROM_CHI` of verdict `b0cbbc9e`.

No new analysis and no new external input: the `ProlatePair` frequency-zero
fields say the whole-line integrals are exactly `I0 = chi0 * h0 0` and
`I4 = chi2 * h4 0`, and the precommitted center anchors send the two centers
to `1` and `3`.  Therefore the anchored integrals are exactly `chi0` and
`3 * chi2`, and the common eventual chi-defect rate transfers to both
integral targets with the a-priori constant `3 * Cχ`.

Deliberately NOT done here: integrating the F72.1C pointwise sup-error over
the expanding window — that would lose one power of `lambda` and recover only
`O(lambda^{-1})`.  This floor exists precisely to avoid that loss.

The private plant records that center anchoring alone does not force the
integral targets: a negative transform scalar sends the anchored integrals to
`-1` and `-3`.  The chi-defect input is load-bearing.

LEDGER:
  CLOSES: [F72_4_CENTER_INTEGRAL_RATE_FROM_CHI]
  OPENS:  []
-/

/-- **The plant.**  Center anchoring alone does not force the whole-window
integral targets: a negative transform scalar sends the anchored integrals
to `-1` and `-3`. -/
private theorem centerAnchoredIntegral_without_chiRate_plant :
    |(-1 : ℝ) - 1| = 2 ∧ |3 * (-1 : ℝ) - 3| = 6 := by
  norm_num

/-- **F72.4.**  The common eventual chi-defect rate produces the
center-anchored integral rate at both selected modes, with the exact common
constant `3 * Cχ`. -/
theorem selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate
    (Cχ : ℝ) (hCχ : 0 ≤ Cχ)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ CI : ℝ, 0 ≤ CI ∧
      ∀ᶠ k in Filter.atTop,
        ‖centerAnchorScalarZero k *
            ((selectedFerrersPreAnchorPair k).I0 : ℂ) - (1 : ℂ)‖ ≤
            CI / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
            ((selectedFerrersPreAnchorPair k).I4 : ℂ) - (3 : ℂ)‖ ≤
            CI / (selectedFerrersPaperLambda k) ^ 2 := by
  refine ⟨3 * Cχ, by linarith, ?_⟩
  filter_upwards [hχ] with k hk
  have hlampos : 0 < selectedFerrersPaperLambda k := by
    rw [selectedFerrersPaperLambda]
    apply Real.sqrt_pos.mpr
    positivity
  have hlamsq : 0 < (selectedFerrersPaperLambda k) ^ 2 := by positivity
  -- the two exact anchored-integral identities
  have hid0 : centerAnchorScalarZero k *
      ((selectedFerrersPreAnchorPair k).I0 : ℂ)
        = (((selectedFerrersPreAnchorPair k).chi0 : ℝ) : ℂ) := by
    rw [(selectedFerrersPreAnchorPair k).h0_fourier_center]
    have hlock := centerAnchorScalarZero_mul_center k
    rw [selectedFerrersCenterZero] at hlock
    calc centerAnchorScalarZero k *
        ((((selectedFerrersPreAnchorPair k).chi0 : ℝ) : ℂ) *
          (selectedFerrersPreAnchorPair k).h0 0)
        = (((selectedFerrersPreAnchorPair k).chi0 : ℝ) : ℂ) *
          (centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 0) := by
          ring
      _ = (((selectedFerrersPreAnchorPair k).chi0 : ℝ) : ℂ) := by
          rw [hlock, mul_one]
  have hid4 : centerAnchorScalarFour k *
      ((selectedFerrersPreAnchorPair k).I4 : ℂ)
        = 3 * (((selectedFerrersPreAnchorPair k).chi2 : ℝ) : ℂ) := by
    rw [(selectedFerrersPreAnchorPair k).h4_fourier_center]
    have hlock := centerAnchorScalarFour_mul_center k
    rw [selectedFerrersCenterFour] at hlock
    calc centerAnchorScalarFour k *
        ((((selectedFerrersPreAnchorPair k).chi2 : ℝ) : ℂ) *
          (selectedFerrersPreAnchorPair k).h4 0)
        = (((selectedFerrersPreAnchorPair k).chi2 : ℝ) : ℂ) *
          (centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 0) := by
          ring
      _ = 3 * (((selectedFerrersPreAnchorPair k).chi2 : ℝ) : ℂ) := by
          rw [hlock]
          ring
  constructor
  · -- mode zero: ‖chi0 − 1‖ = |1 − chi0| ≤ Cχ/λ² ≤ 3Cχ/λ²
    rw [hid0]
    have hnorm : ‖(((selectedFerrersPreAnchorPair k).chi0 : ℝ) : ℂ) - (1 : ℂ)‖
        = |1 - (selectedFerrersPreAnchorPair k).chi0| := by
      rw [show (((selectedFerrersPreAnchorPair k).chi0 : ℝ) : ℂ) - (1 : ℂ)
          = (((selectedFerrersPreAnchorPair k).chi0 - 1 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [hnorm]
    refine le_trans hk.1 ?_
    apply div_le_div_of_nonneg_right ?_ hlamsq.le
    linarith
  · -- mode four: ‖3·chi2 − 3‖ = 3·|1 − chi2| ≤ 3Cχ/λ²
    rw [hid4]
    have hnorm : ‖3 * (((selectedFerrersPreAnchorPair k).chi2 : ℝ) : ℂ) - (3 : ℂ)‖
        = 3 * |1 - (selectedFerrersPreAnchorPair k).chi2| := by
      rw [show 3 * (((selectedFerrersPreAnchorPair k).chi2 : ℝ) : ℂ) - (3 : ℂ)
          = ((3 * ((selectedFerrersPreAnchorPair k).chi2 - 1) : ℝ) : ℂ) by
            push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_sub_comm]
      norm_num
    rw [hnorm]
    have h3 : 3 * |1 - (selectedFerrersPreAnchorPair k).chi2|
        ≤ 3 * (Cχ / (selectedFerrersPaperLambda k) ^ 2) :=
      mul_le_mul_of_nonneg_left hk.2 (by norm_num)
    refine le_trans h3 (le_of_eq ?_)
    ring

#print axioms selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate

end Q3.RouteB.D0Pstar

end
