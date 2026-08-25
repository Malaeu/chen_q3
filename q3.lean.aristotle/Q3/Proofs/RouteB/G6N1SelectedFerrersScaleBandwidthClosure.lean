import Q3.Proofs.RouteB.G6N1SelectedFerrersFirstOrderBudgetApplication

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Complex Filter MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Closing the scale and bandwidth inputs of the b1 application

Ratified by verdict d52dcc77: neither `SOURCE_SCALE_INVERSE_BOUNDED` nor
`SelectedPhysicalBandwidthCofinal` is free owner data on the b1 path.

* The inverse source scale is bounded via the preferred route: the F72.6
  mode-zero rate on the fixed window `[-1/4, 1/4]` plus the exact unit `L²`
  normalization of `h0` force `‖centerAnchorScalarZero‖ ≥ 1/3` eventually;
  the chi defect keeps `|chi2| ≥ 1/2`; the mode-four center factor cancels
  exactly through `a4 * h4(0) = 3`.  Final bound: `‖scale⁻¹‖ ≤ 8`.
* Bandwidth cofinality is pure arithmetic on the precommitted schedule
  `m = N = k + 2` transported through the b1 family contract.
-/

private theorem w5s_D0_eq (t : ℝ) :
    parabolicCylinderD 0 t = Real.exp (-t ^ 2 / 4) := by
  rw [parabolicCylinderD, Polynomial.hermite_zero]
  simp

private theorem w5s_paperLambda_sq (k : ℕ) :
    (selectedFerrersPaperLambda k) ^ 2 = ((k + 2 : ℕ) : ℝ) := by
  rw [selectedFerrersPaperLambda]
  exact Real.sq_sqrt (by positivity)

private theorem w5s_paperLambda_one_le (k : ℕ) :
    (1 : ℝ) ≤ selectedFerrersPaperLambda k := by
  apply Real.one_le_sqrt.mpr
  have : (1 : ℕ) ≤ k + 2 := Nat.le_add_left 1 (k + 1)
  exact_mod_cast this

/-- Eventually the F72.6 error is at most `1/4`. -/
private theorem w5s_error_small
    {C0 : ℝ} :
    ∀ᶠ k : ℕ in atTop,
      C0 / (selectedFerrersPaperLambda k) ^ 2 < 1 / 4 := by
  have hto : Tendsto (fun k : ℕ => C0 / ((k + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop (tendsto_const_nhds)
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    refine h1.congr ?_
    intro k
    push_cast
    ring
  have := hto.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [this] with k hk
  rw [w5s_paperLambda_sq]
  exact hk

/-- The mode-zero anchor scalar has an eventual explicit lower bound. -/
private theorem w5s_a0_lower
    (C0 C4 : ℝ)
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
              C4 / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k : ℕ in atTop, (1 / 3 : ℝ) ≤ ‖centerAnchorScalarZero k‖ := by
  filter_upwards [hmode, w5s_error_small (C0 := C0)] with k hk hsmall
  set P := selectedFerrersPreAnchorPair k with hP
  set a0 := centerAnchorScalarZero k with ha0
  -- pointwise lower bound on J = [-1/4, 1/4]
  have hJsub : Set.Icc (-(1/4) : ℝ) (1/4) ⊆
      Set.Icc (-(selectedFerrersPaperLambda k))
        (selectedFerrersPaperLambda k) := by
    have h1 := w5s_paperLambda_one_le k
    intro x hx
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  have hpoint : ∀ x ∈ Set.Icc (-(1/4) : ℝ) (1/4),
      (1 / 2 : ℝ) ≤ ‖a0 * P.h0 x‖ := by
    intro x hx
    have hbound := (hk x (hJsub hx)).1
    have hD0 : (3 / 4 : ℝ) ≤ parabolicCylinderD 0 (projectCylinderArgument x) := by
      rw [w5s_D0_eq]
      have hsq : (projectCylinderArgument x) ^ 2 = 4 * Real.pi * x ^ 2 := by
        rw [projectCylinderArgument, mul_pow, Real.sq_sqrt (by positivity)]
      have hx2 : x ^ 2 ≤ (1 / 16 : ℝ) := by
        rcases hx with ⟨hx1, hx2⟩
        nlinarith
      have hexp := Real.add_one_le_exp (-(projectCylinderArgument x) ^ 2 / 4)
      have hpi := Real.pi_le_four
      have hpi0 := Real.pi_pos
      nlinarith [hexp, hsq]
    have hnormD :
        ‖((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ =
          parabolicCylinderD 0 (projectCylinderArgument x) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have htri := abs_norm_sub_norm_le (a0 * P.h0 x)
      ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)
    rw [abs_le] at htri
    have h1 := htri.1
    rw [hnormD] at h1
    linarith [hbound, hD0, h1]
  -- integrate the square over J
  have hIntOn : IntegrableOn
      (fun x : ℝ => ‖a0‖ ^ 2 * ‖P.h0 x‖ ^ 2)
      (Set.Icc (-(1/4) : ℝ) (1/4)) volume :=
    ((P.h0_sqNorm_integrable.const_mul (‖a0‖ ^ 2))).integrableOn
  have hlow : (1 / 8 : ℝ) ≤
      ∫ x in Set.Icc (-(1/4) : ℝ) (1/4), ‖a0‖ ^ 2 * ‖P.h0 x‖ ^ 2 := by
    have hconst :
        (∫ _x in Set.Icc (-(1/4) : ℝ) (1/4), (1 / 4 : ℝ)) = 1 / 8 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_real_Icc]
      norm_num
    rw [← hconst]
    have hconstInt : IntegrableOn (fun _ : ℝ => (1 / 4 : ℝ))
        (Set.Icc (-(1/4) : ℝ) (1/4)) volume :=
      MeasureTheory.integrableOn_const
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    apply MeasureTheory.setIntegral_mono_on
      hconstInt hIntOn measurableSet_Icc
    intro x hx
    have := hpoint x hx
    have hrw : ‖a0‖ ^ 2 * ‖P.h0 x‖ ^ 2 = ‖a0 * P.h0 x‖ ^ 2 := by
      rw [norm_mul, mul_pow]
    rw [hrw]
    nlinarith [this, norm_nonneg (a0 * P.h0 x)]
  have hupper :
      (∫ x in Set.Icc (-(1/4) : ℝ) (1/4), ‖a0‖ ^ 2 * ‖P.h0 x‖ ^ 2) ≤
        ‖a0‖ ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
    have hle :
        (∫ x in Set.Icc (-(1/4) : ℝ) (1/4), ‖P.h0 x‖ ^ 2) ≤
          ∫ x : ℝ, ‖P.h0 x‖ ^ 2 :=
      MeasureTheory.setIntegral_le_integral P.h0_sqNorm_integrable
        (Eventually.of_forall fun x => by positivity)
    calc
      ‖a0‖ ^ 2 * ∫ x in Set.Icc (-(1/4) : ℝ) (1/4), ‖P.h0 x‖ ^ 2
          ≤ ‖a0‖ ^ 2 * ∫ x : ℝ, ‖P.h0 x‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ‖a0‖ ^ 2 := by
            rw [P.h0_normalized, mul_one]
  have hsq : (1 / 8 : ℝ) ≤ ‖a0‖ ^ 2 := le_trans hlow hupper
  nlinarith [norm_nonneg a0, hsq]

/-- Eventual chi-two lower bound from the chi defect. -/
private theorem w5s_chi2_lower
    (Cχ : ℝ)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k : ℕ in atTop,
      (1 / 2 : ℝ) ≤ |(selectedFerrersPreAnchorPair k).chi2| := by
  filter_upwards [hχ, w5s_error_small (C0 := Cχ)] with k hk hsmall
  have h2 : |1 - (selectedFerrersPreAnchorPair k).chi2| < 1 / 4 :=
    lt_of_le_of_lt hk.2 hsmall
  rw [abs_lt] at h2
  have hpos : (3 / 4 : ℝ) < (selectedFerrersPreAnchorPair k).chi2 := by
    linarith [h2.2]
  rw [abs_of_pos (by linarith)]
  linarith

/-- **The derived inverse-scale bound** (verdict d52dcc77 preferred route). -/
theorem selectedFerrersSourceScale_inverse_bounded
    (C0 C4 Cχ : ℝ)
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
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k : ℕ in atTop,
      ‖(selectedFerrersLemma73SourceScale k)⁻¹‖ ≤ 8 := by
  filter_upwards [w5s_a0_lower C0 C4 hmode, w5s_chi2_lower Cχ hχ]
    with k ha0 hchi2
  set P := selectedFerrersPreAnchorPair k with hP
  -- exact center cancellation at mode four
  have hcenter4 := centerAnchorScalarFour_mul_center k
  have hnorm4 : ‖centerAnchorScalarFour k‖ * ‖P.h4 0‖ = 3 := by
    have := congrArg norm hcenter4
    rw [norm_mul] at this
    simpa [selectedFerrersCenterFour, hP] using this
  -- denominator lower bound through I4
  have hI4 : ((P.I4 : ℝ) : ℂ) = ((P.chi2 : ℝ) : ℂ) * P.h4 0 := P.h4_fourier_center
  have hI4abs : |P.I4| = |P.chi2| * ‖P.h4 0‖ := by
    have := congrArg norm hI4
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs] at this
    exact this
  have hdenom : |P.I4| ≤ P.normalizingDenominator := by
    rw [ProlatePair.normalizingDenominator]
    have h1 : P.I4 ^ 2 ≤ P.I0 ^ 2 + P.I4 ^ 2 := by nlinarith [sq_nonneg P.I0]
    calc
      |P.I4| = Real.sqrt (P.I4 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (P.I0 ^ 2 + P.I4 ^ 2) := Real.sqrt_le_sqrt h1
  have hdenom0 : 0 ≤ P.normalizingDenominator := Real.sqrt_nonneg _
  -- norm of the scale
  have hscale_norm :
      ‖selectedFerrersLemma73SourceScale k‖ =
        ‖centerAnchorScalarZero k‖ * ‖centerAnchorScalarFour k‖ / 4 *
          P.normalizingDenominator := by
    rw [selectedFerrersLemma73SourceScale, selectedFerrersLemma72Scale]
    rw [norm_mul, norm_mul, norm_neg, norm_div, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdenom0]
    have h4n : ‖(4 : ℂ)‖ = 4 := by norm_num
    have h16n : ‖(16 : ℂ)‖ = 16 := by norm_num
    rw [h4n, h16n]
    ring
  have hscale_low :
      (1 / 8 : ℝ) ≤ ‖selectedFerrersLemma73SourceScale k‖ := by
    rw [hscale_norm]
    have hstep : |P.chi2| * ‖P.h4 0‖ ≤ P.normalizingDenominator := by
      rw [← hI4abs]
      exact hdenom
    have ha4pos : 0 ≤ ‖centerAnchorScalarFour k‖ := norm_nonneg _
    have hchain :
        ‖centerAnchorScalarZero k‖ * ‖centerAnchorScalarFour k‖ / 4 *
            (|P.chi2| * ‖P.h4 0‖) ≤
          ‖centerAnchorScalarZero k‖ * ‖centerAnchorScalarFour k‖ / 4 *
            P.normalizingDenominator := by
      apply mul_le_mul_of_nonneg_left hstep
      positivity
    have hval :
        ‖centerAnchorScalarZero k‖ * ‖centerAnchorScalarFour k‖ / 4 *
            (|P.chi2| * ‖P.h4 0‖) =
          ‖centerAnchorScalarZero k‖ * |P.chi2| *
            (‖centerAnchorScalarFour k‖ * ‖P.h4 0‖) / 4 := by
      ring
    have hval2 :
        ‖centerAnchorScalarZero k‖ * |P.chi2| *
            (‖centerAnchorScalarFour k‖ * ‖P.h4 0‖) / 4 =
          ‖centerAnchorScalarZero k‖ * |P.chi2| * 3 / 4 := by
      rw [hnorm4]
    have hlow2 : (1 / 8 : ℝ) ≤
        ‖centerAnchorScalarZero k‖ * |P.chi2| * 3 / 4 := by
      nlinarith [ha0, hchi2, norm_nonneg (centerAnchorScalarZero k),
        abs_nonneg P.chi2]
    calc
      (1 / 8 : ℝ) ≤ ‖centerAnchorScalarZero k‖ * |P.chi2| * 3 / 4 := hlow2
      _ = ‖centerAnchorScalarZero k‖ * ‖centerAnchorScalarFour k‖ / 4 *
            (|P.chi2| * ‖P.h4 0‖) := by rw [hval, hval2]
      _ ≤ _ := hchain
  rw [norm_inv]
  have hpos : (0 : ℝ) < ‖selectedFerrersLemma73SourceScale k‖ := by
    linarith
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith [hscale_low, hpos]

/-- **Derived bandwidth cofinality** on the b1 path: pure arithmetic on the
precommitted schedule `m = N = k + 2`. -/
theorem selectedPhysicalBandwidthCofinal_of_familyCrosswalk
    (S : ProlateCanonicalSourceData)
    (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S) :
    SelectedPhysicalBandwidthCofinal S := by
  unfold SelectedPhysicalBandwidthCofinal
  have hpre : Tendsto
      (fun k : ℕ =>
        physicalFourierBandwidth (selectedFerrersPreAnchorIndex k))
      atTop atTop := by
    have hlower : ∀ k : ℕ,
        Real.pi * Real.sqrt ((k + 2 : ℕ) : ℝ) ≤
          physicalFourierBandwidth (selectedFerrersPreAnchorIndex k) := by
      intro k
      have hm : ((selectedFerrersPreAnchorIndex k).m : ℝ) = ((k + 2 : ℕ) : ℝ) := rfl
      have hN : ((selectedFerrersPreAnchorIndex k).N : ℕ) = k + 2 := rfl
      have hk2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      have hsqrt_pos : (0 : ℝ) < Real.sqrt ((k + 2 : ℕ) : ℝ) := by
        apply Real.sqrt_pos.mpr
        linarith
      have hL : L_m (selectedFerrersPreAnchorIndex k) =
          Real.log ((k + 2 : ℕ) : ℝ) := by
        show logLength _ = _
        rw [logLength, hm]
      have hLpos : 0 < L_m (selectedFerrersPreAnchorIndex k) :=
        logLength_pos _
      have hlog_le : Real.log ((k + 2 : ℕ) : ℝ) ≤
          2 * Real.sqrt ((k + 2 : ℕ) : ℝ) := by
        have hsq : Real.log ((k + 2 : ℕ) : ℝ) =
            2 * Real.log (Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
          rw [Real.log_sqrt (by linarith)]
          ring
        have hle := Real.log_le_sub_one_of_pos hsqrt_pos
        nlinarith [hle]
      rw [physicalFourierBandwidth, hL]
      have hNcast : (((selectedFerrersPreAnchorIndex k).N + 1 : ℕ) : ℝ) =
          ((k + 2 : ℕ) : ℝ) + 1 := by
        rw [hN]
        push_cast
        ring
      rw [hNcast]
      have hlogpos : 0 < Real.log ((k + 2 : ℕ) : ℝ) := by
        rw [← hL]
        exact hLpos
      rw [le_div_iff₀ hlogpos]
      have hpi := Real.pi_pos
      have hself : Real.sqrt ((k + 2 : ℕ) : ℝ) *
          Real.sqrt ((k + 2 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) :=
        Real.mul_self_sqrt (by linarith)
      have hmul : Real.pi * Real.sqrt ((k + 2 : ℕ) : ℝ) *
          Real.log ((k + 2 : ℕ) : ℝ) ≤
          Real.pi * Real.sqrt ((k + 2 : ℕ) : ℝ) *
            (2 * Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hlog_le
        positivity
      nlinarith [hmul, hself, hpi]
    apply tendsto_atTop_mono hlower
    apply Tendsto.const_mul_atTop Real.pi_pos
    have hsqrtTendsto : Tendsto Real.sqrt atTop atTop := by
      apply tendsto_atTop_atTop.mpr
      intro b
      refine ⟨max (b ^ 2) 0 + 1, fun a ha => ?_⟩
      have hb2 : b ^ 2 ≤ a := by
        have := le_max_left (b ^ 2) (0 : ℝ)
        linarith
      have h1 : Real.sqrt (b ^ 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt hb2
      rw [Real.sqrt_sq_eq_abs] at h1
      calc b ≤ |b| := le_abs_self b
        _ ≤ Real.sqrt a := h1
    apply hsqrtTendsto.comp
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    refine h1.congr ?_
    intro k
    push_cast
    ring
  refine hpre.congr' ?_
  filter_upwards [hFamily] with k hk
  rw [hk.1]

/--
**The closed-scale-closed-bandwidth application** (verdict d52dcc77 target):
production projection-tail decay from only the b1 family contract, the F72.6
mode/chi rates, and the open derivative-budget supplier.
-/
theorem selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget_closedScaleBandwidth
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
        selectedFerrersAbelLogDerivativeBudget k ≤ D) :
    SelectedProjectionTailDecay S := by
  apply selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget
    S hFamily C0 C4 Cχ hC0 hC4 hCχ hmode hχ hD
  · exact ⟨8, by norm_num,
      selectedFerrersSourceScale_inverse_bounded C0 C4 Cχ hmode hχ⟩
  · exact selectedPhysicalBandwidthCofinal_of_familyCrosswalk S hFamily

#print axioms selectedFerrersSourceScale_inverse_bounded
#print axioms selectedPhysicalBandwidthCofinal_of_familyCrosswalk
#print axioms selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget_closedScaleBandwidth

end Q3.RouteB.D0Pstar
