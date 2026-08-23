import Q3.Proofs.RouteB.G6N1SelectedFerrersDirectCylinderRate
import Q3.Proofs.RouteB.G6N1SelectedFerrersCenterIntegralRate

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.5 — the selected zero-mass cylinder packet assembly

Floor `F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY` of verdict `b7e56afd`.

Finite algebra only.  The internal Lemma-7.2 source scale is precommitted by
an explicit formula — the unique sign/orientation dictated by the literal
`prolateCombination`, the two center anchors and the exact cylinder
decomposition, never fitted from the desired limit:

`s_k = -((a0_k * a4_k) / 16) * D_k`,  `D_k = normalizingDenominator`.

Exact cancellation of the nonzero denominator gives

`s_k * q_k = (1/16)(a0 I0)(a4 h4) - (1/16)(a4 I4)(a0 h0)`,

whose limiting value is `(1/16) D4 - (3/16) D0 = explicitCCMLimitH`.  The
negative sign is load-bearing (the private plant refutes the positive one).
The mode rates and the anchored-integral rates enter as the two upstream
suppliers; the crude global cylinder bounds `1` and `91` are reproved
privately (the analogous F72.1C helpers are private and not exported — this
is source duplication, not a new premise).  No sup-error is integrated over
the expanding window; the `lambda^(-2)` budget is preserved by
finite-dimensional algebra alone.

LEDGER:
  CLOSES: [F72_5_SELECTED_FERRERS_INTERNAL_LEMMA72_SCALE,
           F72_5_ZERO_MASS_CYLINDER_PACKET_RATE]
  OPENS:  []
-/

/-- **The plant.**  With ideal coefficients `I4 = 3`, `I0 = 1`, ideal mode
values `d0 = 0`, `d4 = 16` and denominator `1`, the positive scale gives `-1`
while the mandated negative scale gives `+1`: the source-scale sign is
load-bearing. -/
private theorem zeroMassCylinderPacket_wrong_scale_sign_plant :
    ((1 : ℂ) / 16) * ((3 : ℂ) * 0 - 1 * 16) = -1 ∧
      (-((1 : ℂ) / 16)) * ((3 : ℂ) * 0 - 1 * 16) = 1 := by
  norm_num

/-! ## Private crude cylinder bounds (duplicated from the private F72.1C helpers) -/

private theorem exp_linear_bound (c s : ℝ) (hc : 0 < c) (_hs : 0 ≤ s) :
    s * Real.exp (-(s / c)) ≤ c := by
  have h1 : s / c + 1 ≤ Real.exp (s / c) := Real.add_one_le_exp _
  have h2 : s ≤ c * Real.exp (s / c) := by
    have h3 : c * (s / c + 1) = s + c := by
      rw [mul_add, mul_div_cancel₀ _ hc.ne', mul_one]
    have h4 := mul_le_mul_of_nonneg_left h1 hc.le
    rw [h3] at h4
    linarith
  rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
  linarith [h2]

private theorem targetD0_bound (x : ℝ) :
    |parabolicCylinderD 0 (projectCylinderArgument x)| ≤ 1 := by
  rw [parabolicCylinderD_zero_projectArgument,
    abs_of_pos (Real.exp_pos _)]
  have h1 : -Real.pi * x ^ 2 ≤ 0 := by nlinarith [Real.pi_pos, sq_nonneg x]
  calc Real.exp (-Real.pi * x ^ 2) ≤ Real.exp 0 := Real.exp_le_exp.mpr h1
    _ = 1 := Real.exp_zero

private theorem targetD4_bound (x : ℝ) :
    |parabolicCylinderD 4 (projectCylinderArgument x)| ≤ 91 := by
  rw [parabolicCylinderD_four_projectArgument]
  set s : ℝ := Real.pi * x ^ 2 with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hE : (-Real.pi * x ^ 2 : ℝ) = -s := by rw [hsdef]; ring
  have hpoly : (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3 : ℝ)
      = 16 * s ^ 2 - 24 * s + 3 := by rw [hsdef]; ring
  rw [hE, hpoly, abs_mul, abs_of_pos (Real.exp_pos _)]
  have htri : |16 * s ^ 2 - 24 * s + 3| ≤ 16 * s ^ 2 + 24 * s + 3 := by
    rw [abs_le]
    constructor <;> nlinarith [hs0, sq_nonneg s]
  have hlin : s * Real.exp (-s) ≤ 1 := by
    have := exp_linear_bound 1 s one_pos hs0
    rwa [div_one] at this
  have hsq : s ^ 2 * Real.exp (-s) ≤ 4 := by
    have hhalf : s * Real.exp (-(s / 2)) ≤ 2 := exp_linear_bound 2 s two_pos hs0
    have hprod : (s * Real.exp (-(s / 2))) * (s * Real.exp (-(s / 2)))
        ≤ 2 * 2 := by
      have h0 : 0 ≤ s * Real.exp (-(s / 2)) := by positivity
      exact mul_le_mul hhalf hhalf h0 (by norm_num)
    have hexp2 : Real.exp (-(s / 2)) * Real.exp (-(s / 2)) = Real.exp (-s) := by
      rw [← Real.exp_add]
      ring_nf
    calc s ^ 2 * Real.exp (-s)
        = (s * Real.exp (-(s / 2))) * (s * Real.exp (-(s / 2))) := by
          rw [show (s * Real.exp (-(s / 2))) * (s * Real.exp (-(s / 2)))
              = s ^ 2 * (Real.exp (-(s / 2)) * Real.exp (-(s / 2))) from by ring,
            hexp2]
      _ ≤ 2 * 2 := hprod
      _ = 4 := by norm_num
  have hone : Real.exp (-s) ≤ 1 := by
    calc Real.exp (-s) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  calc Real.exp (-s) * |16 * s ^ 2 - 24 * s + 3|
      ≤ Real.exp (-s) * (16 * s ^ 2 + 24 * s + 3) :=
        mul_le_mul_of_nonneg_left htri (Real.exp_pos _).le
    _ = 16 * (s ^ 2 * Real.exp (-s)) + 24 * (s * Real.exp (-s))
        + 3 * Real.exp (-s) := by ring
    _ ≤ 16 * 4 + 24 * 1 + 3 * 1 := by
        have h1 := mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 16)
        have h2 := mul_le_mul_of_nonneg_left hlin (by norm_num : (0:ℝ) ≤ 24)
        have h3 := mul_le_mul_of_nonneg_left hone (by norm_num : (0:ℝ) ≤ 3)
        linarith
    _ = 91 := by norm_num

/-! ## The precommitted source scale -/

/-- **The internal Lemma-7.2 source scale.**  Precommitted formula; the
negative sign is the unique orientation dictated by `prolateCombination` and
the cylinder decomposition. -/
noncomputable def selectedFerrersLemma72Scale (k : ℕ) : ℂ :=
  -((centerAnchorScalarZero k * centerAnchorScalarFour k) / (16 : ℂ)) *
    (((selectedFerrersPreAnchorPair k).normalizingDenominator : ℝ) : ℂ)

private theorem selected_normalizingDenominator_pos (k : ℕ) :
    0 < (selectedFerrersPreAnchorPair k).normalizingDenominator := by
  rw [ProlatePair.normalizingDenominator_eq]
  apply Real.sqrt_pos.mpr
  have hI0 := (selectedFerrersPreAnchorPair_spec k).2.2.2.1
  nlinarith [sq_nonneg (selectedFerrersPreAnchorPair k).I4]

/-- The source scale never vanishes. -/
theorem selectedFerrersLemma72Scale_ne (k : ℕ) :
    selectedFerrersLemma72Scale k ≠ 0 := by
  rw [selectedFerrersLemma72Scale]
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    apply div_ne_zero
    · exact mul_ne_zero (centerAnchorScalarZero_ne k) (centerAnchorScalarFour_ne k)
    · norm_num
  · rw [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (selected_normalizingDenominator_pos k)

/-- The exact cancellation identity: the scaled packet is the anchored
two-mode combination. -/
private theorem scale_mul_combination (k : ℕ) (x : ℝ) :
    selectedFerrersLemma72Scale k *
        prolateCombination (selectedFerrersPreAnchorPair k) x
      = (1 / 16 : ℂ) *
          ((centerAnchorScalarZero k *
              ((selectedFerrersPreAnchorPair k).I0 : ℂ)) *
            (centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 x))
        - (1 / 16 : ℂ) *
          ((centerAnchorScalarFour k *
              ((selectedFerrersPreAnchorPair k).I4 : ℂ)) *
            (centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 x)) := by
  rw [selectedFerrersLemma72Scale, prolateCombination_apply]
  have hD : (((selectedFerrersPreAnchorPair k).normalizingDenominator : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (selected_normalizingDenominator_pos k)
  field_simp
  ring

/-! ## The packet rate -/

/-- **F72.5.**  The exact mode rates and the chi-defect rate produce the
selected zero-mass cylinder packet rate to `explicitCCMLimitH` at the
`lambda^(-2)` unit, with an a-priori constant. -/
theorem selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates
    (C0 C4 Cχ : ℝ)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hCχ : 0 ≤ Cχ)
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
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖selectedFerrersLemma72Scale k *
              prolateCombination (selectedFerrersPreAnchorPair k) x -
            explicitCCMLimitH x‖ ≤
              C / (selectedFerrersPaperLambda k) ^ 2 := by
  obtain ⟨CI, hCI0, hCIrate⟩ :=
    selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate Cχ hCχ hχ
  refine ⟨((1 + CI) * C4 + (3 + CI) * C0 + 92 * CI) / 16, by positivity, ?_⟩
  filter_upwards [hmode, hCIrate] with k hmodek hIk
  intro x hx
  have hlampos : 0 < selectedFerrersPaperLambda k := by
    rw [selectedFerrersPaperLambda]
    apply Real.sqrt_pos.mpr
    positivity
  have hlamsq1 : (1 : ℝ) ≤ (selectedFerrersPaperLambda k) ^ 2 := by
    rw [selectedFerrersPaperLambda_sq]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hlamsq0 : 0 < (selectedFerrersPaperLambda k) ^ 2 := by positivity
  -- anchored-integral norm ceilings
  have hI0norm : ‖centerAnchorScalarZero k *
      ((selectedFerrersPreAnchorPair k).I0 : ℂ)‖ ≤ 1 + CI := by
    have h1 : ‖centerAnchorScalarZero k *
        ((selectedFerrersPreAnchorPair k).I0 : ℂ)‖
        ≤ ‖centerAnchorScalarZero k *
            ((selectedFerrersPreAnchorPair k).I0 : ℂ) - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      calc ‖centerAnchorScalarZero k * ((selectedFerrersPreAnchorPair k).I0 : ℂ)‖
          = ‖(centerAnchorScalarZero k *
              ((selectedFerrersPreAnchorPair k).I0 : ℂ) - 1) + 1‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : CI / (selectedFerrersPaperLambda k) ^ 2 ≤ CI :=
      div_le_self hCI0 hlamsq1
    have h3 := hIk.1
    simp only [norm_one] at h1
    linarith
  have hI4norm : ‖centerAnchorScalarFour k *
      ((selectedFerrersPreAnchorPair k).I4 : ℂ)‖ ≤ 3 + CI := by
    have h1 : ‖centerAnchorScalarFour k *
        ((selectedFerrersPreAnchorPair k).I4 : ℂ)‖
        ≤ ‖centerAnchorScalarFour k *
            ((selectedFerrersPreAnchorPair k).I4 : ℂ) - (3 : ℂ)‖ + ‖(3 : ℂ)‖ := by
      calc ‖centerAnchorScalarFour k * ((selectedFerrersPreAnchorPair k).I4 : ℂ)‖
          = ‖(centerAnchorScalarFour k *
              ((selectedFerrersPreAnchorPair k).I4 : ℂ) - 3) + 3‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : CI / (selectedFerrersPaperLambda k) ^ 2 ≤ CI :=
      div_le_self hCI0 hlamsq1
    have h3 := hIk.2
    have hnorm3 : ‖(3 : ℂ)‖ = 3 := by
      rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num
    rw [hnorm3] at h1
    linarith
  -- decomposition
  set A0 : ℂ := centerAnchorScalarZero k *
    ((selectedFerrersPreAnchorPair k).I0 : ℂ) with hA0
  set A4 : ℂ := centerAnchorScalarFour k *
    ((selectedFerrersPreAnchorPair k).I4 : ℂ) with hA4
  set F0 : ℂ := centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 x
    with hF0
  set F4 : ℂ := centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 x
    with hF4
  set d0 : ℝ := parabolicCylinderD 0 (projectCylinderArgument x) with hd0
  set d4 : ℝ := parabolicCylinderD 4 (projectCylinderArgument x) with hd4
  have hkey : selectedFerrersLemma72Scale k *
      prolateCombination (selectedFerrersPreAnchorPair k) x -
        explicitCCMLimitH x
      = (1 / 16 : ℂ) * (A0 * (F4 - ((d4 : ℝ) : ℂ)) + (A0 - 1) * ((d4 : ℝ) : ℂ))
        - (1 / 16 : ℂ) * (A4 * (F0 - ((d0 : ℝ) : ℂ)) + (A4 - 3) * ((d0 : ℝ) : ℂ)) := by
    rw [scale_mul_combination, explicitCCMLimitH_eq_cylinder_combination]
    rw [hA0, hA4, hF0, hF4, hd0, hd4]
    push_cast
    ring
  rw [hkey]
  -- norm bounds for the four summands
  have hT4 := (hmodek x hx).2
  have hT0 := (hmodek x hx).1
  have hE0 := hIk.1
  have hE4 := hIk.2
  have hd0abs : |d0| ≤ 1 := targetD0_bound x
  have hd4abs : |d4| ≤ 91 := targetD4_bound x
  have hd0norm : ‖((d0 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hd0abs
  have hd4norm : ‖((d4 : ℝ) : ℂ)‖ ≤ 91 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hd4abs
  set L : ℝ := (selectedFerrersPaperLambda k) ^ 2 with hL
  have hb1 : ‖A0 * (F4 - ((d4 : ℝ) : ℂ))‖ ≤ (1 + CI) * (C4 / L) := by
    rw [norm_mul]
    exact mul_le_mul hI0norm hT4 (norm_nonneg _) (by linarith)
  have hb2 : ‖(A0 - 1) * ((d4 : ℝ) : ℂ)‖ ≤ (CI / L) * 91 := by
    rw [norm_mul]
    exact mul_le_mul hE0 hd4norm (norm_nonneg _) (by positivity)
  have hb3 : ‖A4 * (F0 - ((d0 : ℝ) : ℂ))‖ ≤ (3 + CI) * (C0 / L) := by
    rw [norm_mul]
    exact mul_le_mul hI4norm hT0 (norm_nonneg _) (by linarith)
  have hb4 : ‖(A4 - 3) * ((d0 : ℝ) : ℂ)‖ ≤ (CI / L) * 1 := by
    rw [norm_mul]
    exact mul_le_mul hE4 hd0norm (norm_nonneg _) (by positivity)
  have hnorm16 : ‖(1 / 16 : ℂ)‖ = 1 / 16 := by
    rw [show (1 / 16 : ℂ) = ((1 / 16 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  calc ‖(1 / 16 : ℂ) * (A0 * (F4 - ((d4 : ℝ) : ℂ)) + (A0 - 1) * ((d4 : ℝ) : ℂ))
        - (1 / 16 : ℂ) * (A4 * (F0 - ((d0 : ℝ) : ℂ)) + (A4 - 3) * ((d0 : ℝ) : ℂ))‖
      ≤ ‖(1 / 16 : ℂ) * (A0 * (F4 - ((d4 : ℝ) : ℂ)) + (A0 - 1) * ((d4 : ℝ) : ℂ))‖
        + ‖(1 / 16 : ℂ) * (A4 * (F0 - ((d0 : ℝ) : ℂ)) + (A4 - 3) * ((d0 : ℝ) : ℂ))‖ :=
        norm_sub_le _ _
    _ ≤ (1 / 16) * ((1 + CI) * (C4 / L) + (CI / L) * 91)
        + (1 / 16) * ((3 + CI) * (C0 / L) + (CI / L) * 1) := by
        have hs1 : ‖(1 / 16 : ℂ) * (A0 * (F4 - ((d4 : ℝ) : ℂ))
            + (A0 - 1) * ((d4 : ℝ) : ℂ))‖
            ≤ (1 / 16) * ((1 + CI) * (C4 / L) + (CI / L) * 91) := by
          rw [norm_mul, hnorm16]
          apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact le_trans (norm_add_le _ _) (by linarith)
        have hs2 : ‖(1 / 16 : ℂ) * (A4 * (F0 - ((d0 : ℝ) : ℂ))
            + (A4 - 3) * ((d0 : ℝ) : ℂ))‖
            ≤ (1 / 16) * ((3 + CI) * (C0 / L) + (CI / L) * 1) := by
          rw [norm_mul, hnorm16]
          apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact le_trans (norm_add_le _ _) (by linarith)
        linarith
    _ = (((1 + CI) * C4 + (3 + CI) * C0 + 92 * CI) / 16) / L := by
        rw [hL]
        field_simp
        ring

#print axioms selectedFerrersLemma72Scale_ne
#print axioms selectedFerrers_zeroMassCylinderPacketRate_of_modeAndChiRates

end Q3.RouteB.D0Pstar

end
