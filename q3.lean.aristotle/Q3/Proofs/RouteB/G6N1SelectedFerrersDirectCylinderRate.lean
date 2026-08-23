import Q3.Proofs.RouteB.G6N1CenterNormalizedSatz9RateTransfer
import Q3.Proofs.RouteB.G6N1CenterAnchorScalarLock

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.1C — selected Ferrers direct cylinder rate, with explicit paper-rate input

Floor `F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT`
of verdict `a3675740`.

The composition and nothing else: two explicit source families `S0`, `S4` at
the exact selected project separation values carry explicit raw paper rates
(the Meixner–Schäfke Satz-9 asymptotic remains an external, typed input about
these same families — it is never inferred from the payload type).  The
center-normalized source/project bind identifies their normalized views with
the selected Ferrers modes, the precommitted center anchors convert the
normalization into the anchored scalars, and the ratified F72.1A0 transfer
turns each raw `gamma^(-1)` rate into the physical `lambda^(-2)` rate.  The
denominator guards are derived from the selected schedule
(`gamma_k = 2*pi*(k+2) -> infinity`), not assumed; the global cylinder target
bounds `1` and `91` are proved privately, not assumed.

LEDGER:
  CLOSES: [F72_0B2_SELECTED_CENTER_NORMALIZED_SOURCE_BIND,
           F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_COMPOSITION]
  OPENS:  []
-/

/-! ## Private exponential-polynomial target bounds -/

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

/-! ## The selected project mode data -/

private def selectedProjectModeData0 (k : ℕ) :
    ProjectModeData (selectedFerrersPaperLambda k)
      (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
        mode4JacobiG (k + 2)) where
  f := (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode
  df := fun y =>
    mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y /
      ((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization : ℂ)
  hasDeriv := fun x hx =>
    normalizedPhysicalMode_hasDerivAt (selectedFerrersPreAnchorSolution0 k)
      (by omega) hx
  flux := by
    intro x hx
    set S := selectedFerrersPreAnchorSolution0 k with hS
    set c : ℂ := (S.physicalL2Normalization : ℂ) with hc
    have hraw := S.physicalComplex_flux_hasDerivAt (show 2 ≤ k + 2 by omega) hx
    have hdiv := hraw.div_const c
    have hfun_eq :
        (fun z : ℝ =>
          (((selectedFerrersPaperLambda k) ^ 2 - z ^ 2 : ℝ) : ℂ) *
            (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
                S.coefficients z / c))
          = fun z : ℝ =>
            ((((Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 2 - z ^ 2 : ℝ) : ℂ) *
              mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
                S.coefficients z) / c := by
      funext z
      rw [show selectedFerrersPaperLambda k = Real.sqrt ((k + 2 : ℕ) : ℝ)
        from rfl]
      ring
    rw [hfun_eq]
    have hxIcc : x ∈ Icc (-Real.sqrt ((k + 2 : ℕ) : ℝ))
        (Real.sqrt ((k + 2 : ℕ) : ℝ)) := ⟨hx.1.le, hx.2.le⟩
    have hval_eq :
        ((((2 * Real.pi * selectedFerrersPaperLambda k * x) ^ 2 : ℝ) : ℂ) -
            ((mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
              mode4JacobiG (k + 2) : ℝ) : ℂ)) *
          S.normalizedPhysicalMode x
          = (((((2 * Real.pi * Real.sqrt ((k + 2 : ℕ) : ℝ) * x) ^ 2 : ℝ) : ℂ) -
              ((mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
                mode4JacobiG (k + 2) : ℝ) : ℂ)) *
            mode4PhysicalFerrersSeriesComplex (k + 2) S.coefficients x) / c := by
      rw [show selectedFerrersPaperLambda k = Real.sqrt ((k + 2 : ℕ) : ℝ)
        from rfl]
      rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
        Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_mem hxIcc]
      ring
    rw [hval_eq]
    exact hdiv
  even := (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode_even
  center_ne := normalizedPhysicalMode_zero_ne
    (selectedFerrersPreAnchorSolution0 k) (by omega)
  normalized_continuousOn := by
    set S := selectedFerrersPreAnchorSolution0 k with hS
    have hphys := (S.physicalComplex_continuousOn_closed
      (show 2 ≤ k + 2 by omega)).div_const (S.physicalL2Normalization : ℂ)
    have hf : ContinuousOn S.normalizedPhysicalMode
        (Icc (-(selectedFerrersPaperLambda k)) (selectedFerrersPaperLambda k)) := by
      refine hphys.congr fun y hy => ?_
      rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
        Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_mem hy]
    exact hf.div_const _

private def selectedProjectModeData4 (k : ℕ) :
    ProjectModeData (selectedFerrersPaperLambda k)
      (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
        mode4JacobiG (k + 2)) where
  f := (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode
  df := fun y =>
    mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y /
      ((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization : ℂ)
  hasDeriv := fun x hx =>
    normalizedPhysicalMode_hasDerivAt (selectedFerrersPreAnchorSolution4 k)
      (by omega) hx
  flux := by
    intro x hx
    set S := selectedFerrersPreAnchorSolution4 k with hS
    set c : ℂ := (S.physicalL2Normalization : ℂ) with hc
    have hraw := S.physicalComplex_flux_hasDerivAt (show 2 ≤ k + 2 by omega) hx
    have hdiv := hraw.div_const c
    have hfun_eq :
        (fun z : ℝ =>
          (((selectedFerrersPaperLambda k) ^ 2 - z ^ 2 : ℝ) : ℂ) *
            (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
                S.coefficients z / c))
          = fun z : ℝ =>
            ((((Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 2 - z ^ 2 : ℝ) : ℂ) *
              mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
                S.coefficients z) / c := by
      funext z
      rw [show selectedFerrersPaperLambda k = Real.sqrt ((k + 2 : ℕ) : ℝ)
        from rfl]
      ring
    rw [hfun_eq]
    have hxIcc : x ∈ Icc (-Real.sqrt ((k + 2 : ℕ) : ℝ))
        (Real.sqrt ((k + 2 : ℕ) : ℝ)) := ⟨hx.1.le, hx.2.le⟩
    have hval_eq :
        ((((2 * Real.pi * selectedFerrersPaperLambda k * x) ^ 2 : ℝ) : ℂ) -
            ((mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
              mode4JacobiG (k + 2) : ℝ) : ℂ)) *
          S.normalizedPhysicalMode x
          = (((((2 * Real.pi * Real.sqrt ((k + 2 : ℕ) : ℝ) * x) ^ 2 : ℝ) : ℂ) -
              ((mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
                mode4JacobiG (k + 2) : ℝ) : ℂ)) *
            mode4PhysicalFerrersSeriesComplex (k + 2) S.coefficients x) / c := by
      rw [show selectedFerrersPaperLambda k = Real.sqrt ((k + 2 : ℕ) : ℝ)
        from rfl]
      rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
        Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_mem hxIcc]
      ring
    rw [hval_eq]
    exact hdiv
  even := (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode_even
  center_ne := normalizedPhysicalMode_zero_ne
    (selectedFerrersPreAnchorSolution4 k) (by omega)
  normalized_continuousOn := by
    set S := selectedFerrersPreAnchorSolution4 k with hS
    have hphys := (S.physicalComplex_continuousOn_closed
      (show 2 ≤ k + 2 by omega)).div_const (S.physicalL2Normalization : ℂ)
    have hf : ContinuousOn S.normalizedPhysicalMode
        (Icc (-(selectedFerrersPaperLambda k)) (selectedFerrersPaperLambda k)) := by
      refine hphys.congr fun y hy => ?_
      rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
        Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_mem hy]
    exact hf.div_const _

/-! ## Selected window and schedule facts -/

private theorem selectedLambda_pos (k : ℕ) :
    0 < selectedFerrersPaperLambda k := by
  rw [selectedFerrersPaperLambda]
  apply Real.sqrt_pos.mpr
  positivity

private theorem selected_denominator_guard (rawC targetCenter : ℝ)
    (hC : 0 < targetCenter) :
    ∀ᶠ k in atTop, 2 * (rawC / selectedFerrersPaperGamma k) ≤ targetCenter := by
  refine eventually_atTop.mpr ⟨⌈2 * rawC / (targetCenter * Real.pi)⌉₊, fun k hk => ?_⟩
  have hpi := Real.pi_pos
  have h1 : 2 * rawC / (targetCenter * Real.pi) ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
  have h2 : 2 * rawC ≤ targetCenter * Real.pi * (k : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at h1
    linarith [h1]
  rw [selectedFerrersPaperGamma_eq]
  push_cast
  have hb : (0 : ℝ) < 2 * Real.pi * ((k : ℝ) + 2) := by positivity
  rw [mul_comm (2 : ℝ) (rawC / (2 * Real.pi * ((k : ℝ) + 2))),
    div_mul_eq_mul_div, div_le_iff₀ hb]
  nlinarith [hpi, hC, sq_nonneg (k : ℝ)]

/-! ## The composition -/

/-- **F72.1C.**  Explicit raw Satz-9 rates on two source families at the
selected project separation values produce the two selected anchored Ferrers
cylinder rates at the physical `lambda^(-2)` scale. -/
theorem selectedFerrers_directCylinderRate_of_explicitSatz9RawRates
    (S0 : ∀ k : ℕ,
      Satz9SourceData
        (selectedFerrersPaperLambda k)
        (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2)))
    (S4 : ∀ k : ℕ,
      Satz9SourceData
        (selectedFerrersPaperLambda k)
        (mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2)))
    (scale0 scale4 : ℕ → ℂ)
    (rawC0 rawC4 : ℝ)
    (hrawC0 : 0 ≤ rawC0)
    (hrawC4 : 0 ≤ rawC4)
    (hscale0 : ∀ k, scale0 k ≠ 0)
    (hscale4 : ∀ k, scale4 k ≠ 0)
    (hraw0 :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖scale0 k * (S0 k).p x -
            ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              rawC0 / selectedFerrersPaperGamma k)
    (hraw4 :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖scale4 k * (S4 k).p x -
            ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              rawC4 / selectedFerrersPaperGamma k) :
    ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            (2 * rawC0 / Real.pi) /
              (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            ((94 * rawC4) / (3 * Real.pi)) /
              (selectedFerrersPaperLambda k) ^ 2 := by
  have hpi := Real.pi_pos
  -- the two F72.1A0 transfers
  have htr0 := centerNormalizedSatz9Rate_of_scaledFixedModeRate
    selectedFerrersPaperLambda selectedFerrersPaperGamma
    (fun k => mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
      mode4JacobiG (k + 2))
    S0 scale0
    (fun x => ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ))
    1 1 rawC0
    selectedLambda_pos
    (fun _ => rfl)
    (by
      show ((parabolicCylinderD 0 (projectCylinderArgument 0) : ℝ) : ℂ)
        = ((1 : ℝ) : ℂ)
      rw [cylinder_centers.1])
    one_pos
    zero_le_one
    (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact targetD0_bound x)
    hrawC0 hscale0 hraw0
    (selected_denominator_guard rawC0 1 one_pos)
  have htr4 := centerNormalizedSatz9Rate_of_scaledFixedModeRate
    selectedFerrersPaperLambda selectedFerrersPaperGamma
    (fun k => mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
      mode4JacobiG (k + 2))
    S4 scale4
    (fun x => ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ))
    3 91 rawC4
    selectedLambda_pos
    (fun _ => rfl)
    (by
      show ((parabolicCylinderD 4 (projectCylinderArgument 0) : ℝ) : ℂ)
        = ((3 : ℝ) : ℂ)
      rw [cylinder_centers.2])
    (by norm_num)
    (by norm_num)
    (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact targetD4_bound x)
    hrawC4 hscale4 hraw4
    (selected_denominator_guard rawC4 3 (by norm_num))
  filter_upwards [htr0, htr4] with k h0k h4k
  intro x hx
  have hlam := selectedLambda_pos k
  constructor
  · -- mode zero
    have hbind := satz9_source_bind_closed hlam (S0 k)
      (selectedProjectModeData0 k) hx
    have heq : centerAnchorScalarZero k *
        (selectedFerrersPreAnchorPair k).h0 x
          = ((1 : ℝ) : ℂ) * centerNormalized (S0 k).p x := by
      rw [centerAnchorScalarZero, selectedFerrersCenterZero,
        selectedFerrersPreAnchorPair_h0_eq_selectedMode]
      rw [← hbind]
      show 1 / (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode 0 *
          (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode x
        = ((1 : ℝ) : ℂ) *
          ((selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode x /
            (selectedFerrersPreAnchorSolution0 k).normalizedPhysicalMode 0)
      push_cast
      rw [one_div_mul_eq_div, one_mul]
    rw [heq]
    refine le_trans (h0k x hx) (le_of_eq ?_)
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    ring
  · -- mode four
    have hbind := satz9_source_bind_closed hlam (S4 k)
      (selectedProjectModeData4 k) hx
    have heq : centerAnchorScalarFour k *
        (selectedFerrersPreAnchorPair k).h4 x
          = ((3 : ℝ) : ℂ) * centerNormalized (S4 k).p x := by
      rw [centerAnchorScalarFour, selectedFerrersCenterFour,
        selectedFerrersPreAnchorPair_h4_eq_selectedMode]
      rw [← hbind]
      show 3 / (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode 0 *
          (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode x
        = ((3 : ℝ) : ℂ) *
          ((selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode x /
            (selectedFerrersPreAnchorSolution4 k).normalizedPhysicalMode 0)
      push_cast
      rw [div_mul_eq_mul_div, mul_div_assoc]
    rw [heq]
    refine le_trans (h4k x hx) (le_of_eq ?_)
    rw [show (3 : ℝ) + 91 = 94 by norm_num]
    ring

#print axioms selectedFerrers_directCylinderRate_of_explicitSatz9RawRates

end Q3.RouteB.D0Pstar

end
