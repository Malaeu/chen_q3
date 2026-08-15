import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalProlateScaling
import Q3.Proofs.RouteB.ProlateSourceCommutation

/-!
# Goal 058 G3: physical Ferrers endpoint-domain Fourier transport

This file instantiates the natural endpoint-domain Fourier theorem for the
accepted physical scaling of a regular even Ferrers solution.  It transports
closed-window continuity, the divergence-form ODE, and both zero-flux limits
through `u = sqrt(mProject) * x` and the real-to-complex embedding.

Fresh supplier preflight at clean HEAD `d24e8a8a` covered all 257 current
Route B modules and 2336 declarations with no proof holes or nonstandard
axioms.  The exact physical-wrapper query returned `CANDIDATE_ONLY`: the
physical derivative/ODE methods and the generic endpoint theorem were
separate suppliers, not the composition below.

The result is only differential-eigenspace preservation.  It does not prove
Fourier scalar proportionality, identify or order a scalar, prove a zero
count, instantiate `ProlatePair`, prove CCM Lemma 7.2, or close Goal 058 G3.
-/

open Complex Filter Set

noncomputable section

namespace Q3.RouteB

/-- Complexification of the accepted physically scaled Ferrers series. -/
noncomputable def mode4PhysicalFerrersSeriesComplex
    (mProject : ℕ) (a : ℕ → ℝ) (u : ℝ) : ℂ :=
  (mode4PhysicalFerrersSeries mProject a u : ℂ)

/-- Complexification of the declared physical first-derivative series. -/
noncomputable def mode4PhysicalFerrersFirstDerivativeSeriesComplex
    (mProject : ℕ) (a : ℕ → ℝ) (u : ℝ) : ℂ :=
  (mode4PhysicalFerrersFirstDerivativeSeries mProject a u : ℂ)

private theorem mode4Physical_scale_maps_closed
    {mProject : ℕ} (hm : 2 ≤ mProject) :
    Set.MapsTo
      (fun u : ℝ ↦ u / Real.sqrt mProject)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject))
      (Icc (-1 : ℝ) 1) := by
  have hs : 0 < Real.sqrt (mProject : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  intro u hu
  constructor
  · rw [le_div_iff₀ hs]
    simpa using hu.1
  · exact (div_le_one hs).2 hu.2

private theorem mode4Physical_scale_tendsto_one
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun u : ℝ ↦ u / s)
      (nhdsWithin s (Iio s))
      (nhdsWithin (1 : ℝ) (Iio 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa [hs.ne'] using
      ((hasDerivAt_id s).div_const s).continuousAt.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact (div_lt_one hs).2 hu

private theorem mode4Physical_scale_tendsto_neg_one
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun u : ℝ ↦ u / s)
      (nhdsWithin (-s) (Ioi (-s)))
      (nhdsWithin (-1 : ℝ) (Ioi (-1))) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa [hs.ne'] using
      ((hasDerivAt_id (-s)).div_const s).continuousAt.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with u hu
    change -1 < u / s
    rw [lt_div_iff₀ hs]
    simpa using hu

/-- The complex physical source is continuous on its exact closed window. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalComplex_continuousOn_closed
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ContinuousOn
      (mode4PhysicalFerrersSeriesComplex mProject S.coefficients)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) := by
  have hreal :
      ContinuousOn
        (mode4PhysicalFerrersSeries mProject S.coefficients)
        (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) := by
    simpa [mode4PhysicalFerrersSeries, Function.comp_def] using
      S.continuousOn_closed.comp
        (continuous_id.div_const (Real.sqrt mProject)).continuousOn
        (mode4Physical_scale_maps_closed hm)
  exact Complex.continuous_ofReal.comp_continuousOn hreal

/-- The declared complex physical first derivative is the actual derivative
in the open physical window. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalComplex_hasDerivAt
    {mProject K : ℕ} {Λ u : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hu : u ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    HasDerivAt
      (mode4PhysicalFerrersSeriesComplex mProject S.coefficients)
      (mode4PhysicalFerrersFirstDerivativeSeriesComplex
        mProject S.coefficients u)
      u := by
  simpa [mode4PhysicalFerrersSeriesComplex,
    mode4PhysicalFerrersFirstDerivativeSeriesComplex] using
      (S.physicalFerrersSeries_hasDerivAt_firstDerivativeSeries hm hu).ofReal_comp

/-- The complex physical weighted derivative has exactly the divergence-form
derivative required by the natural endpoint-domain Fourier theorem. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalComplex_flux_hasDerivAt
    {mProject K : ℕ} {Λ u : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hu : u ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    HasDerivAt
      (fun z : ℝ ↦
        ((((Real.sqrt mProject) ^ 2 - z ^ 2 : ℝ) : ℂ) *
          mode4PhysicalFerrersFirstDerivativeSeriesComplex
            mProject S.coefficients z))
      (((((2 * Real.pi * Real.sqrt mProject * u) ^ 2 : ℝ) : ℂ) -
          ((Λ + mode4JacobiG mProject : ℝ) : ℂ)) *
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients u)
      u := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hsq : (Real.sqrt (mProject : ℝ)) ^ 2 = (mProject : ℝ) :=
    Real.sq_sqrt hmR.le
  have hp :
      HasDerivAt
        (fun z : ℝ ↦ ((((Real.sqrt mProject) ^ 2 - z ^ 2 : ℝ) : ℂ)))
        (((-2 * u : ℝ) : ℂ)) u := by
    convert
      ((hasDerivAt_const u ((Real.sqrt mProject) ^ 2)).sub
        (hasDerivAt_pow 2 u)).ofReal_comp using 1
    all_goals norm_num
  have hd :=
    (S.physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries hm hu).ofReal_comp
  have hprod := hp.mul hd
  convert hprod using 1
  · have hODE := S.physicalProlateDifferentialEquation hm hu
    rw [hsq]
    simp only [mode4PhysicalFerrersSeriesComplex]
    have hODEC := congrArg (fun t : ℝ ↦ (t : ℂ)) hODE
    push_cast at hODEC ⊢
    linear_combination hODEC

/-- The exact dimensionless zero-flux pair transports to the complex physical
window. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalComplex_zeroFlux_at_endpoints
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    Tendsto
        (fun u : ℝ ↦
          ((((Real.sqrt mProject) ^ 2 - u ^ 2 : ℝ) : ℂ) *
            mode4PhysicalFerrersFirstDerivativeSeriesComplex
              mProject S.coefficients u))
        (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)))
        (nhds 0) ∧
      Tendsto
        (fun u : ℝ ↦
          ((((Real.sqrt mProject) ^ 2 - u ^ 2 : ℝ) : ℂ) *
            mode4PhysicalFerrersFirstDerivativeSeriesComplex
              mProject S.coefficients u))
        (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)))
        (nhds 0) := by
  let s : ℝ := Real.sqrt (mProject : ℝ)
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hmR
  have hsne : s ≠ 0 := hs.ne'
  have hsq : s ^ 2 = (mProject : ℝ) := Real.sq_sqrt hmR.le
  have hscalePlus := mode4Physical_scale_tendsto_one hs
  have hscaleMinus := mode4Physical_scale_tendsto_neg_one hs
  have hdimPlus := S.zeroFlux_at_endpoints.1.comp hscalePlus
  have hdimMinus := S.zeroFlux_at_endpoints.2.comp hscaleMinus
  have hscaledPlus :
      Tendsto
        (fun u : ℝ ↦
          s * ((1 - (u / s) ^ 2) *
            mode4FerrersFirstDerivativeSeries S.coefficients (u / s)))
        (nhdsWithin s (Iio s)) (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdimPlus
  have hscaledMinus :
      Tendsto
        (fun u : ℝ ↦
          s * ((1 - (u / s) ^ 2) *
            mode4FerrersFirstDerivativeSeries S.coefficients (u / s)))
        (nhdsWithin (-s) (Ioi (-s))) (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdimMinus
  have hrealPlus :
      Tendsto
        (fun u : ℝ ↦
          (s ^ 2 - u ^ 2) *
            mode4PhysicalFerrersFirstDerivativeSeries
              mProject S.coefficients u)
        (nhdsWithin s (Iio s)) (nhds 0) := by
    convert hscaledPlus using 1
    funext u
    simp only [mode4PhysicalFerrersFirstDerivativeSeries]
    change
      (s ^ 2 - u ^ 2) *
          (s⁻¹ * mode4FerrersFirstDerivativeSeries S.coefficients (u / s)) = _
    field_simp [hsne]
  have hrealMinus :
      Tendsto
        (fun u : ℝ ↦
          (s ^ 2 - u ^ 2) *
            mode4PhysicalFerrersFirstDerivativeSeries
              mProject S.coefficients u)
        (nhdsWithin (-s) (Ioi (-s))) (nhds 0) := by
    convert hscaledMinus using 1
    funext u
    simp only [mode4PhysicalFerrersFirstDerivativeSeries]
    change
      (s ^ 2 - u ^ 2) *
          (s⁻¹ * mode4FerrersFirstDerivativeSeries S.coefficients (u / s)) = _
    field_simp [hsne]
  constructor
  · simpa [s, mode4PhysicalFerrersFirstDerivativeSeriesComplex] using
      hrealPlus.ofReal
  · simpa [s, mode4PhysicalFerrersFirstDerivativeSeriesComplex] using
      hrealMinus.ofReal

/-- The finite-Fourier action of an accepted physical Ferrers solution stays
in the same prolate differential eigenspace on the exact physical scale. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalFiniteFourierAction_preservesProlateWaveEigenrelation
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ∀ x : ℝ,
      D0Pstar.prolateWaveExpression (Real.sqrt mProject)
          (D0Pstar.finiteFourierAction (Real.sqrt mProject)
            (mode4PhysicalFerrersSeriesComplex mProject S.coefficients)) x =
        ((Λ + mode4JacobiG mProject : ℝ) : ℂ) *
          D0Pstar.finiteFourierAction (Real.sqrt mProject)
            (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) x := by
  have hs : 0 < Real.sqrt (mProject : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  exact
    D0Pstar.finiteFourierAction_preserves_prolateWaveEigenrelation_of_endpointFlux
      (Real.sqrt mProject) (Λ + mode4JacobiG mProject) hs
      (mode4PhysicalFerrersSeriesComplex mProject S.coefficients)
      (mode4PhysicalFerrersFirstDerivativeSeriesComplex
        mProject S.coefficients)
      (S.physicalComplex_continuousOn_closed hm)
      (fun u hu ↦ S.physicalComplex_hasDerivAt hm hu)
      (fun u hu ↦ S.physicalComplex_flux_hasDerivAt hm hu)
      (S.physicalComplex_zeroFlux_at_endpoints hm).1
      (S.physicalComplex_zeroFlux_at_endpoints hm).2

#print axioms mode4PhysicalFerrersSeriesComplex
#print axioms mode4PhysicalFerrersFirstDerivativeSeriesComplex
#print axioms Mode4FerrersRegularEvenProlateSolution.physicalComplex_continuousOn_closed
#print axioms Mode4FerrersRegularEvenProlateSolution.physicalComplex_hasDerivAt
#print axioms Mode4FerrersRegularEvenProlateSolution.physicalComplex_flux_hasDerivAt
#print axioms Mode4FerrersRegularEvenProlateSolution.physicalComplex_zeroFlux_at_endpoints
#print axioms
  Mode4FerrersRegularEvenProlateSolution.physicalFiniteFourierAction_preservesProlateWaveEigenrelation

end Q3.RouteB
