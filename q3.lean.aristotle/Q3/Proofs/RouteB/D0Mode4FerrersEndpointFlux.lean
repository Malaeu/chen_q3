import Q3.Proofs.RouteB.D0Mode4FerrersProlateDifferentialEquation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

/-!
# Endpoint flux of the mode-four Ferrers source row

The exact tail splice supplies the weighted absolute summability needed to
pass the natural Legendre flux through the Ferrers `tsum`.  The proof uses the
already committed ordinary-Legendre energy bound on `[-1, 1]`; it does not use
the prolate ODE, a spectral index, a matching root, or an endpoint condition as
an input.

This closes only the endpoint-domain leaf for the tail-spliced mode-four row.
It does not construct an unconditional root, select the third even mode,
construct mode zero, prove a finite-Fourier eigenrelation, instantiate an
actual `ProlatePair`, prove the quantitative CCM source rate, or close G1/G3.
-/

open Filter Topology Polynomial

noncomputable section

namespace Q3.RouteB

/-- The endpoint factor turns the ordinary-Legendre energy estimate into a
linear-in-degree summable majorant for each differentiated Ferrers term. -/
theorem mode4Ferrers_fluxTerm_abs_le
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(1 - x ^ 2) *
        mode4FerrersFirstDerivativeTerm a q x|
      ≤ 4 * (((q + 1 : ℕ) : ℝ) * |a q|) := by
  let d : ℝ :=
    (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x
  let N : ℝ :=
    ((2 * q : ℕ) : ℝ) * (((2 * q : ℕ) : ℝ) + 1)
  have hxsum : 0 ≤ 1 + x := by linarith [hx.1]
  have hxdiff : 0 ≤ 1 - x := by linarith [hx.2]
  have hxSq : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hxsum hxdiff]
  have hfactor0 : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr hxSq
  have hfactor1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hN0 : 0 ≤ N := by
    dsimp [N]
    positivity
  have henergy :=
    mode4OrdinaryLegendreEnergyPolynomial_eval_le_endpoint (2 * q) x hx
  simp only [mode4OrdinaryLegendreEnergyPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at henergy
  have hderivativeEnergy : (1 - x ^ 2) * d ^ 2 ≤ N := by
    dsimp [d, N]
    have hmode0 :
        0 ≤ (((2 * q : ℕ) : ℝ) * (((2 * q : ℕ) : ℝ) + 1)) *
          (mode4OrdinaryLegendrePolynomial (2 * q)).eval x ^ 2 := by
      positivity
    nlinarith
  have hfluxSq : ((1 - x ^ 2) * d) ^ 2 ≤ N := by
    calc
      ((1 - x ^ 2) * d) ^ 2 =
          (1 - x ^ 2) * ((1 - x ^ 2) * d ^ 2) := by ring
      _ ≤ (1 - x ^ 2) * N :=
        mul_le_mul_of_nonneg_left hderivativeEnergy hfactor0
      _ ≤ 1 * N := mul_le_mul_of_nonneg_right hfactor1 hN0
      _ = N := one_mul N
  have hNbound :
      N ≤ (4 * (((q + 1 : ℕ) : ℝ))) ^ 2 := by
    dsimp [N]
    push_cast
    nlinarith [sq_nonneg (q : ℝ)]
  have hflux :
      |(1 - x ^ 2) * d| ≤ 4 * (((q + 1 : ℕ) : ℝ)) := by
    have hright : 0 ≤ 4 * (((q + 1 : ℕ) : ℝ)) := by positivity
    nlinarith [sq_abs ((1 - x ^ 2) * d),
      abs_nonneg ((1 - x ^ 2) * d)]
  calc
    |(1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x| =
        |a q| * |(1 - x ^ 2) * d| := by
      simp only [mode4FerrersFirstDerivativeTerm, abs_mul, abs_pow,
        abs_neg, abs_one, one_pow]
      dsimp [d]
      ring
    _ ≤ |a q| * (4 * (((q + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hflux (abs_nonneg _)
    _ = 4 * (((q + 1 : ℕ) : ℝ) * |a q|) := by ring

/-- Weighted absolute summability is exactly the domination budget needed to
pass the right endpoint limit through the differentiated Ferrers series. -/
theorem mode4Ferrers_fluxSeries_tendsto_zero_at_one
    (a : ℕ → ℝ)
    (ha1 : Summable (fun q : ℕ ↦
      (((q + 1 : ℕ) : ℝ) * |a q|))) :
    Filter.Tendsto
      (fun x : ℝ ↦
        (1 - x ^ 2) *
          mode4FerrersFirstDerivativeSeries a x)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (𝓝 0) := by
  let bound : ℕ → ℝ := fun q ↦
    4 * (((q + 1 : ℕ) : ℝ) * |a q|)
  have hboundSummable : Summable bound := by
    simpa [bound] using ha1.mul_left 4
  have hterm (q : ℕ) :
      Tendsto
        (fun x : ℝ ↦
          (1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (𝓝 0) := by
    have hcontinuous : Continuous (fun x : ℝ ↦
        (1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x) := by
      unfold mode4FerrersFirstDerivativeTerm
      fun_prop
    have hat : Tendsto
        (fun x : ℝ ↦
          (1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x)
        (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa [mode4FerrersFirstDerivativeTerm] using
        (hcontinuous.continuousAt (x := (1 : ℝ))).tendsto
    exact hat.mono_left inf_le_left
  have hbound : ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1), ∀ q,
      ‖(1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x‖ ≤
        bound q := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))] with x hxUpper hxLower
    intro q
    rw [Real.norm_eq_abs]
    exact mode4Ferrers_fluxTerm_abs_le a q x
      ⟨le_of_lt hxLower, le_of_lt hxUpper⟩
  have ht := tendsto_tsum_of_dominated_convergence
    hboundSummable hterm hbound
  simpa [mode4FerrersFirstDerivativeSeries, bound, tsum_mul_left] using ht

/-- The same dominated-series argument at the left endpoint. -/
theorem mode4Ferrers_fluxSeries_tendsto_zero_at_neg_one
    (a : ℕ → ℝ)
    (ha1 : Summable (fun q : ℕ ↦
      (((q + 1 : ℕ) : ℝ) * |a q|))) :
    Filter.Tendsto
      (fun x : ℝ ↦
        (1 - x ^ 2) *
          mode4FerrersFirstDerivativeSeries a x)
      (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
      (𝓝 0) := by
  let bound : ℕ → ℝ := fun q ↦
    4 * (((q + 1 : ℕ) : ℝ) * |a q|)
  have hboundSummable : Summable bound := by
    simpa [bound] using ha1.mul_left 4
  have hterm (q : ℕ) :
      Tendsto
        (fun x : ℝ ↦
          (1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x)
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
        (𝓝 0) := by
    have hcontinuous : Continuous (fun x : ℝ ↦
        (1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x) := by
      unfold mode4FerrersFirstDerivativeTerm
      fun_prop
    have hat : Tendsto
        (fun x : ℝ ↦
          (1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x)
        (𝓝 (-1 : ℝ)) (𝓝 0) := by
      simpa [mode4FerrersFirstDerivativeTerm] using
        (hcontinuous.continuousAt (x := (-1 : ℝ))).tendsto
    exact hat.mono_left inf_le_left
  have hbound : ∀ᶠ x in nhdsWithin (-1 : ℝ) (Set.Ioi (-1)), ∀ q,
      ‖(1 - x ^ 2) * mode4FerrersFirstDerivativeTerm a q x‖ ≤
        bound q := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))] with x hxLower hxUpper
    intro q
    rw [Real.norm_eq_abs]
    exact mode4Ferrers_fluxTerm_abs_le a q x
      ⟨le_of_lt hxLower, le_of_lt hxUpper⟩
  have ht := tendsto_tsum_of_dominated_convergence
    hboundSummable hterm hbound
  simpa [mode4FerrersFirstDerivativeSeries, bound, tsum_mul_left] using ht

/-- The exact source tail splice implies the natural zero-flux condition at
both singular endpoints. -/
theorem mode4Ferrers_zeroFlux_at_endpoints_of_tail_splice
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (a : ℕ → ℝ)
    (hsplice : ∀ n : ℕ,
      a (K - 1 + n) =
        a (K - 1) *
          mode4TailCoefficientRow mProject Λ K n) :
    Filter.Tendsto
        (fun x : ℝ ↦
          (1 - x ^ 2) *
            mode4FerrersFirstDerivativeSeries a x)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (𝓝 0) ∧
      Filter.Tendsto
        (fun x : ℝ ↦
          (1 - x ^ 2) *
            mode4FerrersFirstDerivativeSeries a x)
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
        (𝓝 0) := by
  have ha1 : Summable (fun q : ℕ ↦
      (((q + 1 : ℕ) : ℝ) * |a q|)) := by
    simpa using
      (mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
        mProject K Λ hm hK hsep hΛ a hsplice 1)
  exact ⟨mode4Ferrers_fluxSeries_tendsto_zero_at_one a ha1,
    mode4Ferrers_fluxSeries_tendsto_zero_at_neg_one a ha1⟩

/-! ## Planted falsifiers

These guards reject the four forbidden weakenings independently of the public
endpoint theorem.
-/

private theorem mode4OrdinaryLegendrePolynomial_two_derivative_at_one :
    (mode4OrdinaryLegendrePolynomial 2).derivative.eval 1 = 3 := by
  have h := congrArg
    (fun p : ℝ[X] ↦ p.derivative.eval 1)
    (mode4OrdinaryLegendrePolynomial_three_term_succ 0)
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one, Polynomial.derivative_mul] at h
  linarith

private def g3Mode4EndpointFactorPlantRow (q : ℕ) : ℝ :=
  if q = 1 then 1 else 0

-- G3_MODE4_ENDPOINT_FACTOR_MUTATION_SURVIVED:
-- the `1 + x²` mutant is already nonzero at the endpoint on the finite q=1 row.
private theorem g3Mode4EndpointFactorMutation_survived :
    (1 + (1 : ℝ) ^ 2) *
        mode4FerrersFirstDerivativeTerm
          g3Mode4EndpointFactorPlantRow 1 1 ≠ 0 := by
  simp [mode4FerrersFirstDerivativeTerm, g3Mode4EndpointFactorPlantRow,
    mode4OrdinaryLegendrePolynomial_two_derivative_at_one]

private def g3InteriorC2PlantDerivative (x : ℝ) : ℝ :=
  (1 - x ^ 2)⁻¹

-- The derivative field is C² on the open interval despite its endpoint pole.
private theorem g3InteriorC2PlantDerivative_contDiffOn :
    ContDiffOn ℝ 2 g3InteriorC2PlantDerivative (Set.Ioo (-1 : ℝ) 1) := by
  unfold g3InteriorC2PlantDerivative
  apply ContDiffOn.inv
  · fun_prop
  · intro x hx
    have hpos : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos (by linarith [hx.1] : 0 < 1 + x)
        (by linarith [hx.2] : 0 < 1 - x)]
    exact ne_of_gt hpos

private theorem g3InteriorC2PlantDerivative_flux_eq_one
    (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) * g3InteriorC2PlantDerivative x = 1 := by
  have hpos : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (by linarith [hx.1] : 0 < 1 + x)
      (by linarith [hx.2] : 0 < 1 - x)]
  exact mul_inv_cancel₀ (ne_of_gt hpos)

-- G3_INTERIOR_C2_NOT_ENDPOINT_DOMAIN:
-- interior C² alone cannot force zero flux at the singular endpoint.
private theorem g3InteriorC2PlantDerivative_not_zeroFlux :
    ¬ Tendsto
      (fun x : ℝ ↦ (1 - x ^ 2) * g3InteriorC2PlantDerivative x)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (𝓝 0) := by
  intro ht
  rw [Metric.tendsto_nhds] at ht
  have hsmall := ht (1 / 2 : ℝ) (by norm_num)
  have hopen : ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Iio 1),
      x ∈ Set.Ioo (-1 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))] with x hxUpper hxLower
    exact ⟨hxLower, hxUpper⟩
  obtain ⟨x, hxSmall, hxOpen⟩ := (hsmall.and hopen).exists
  rw [g3InteriorC2PlantDerivative_flux_eq_one x hxOpen] at hxSmall
  norm_num [Real.dist_eq] at hxSmall

private def g3L2PlantRow (q : ℕ) : ℝ :=
  1 / ((((q + 1 : ℕ) : ℝ)) ^ 2)

-- G3_L2_TO_WEIGHTED_L1_SHORTCUT:
-- a_q=(q+1)^-2 is square summable, while (q+1)|a_q| is harmonic.
private theorem g3L2PlantRow_squareSummable_not_weightedL1 :
    Summable (fun q : ℕ ↦ (g3L2PlantRow q) ^ 2) ∧
      ¬ Summable (fun q : ℕ ↦
        (((q + 1 : ℕ) : ℝ) * |g3L2PlantRow q|)) := by
  constructor
  · have h4 : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 4)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h4shift := (summable_nat_add_iff 1).2 h4
    convert h4shift using 1
    funext q
    have hq : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    dsimp [g3L2PlantRow]
    field_simp
  · intro hweighted
    have hharmonic : Summable (fun q : ℕ ↦
        1 / (((q + 1 : ℕ) : ℝ))) := by
      convert hweighted using 1
      funext q
      have hqrow : 0 < g3L2PlantRow q := by
        dsimp [g3L2PlantRow]
        positivity
      rw [show |g3L2PlantRow q| = g3L2PlantRow q by
        exact abs_of_pos hqrow]
      dsimp [g3L2PlantRow]
      field_simp
    exact Real.not_summable_one_div_natCast
      ((summable_nat_add_iff 1).1 hharmonic)

-- G3_MODE4_SOURCE_ROW_DROPPED:
-- this named guard compiles only while the exact source tail splice remains
-- the supplier for the weighted domination budget used by the public theorem.
private theorem g3Mode4SourceRowPlant_exact_tail_splice_required
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep : ∀ q ≥ K,
      (31 / 24 : ℝ) * mode4JacobiG mProject ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) (a : ℕ → ℝ)
    (hsplice : ∀ n : ℕ,
      a (K - 1 + n) = a (K - 1) *
        mode4TailCoefficientRow mProject Λ K n) :
    Summable (fun q : ℕ ↦ (((q + 1 : ℕ) : ℝ) * |a q|)) := by
  simpa using
    (mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
      mProject K Λ hm hK hsep hΛ a hsplice 1)

#print axioms mode4Ferrers_fluxTerm_abs_le
#print axioms mode4Ferrers_fluxSeries_tendsto_zero_at_one
#print axioms mode4Ferrers_fluxSeries_tendsto_zero_at_neg_one
#print axioms mode4Ferrers_zeroFlux_at_endpoints_of_tail_splice

end Q3.RouteB
