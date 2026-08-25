import Q3.Proofs.RouteB.G6N1SturmWeightedEnergyIdentity
import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalProlateScaling
import Q3.Proofs.RouteB.D0Mode4FerrersEndpointFlux
import Q3.Proofs.RouteB.G6N1SelectedFerrersPreAnchorDataInhabitant

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# STURM_ENERGY_NODE, part B1: physical mode plumbing (verdict 4c0e13ba)

For a committed Ferrers solution, the physical weighted flux
`(lam² − u²) · physFirstDeriv u` has (i) the exact derivative
`(2π lam u)² · physSeries − θ · physSeries` supplied by the committed
physical prolate ODE, and (ii) zero limits at both singular endpoints,
transported from the committed s-variable zero-flux theorem.  Everything is
per-mode and at the raw (unnormalized) series level; normalization is a
positive scalar handled at assembly.
-/

variable {mProject K : ℕ} {Λ : ℝ}

/-- The exact derivative of the physical weighted flux, from the committed
physical prolate ODE. -/
theorem sturm_mode_flux_hasDerivAt
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) {u : ℝ}
    (hu : u ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    HasDerivAt
      (fun y : ℝ => ((Real.sqrt mProject) ^ 2 - y ^ 2) *
        mode4PhysicalFerrersFirstDerivativeSeries mProject S.coefficients y)
      ((2 * Real.pi * Real.sqrt mProject * u) ^ 2 *
          mode4PhysicalFerrersSeries mProject S.coefficients u -
        (Λ + mode4JacobiG mProject) *
          mode4PhysicalFerrersSeries mProject S.coefficients u) u := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hsq : (Real.sqrt (mProject : ℝ)) ^ 2 = (mProject : ℝ) :=
    Real.sq_sqrt hmR.le
  have hw : HasDerivAt (fun y : ℝ => (Real.sqrt (mProject : ℝ)) ^ 2 - y ^ 2)
      (-(2 * u)) u := by
    have h2 := hasDerivAt_pow 2 u
    have hc := hasDerivAt_const u ((Real.sqrt (mProject : ℝ)) ^ 2)
    exact (hc.sub h2).congr_deriv (by push_cast; ring)
  have hfd := S.physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
    hm hu
  have hprod := hw.mul hfd
  have hODE := S.physicalProlateDifferentialEquation hm hu
  refine hprod.congr_deriv ?_
  rw [hsq]
  nlinarith [hODE]

/-- Transport of the committed s-variable zero flux to the physical top
endpoint. -/
theorem sturm_mode_flux_tendsto_zero_top
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Tendsto
      (fun u : ℝ => ((Real.sqrt mProject) ^ 2 - u ^ 2) *
        mode4PhysicalFerrersFirstDerivativeSeries mProject S.coefficients u)
      (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)))
      (𝓝 0) := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hs : (0 : ℝ) < Real.sqrt (mProject : ℝ) := Real.sqrt_pos.2 hmR
  have hsq : (Real.sqrt (mProject : ℝ)) ^ 2 = (mProject : ℝ) :=
    Real.sq_sqrt hmR.le
  have hzf := (mode4Ferrers_zeroFlux_at_endpoints_of_tail_splice
    mProject K Λ hm hK hsep hΛ S.coefficients S.tail_splice).1
  -- the scale map tends into the s-window
  have hscale : Tendsto (fun u : ℝ => u / Real.sqrt mProject)
      (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)))
      (nhdsWithin (1 : ℝ) (Iio 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : Tendsto (fun u : ℝ => u / Real.sqrt mProject)
          (𝓝 (Real.sqrt mProject)) (𝓝 (Real.sqrt mProject / Real.sqrt mProject)) :=
        (continuous_id.div_const _).tendsto _
      rw [div_self hs.ne'] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact (div_lt_one hs).2 hu
  have hcomp := hzf.comp hscale
  have hconst := hcomp.const_mul (Real.sqrt (mProject : ℝ))
  rw [mul_zero] at hconst
  refine hconst.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u _
  simp only [Function.comp_apply]
  rw [mode4PhysicalFerrersFirstDerivativeSeries]
  have hne : Real.sqrt (mProject : ℝ) ≠ 0 := hs.ne'
  field_simp

/-- Transport of the committed s-variable zero flux to the physical bottom
endpoint. -/
theorem sturm_mode_flux_tendsto_zero_bot
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Tendsto
      (fun u : ℝ => ((Real.sqrt mProject) ^ 2 - u ^ 2) *
        mode4PhysicalFerrersFirstDerivativeSeries mProject S.coefficients u)
      (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)))
      (𝓝 0) := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hs : (0 : ℝ) < Real.sqrt (mProject : ℝ) := Real.sqrt_pos.2 hmR
  have hsq : (Real.sqrt (mProject : ℝ)) ^ 2 = (mProject : ℝ) :=
    Real.sq_sqrt hmR.le
  have hzf := (mode4Ferrers_zeroFlux_at_endpoints_of_tail_splice
    mProject K Λ hm hK hsep hΛ S.coefficients S.tail_splice).2
  have hscale : Tendsto (fun u : ℝ => u / Real.sqrt mProject)
      (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)))
      (nhdsWithin (-1 : ℝ) (Ioi (-1))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : Tendsto (fun u : ℝ => u / Real.sqrt mProject)
          (𝓝 (-Real.sqrt mProject))
          (𝓝 (-Real.sqrt mProject / Real.sqrt mProject)) :=
        (continuous_id.div_const _).tendsto _
      rw [neg_div, div_self hs.ne'] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      rw [Set.mem_Ioi, lt_div_iff₀ hs]
      simpa using hu
  have hcomp := hzf.comp hscale
  have hconst := hcomp.const_mul (Real.sqrt (mProject : ℝ))
  rw [mul_zero] at hconst
  refine hconst.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u _
  simp only [Function.comp_apply]
  rw [mode4PhysicalFerrersFirstDerivativeSeries]
  have hne : Real.sqrt (mProject : ℝ) ≠ 0 := hs.ne'
  field_simp

#print axioms sturm_mode_flux_hasDerivAt
#print axioms sturm_mode_flux_tendsto_zero_top
#print axioms sturm_mode_flux_tendsto_zero_bot

end Q3.RouteB.D0Pstar
