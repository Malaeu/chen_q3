import Q3.Proofs.RouteB.G6N1SturmDefectEnergyModePlumbing
import Q3.Proofs.RouteB.D0Mode4FerrersCoefficientAbsoluteSummability

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# STURM_ENERGY_NODE, part B2: the defect truncated energy bound

For the per-mode defect `δ = c·(physical Ferrers series) − W` against any
C²-cylinder profile `W`, the truncated weighted energy obeys the abstract
bound of part A with the EXACT source
`r(u) = c·((2πλu)²·S − θ·S) + 2u·W′(u) − (λ²−u²)·W″(u)`
supplied by the committed physical prolate ODE (part B1) and the product
rule.  No integrability of the energy is assumed anywhere; the anchoring
constant and the C0 ledger enter only downstream.
-/

variable {mProject K : ℕ} {Λ : ℝ}

/-- The physical series is continuous on the closed physical window. -/
theorem sturm_physSeries_continuousOn_closed
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ContinuousOn
      (mode4PhysicalFerrersSeries mProject S.coefficients)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hs : (0 : ℝ) < Real.sqrt (mProject : ℝ) := Real.sqrt_pos.2 hmR
  have hbase := mode4FerrersSeries_continuousOn S.coefficients
    S.coefficients_abs_summable
  have hscale : ContinuousOn (fun u : ℝ => u / Real.sqrt mProject)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) :=
    (continuous_id.div_const _).continuousOn
  have hmaps : MapsTo (fun u : ℝ => u / Real.sqrt mProject)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject))
      (Icc (-1 : ℝ) 1) := by
    intro u hu
    constructor
    · rw [le_div_iff₀ hs]
      simpa using hu.1
    · rw [div_le_one hs]
      exact hu.2
  exact hbase.comp hscale hmaps

/--
**The defect truncated energy bound.**  Instantiation of
`sturm_weighted_energy_truncated_bound` on `δ = c·physSeries − W`.
-/
theorem sturm_defect_truncated_energy_bound
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (c : ℝ) (W Wd Wdd : ℝ → ℝ)
    (hW : ∀ y : ℝ, HasDerivAt W (Wd y) y)
    (hWd : ∀ y : ℝ, HasDerivAt Wd (Wdd y) y)
    (hWcont : Continuous W)
    (hWddcont : Continuous Wdd)
    (a b : ℝ) (hab : a ≤ b)
    (haI : a ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject))
    (hbI : b ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    (∫ x in a..b, ((Real.sqrt mProject) ^ 2 - x ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients x - Wd x) ^ 2) ≤
      |((Real.sqrt mProject) ^ 2 - b ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients b - Wd b) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients b - W b)| +
      |((Real.sqrt mProject) ^ 2 - a ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients a - Wd a) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients a - W a)| +
      ∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        |(c * ((2 * Real.pi * Real.sqrt mProject * x) ^ 2 *
              mode4PhysicalFerrersSeries mProject S.coefficients x -
            (Λ + mode4JacobiG mProject) *
              mode4PhysicalFerrersSeries mProject S.coefficients x) +
          2 * x * Wd x - ((Real.sqrt mProject) ^ 2 - x ^ 2) * Wdd x) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients x - W x)| := by
  set lam := Real.sqrt (mProject : ℝ) with hlamdef
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hlam0 : (0 : ℝ) < lam := Real.sqrt_pos.2 hmR
  set g : ℝ → ℝ := fun u =>
    c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u with hg
  set gd : ℝ → ℝ := fun u =>
    c * mode4PhysicalFerrersFirstDerivativeSeries mProject
      S.coefficients u - Wd u with hgd
  set r : ℝ → ℝ := fun u =>
    c * ((2 * Real.pi * lam * u) ^ 2 *
        mode4PhysicalFerrersSeries mProject S.coefficients u -
      (Λ + mode4JacobiG mProject) *
        mode4PhysicalFerrersSeries mProject S.coefficients u) +
      2 * u * Wd u - (lam ^ 2 - u ^ 2) * Wdd u with hr
  have hgderiv : ∀ x ∈ Ioo (-lam) lam, HasDerivAt g (gd x) x := by
    intro x hx
    have h1 := (S.physicalFerrersSeries_hasDerivAt_firstDerivativeSeries
      hm hx).const_mul c
    have h2 := hW x
    have h := h1.sub h2
    exact h.congr_deriv rfl
  have hrderiv : ∀ x ∈ Ioo (-lam) lam,
      HasDerivAt (fun y : ℝ => (lam ^ 2 - y ^ 2) * gd y) (r x) x := by
    intro x hx
    have hmode := (sturm_mode_flux_hasDerivAt S hm hx).const_mul c
    have hwexpr : HasDerivAt (fun y : ℝ => (lam ^ 2 - y ^ 2) * Wd y)
        ((-(2 * x)) * Wd x + (lam ^ 2 - x ^ 2) * Wdd x) x := by
      have hwq : HasDerivAt (fun y : ℝ => lam ^ 2 - y ^ 2) (-(2 * x)) x := by
        have h2 := hasDerivAt_pow 2 x
        have hc := hasDerivAt_const x (lam ^ 2)
        exact (hc.sub h2).congr_deriv (by push_cast; ring)
      exact hwq.mul (hWd x)
    have hcomb : HasDerivAt (fun y : ℝ =>
        c * ((lam ^ 2 - y ^ 2) *
          mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients y) -
        (lam ^ 2 - y ^ 2) * Wd y)
        (c * ((2 * Real.pi * lam * x) ^ 2 *
            mode4PhysicalFerrersSeries mProject S.coefficients x -
          (Λ + mode4JacobiG mProject) *
            mode4PhysicalFerrersSeries mProject S.coefficients x) -
          ((-(2 * x)) * Wd x + (lam ^ 2 - x ^ 2) * Wdd x)) x :=
      hmode.sub hwexpr
    have hfun : (fun y : ℝ =>
        c * ((lam ^ 2 - y ^ 2) *
          mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients y) -
        (lam ^ 2 - y ^ 2) * Wd y) =
        fun y : ℝ => (lam ^ 2 - y ^ 2) * gd y := by
      funext y
      rw [hgd]
      ring
    rw [hfun] at hcomb
    exact hcomb.congr_deriv (by rw [hr]; ring)
  have hWdcont : Continuous Wd :=
    continuous_iff_continuousAt.mpr fun x => (hWd x).continuousAt
  have hWcont' : Continuous W :=
    continuous_iff_continuousAt.mpr fun x => (hW x).continuousAt
  have hphys_closed := sturm_physSeries_continuousOn_closed S hm
  have hsub : Ioo (-lam) lam ⊆ Icc (-lam) lam := Ioo_subset_Icc_self
  have hg_cont_closed : ContinuousOn g (Icc (-lam) lam) := by
    rw [hg]
    exact ((hphys_closed.const_smul c).congr
      (fun x _ => by simp [smul_eq_mul])).sub hWcont'.continuousOn
  have hcont_gd : ContinuousOn gd (Ioo (-lam) lam) := by
    intro x hx
    have h1 := (S.physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
      hm hx).continuousAt
    have h2 := (hWd x).continuousAt
    have h3 : ContinuousAt gd x := by
      rw [hgd]
      exact (continuousAt_const.mul h1).sub h2
    exact h3.continuousWithinAt
  have hr_cont_closed : ContinuousOn r (Icc (-lam) lam) := by
    rw [hr]
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.sub
        · apply ContinuousOn.mul _ hphys_closed
          fun_prop
        · exact continuousOn_const.mul hphys_closed
      · exact (continuousOn_const.mul continuousOn_id).mul
          hWdcont.continuousOn
    · exact (continuousOn_const.sub (continuous_pow 2).continuousOn).mul
        hWddcont.continuousOn
  have hcont_rg : ContinuousOn (fun x : ℝ => r x * g x) (Ioo (-lam) lam) :=
    ((hr_cont_closed.mono hsub).mul (hg_cont_closed.mono hsub))
  have hint1 : IntegrableOn (fun x : ℝ => r x * g x)
      (Ioo (-lam) lam) volume := by
    apply MeasureTheory.IntegrableOn.mono_set (t := Icc (-lam) lam)
    · exact (hr_cont_closed.mul hg_cont_closed).integrableOn_compact
        isCompact_Icc
    · exact hsub
  exact sturm_weighted_energy_truncated_bound lam hlam0 g gd r
    hgderiv hrderiv hcont_gd hcont_rg hint1 a b hab haI hbI

#print axioms sturm_physSeries_continuousOn_closed
#print axioms sturm_defect_truncated_energy_bound

end Q3.RouteB.D0Pstar
