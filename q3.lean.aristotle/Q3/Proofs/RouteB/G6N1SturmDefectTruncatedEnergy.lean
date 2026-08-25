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

/-!
## Part B3a: the defect flux vanishes at both singular endpoints

The physical part of the flux dies by the committed zero-flux transport
(part B1); the cylinder part dies because the weight `λ² − u²` vanishes at
the endpoint while `W`, `W′` and the defect stay bounded.
-/

/-- The defect flux vanishes at the physical top endpoint. -/
theorem sturm_defect_flux_tendsto_zero_top
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (c : ℝ) (W Wd : ℝ → ℝ)
    (hWcont : Continuous W) (hWdcont : Continuous Wd) :
    Tendsto
      (fun u : ℝ => ((Real.sqrt mProject) ^ 2 - u ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients u - Wd u) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u))
      (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)))
      (𝓝 0) := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hlam0 : (0 : ℝ) < Real.sqrt mProject := Real.sqrt_pos.2 hmR
  have h1 := sturm_mode_flux_tendsto_zero_top S hm hK hsep hΛ
  have hIooIio :
      nhdsWithin (Real.sqrt mProject)
        (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) =
      nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)) :=
    nhdsWithin_Ioo_eq_nhdsLT (by linarith)
  have hmem : Real.sqrt mProject ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
    constructor <;> linarith
  have hSt : Tendsto (mode4PhysicalFerrersSeries mProject S.coefficients)
      (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)))
      (𝓝 (mode4PhysicalFerrersSeries mProject S.coefficients
        (Real.sqrt mProject))) := by
    have hphys := sturm_physSeries_continuousOn_closed S hm
    have hcw : Tendsto (mode4PhysicalFerrersSeries mProject S.coefficients)
        (nhdsWithin (Real.sqrt mProject)
          (Icc (-Real.sqrt mProject) (Real.sqrt mProject)))
        (𝓝 (mode4PhysicalFerrersSeries mProject S.coefficients
          (Real.sqrt mProject))) := hphys _ hmem
    rw [← hIooIio]
    exact hcw.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have hWt : Tendsto W
      (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)))
      (𝓝 (W (Real.sqrt mProject))) :=
    (hWcont.tendsto _).mono_left nhdsWithin_le_nhds
  have hWdt : Tendsto Wd
      (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)))
      (𝓝 (Wd (Real.sqrt mProject))) :=
    (hWdcont.tendsto _).mono_left nhdsWithin_le_nhds
  have hwt : Tendsto (fun u : ℝ => (Real.sqrt mProject) ^ 2 - u ^ 2)
      (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject)))
      (𝓝 ((Real.sqrt mProject) ^ 2 - (Real.sqrt mProject) ^ 2)) :=
    ((continuous_const.sub (continuous_pow 2)).tendsto _).mono_left
      nhdsWithin_le_nhds
  have T := ((h1.const_mul c).sub (hwt.mul hWdt)).mul
    ((hSt.const_mul c).sub hWt)
  have hval : (c * 0 -
      ((Real.sqrt mProject) ^ 2 - (Real.sqrt mProject) ^ 2) *
        Wd (Real.sqrt mProject)) *
      (c * mode4PhysicalFerrersSeries mProject S.coefficients
          (Real.sqrt mProject) - W (Real.sqrt mProject)) = 0 := by ring
  rw [hval] at T
  exact T.congr fun u => by ring

/-- The defect flux vanishes at the physical bottom endpoint. -/
theorem sturm_defect_flux_tendsto_zero_bot
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (c : ℝ) (W Wd : ℝ → ℝ)
    (hWcont : Continuous W) (hWdcont : Continuous Wd) :
    Tendsto
      (fun u : ℝ => ((Real.sqrt mProject) ^ 2 - u ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients u - Wd u) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u))
      (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)))
      (𝓝 0) := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hlam0 : (0 : ℝ) < Real.sqrt mProject := Real.sqrt_pos.2 hmR
  have h1 := sturm_mode_flux_tendsto_zero_bot S hm hK hsep hΛ
  have hIooIoi :
      nhdsWithin (-Real.sqrt mProject)
        (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) =
      nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)) :=
    nhdsWithin_Ioo_eq_nhdsGT (by linarith)
  have hmem : -Real.sqrt mProject ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
    constructor <;> linarith
  have hSt : Tendsto (mode4PhysicalFerrersSeries mProject S.coefficients)
      (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)))
      (𝓝 (mode4PhysicalFerrersSeries mProject S.coefficients
        (-Real.sqrt mProject))) := by
    have hphys := sturm_physSeries_continuousOn_closed S hm
    have hcw : Tendsto (mode4PhysicalFerrersSeries mProject S.coefficients)
        (nhdsWithin (-Real.sqrt mProject)
          (Icc (-Real.sqrt mProject) (Real.sqrt mProject)))
        (𝓝 (mode4PhysicalFerrersSeries mProject S.coefficients
          (-Real.sqrt mProject))) := hphys _ hmem
    rw [← hIooIoi]
    exact hcw.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have hWt : Tendsto W
      (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)))
      (𝓝 (W (-Real.sqrt mProject))) :=
    (hWcont.tendsto _).mono_left nhdsWithin_le_nhds
  have hWdt : Tendsto Wd
      (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)))
      (𝓝 (Wd (-Real.sqrt mProject))) :=
    (hWdcont.tendsto _).mono_left nhdsWithin_le_nhds
  have hwt : Tendsto (fun u : ℝ => (Real.sqrt mProject) ^ 2 - u ^ 2)
      (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject)))
      (𝓝 ((Real.sqrt mProject) ^ 2 - (-Real.sqrt mProject) ^ 2)) :=
    ((continuous_const.sub (continuous_pow 2)).tendsto _).mono_left
      nhdsWithin_le_nhds
  have T := ((h1.const_mul c).sub (hwt.mul hWdt)).mul
    ((hSt.const_mul c).sub hWt)
  have hval : (c * 0 -
      ((Real.sqrt mProject) ^ 2 - (-Real.sqrt mProject) ^ 2) *
        Wd (-Real.sqrt mProject)) *
      (c * mode4PhysicalFerrersSeries mProject S.coefficients
          (-Real.sqrt mProject) - W (-Real.sqrt mProject)) = 0 := by ring
  rw [hval] at T
  exact T.congr fun u => by ring

/-!
## Part B3b: the defect energy is integrable on the open window

Exhaust the open physical window by the compacts
`Icc (−λ + λ/(n+2)) (λ − λ/(n+2))`.  On each compact the truncated bound
(part B2) holds; the flux terms vanish along the exhaustion (part B3a), so
the truncated energies are eventually bounded by the source integral plus
one, and Mathlib's `AECover` machinery upgrades this to integrability of
the weighted energy on the open window together with the clean bound
`∫ (λ² − x²) δ′² ≤ ∫ |r·δ|`.
-/

/-- **The defect energy bound.**  The weighted defect energy is integrable
on the open physical window and is bounded by the integral of the exact
source `|r·δ|` — no flux terms remain. -/
theorem sturm_defect_energy_integrable_and_bound
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (c : ℝ) (W Wd Wdd : ℝ → ℝ)
    (hW : ∀ y : ℝ, HasDerivAt W (Wd y) y)
    (hWd : ∀ y : ℝ, HasDerivAt Wd (Wdd y) y)
    (hWcont : Continuous W)
    (hWddcont : Continuous Wdd) :
    IntegrableOn
      (fun x : ℝ => ((Real.sqrt mProject) ^ 2 - x ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients x - Wd x) ^ 2)
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) volume ∧
    (∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        ((Real.sqrt mProject) ^ 2 - x ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients x - Wd x) ^ 2) ≤
      ∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        |(c * ((2 * Real.pi * Real.sqrt mProject * x) ^ 2 *
              mode4PhysicalFerrersSeries mProject S.coefficients x -
            (Λ + mode4JacobiG mProject) *
              mode4PhysicalFerrersSeries mProject S.coefficients x) +
          2 * x * Wd x - ((Real.sqrt mProject) ^ 2 - x ^ 2) * Wdd x) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients x - W x)| := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hlam0 : (0 : ℝ) < Real.sqrt mProject := Real.sqrt_pos.2 hmR
  have hWdcont : Continuous Wd :=
    continuous_iff_continuousAt.mpr fun x => (hWd x).continuousAt
  -- the exhausting sequences
  set aseq : ℕ → ℝ :=
    fun n => -Real.sqrt mProject + Real.sqrt mProject / ((n : ℝ) + 2)
    with haseq
  set bseq : ℕ → ℝ :=
    fun n => Real.sqrt mProject - Real.sqrt mProject / ((n : ℝ) + 2)
    with hbseq
  have hd_pos : ∀ n : ℕ, 0 < Real.sqrt mProject / ((n : ℝ) + 2) := by
    intro n; positivity
  have hd_le : ∀ n : ℕ, Real.sqrt mProject / ((n : ℝ) + 2) ≤
      Real.sqrt mProject := by
    intro n
    apply div_le_self hlam0.le
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have haI : ∀ n : ℕ,
      aseq n ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject) := by
    intro n
    have h1 := hd_pos n
    have h2 := hd_le n
    constructor
    · simp only [haseq]; linarith
    · simp only [haseq]; linarith
  have hbI : ∀ n : ℕ,
      bseq n ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject) := by
    intro n
    have h1 := hd_pos n
    have h2 := hd_le n
    constructor
    · simp only [hbseq]; linarith
    · simp only [hbseq]; linarith
  have hab : ∀ n : ℕ, aseq n ≤ bseq n := by
    intro n
    have h1 := hd_le n
    simp only [haseq, hbseq]
    linarith
  -- convergence of the endpoints
  have hn2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hd0 : Tendsto (fun n : ℕ => Real.sqrt mProject / ((n : ℝ) + 2))
      atTop (𝓝 0) := hn2.const_div_atTop _
  have ha_nhds : Tendsto aseq atTop (𝓝 (-Real.sqrt mProject)) := by
    have h := (tendsto_const_nhds
      (x := -Real.sqrt mProject) (f := (atTop : Filter ℕ))).add hd0
    simpa [haseq] using h
  have hb_nhds : Tendsto bseq atTop (𝓝 (Real.sqrt mProject)) := by
    have h := (tendsto_const_nhds
      (x := Real.sqrt mProject) (f := (atTop : Filter ℕ))).sub hd0
    simpa [hbseq] using h
  have ha_within : Tendsto aseq atTop
      (nhdsWithin (-Real.sqrt mProject) (Ioi (-Real.sqrt mProject))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha_nhds
    filter_upwards with n
    exact Set.mem_Ioi.mpr (haI n).1
  have hb_within : Tendsto bseq atTop
      (nhdsWithin (Real.sqrt mProject) (Iio (Real.sqrt mProject))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hb_nhds
    filter_upwards with n
    exact Set.mem_Iio.mpr (hbI n).2
  -- flux terms vanish along the exhaustion
  have habs_top : Tendsto (fun n : ℕ =>
      |((Real.sqrt mProject) ^ 2 - bseq n ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients (bseq n) - Wd (bseq n)) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients (bseq n) -
          W (bseq n))|) atTop (𝓝 0) := by
    have h := ((sturm_defect_flux_tendsto_zero_top S hm hK hsep hΛ c W Wd
      hWcont hWdcont).comp hb_within).abs
    simpa [Function.comp] using h
  have habs_bot : Tendsto (fun n : ℕ =>
      |((Real.sqrt mProject) ^ 2 - aseq n ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients (aseq n) - Wd (aseq n)) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients (aseq n) -
          W (aseq n))|) atTop (𝓝 0) := by
    have h := ((sturm_defect_flux_tendsto_zero_bot S hm hK hsep hΛ c W Wd
      hWcont hWdcont).comp ha_within).abs
    simpa [Function.comp] using h
  -- the truncated bound on every window of the exhaustion
  have hB2 : ∀ n : ℕ,
      (∫ x in (aseq n)..(bseq n),
        ((Real.sqrt mProject) ^ 2 - x ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients x - Wd x) ^ 2) ≤
      |((Real.sqrt mProject) ^ 2 - bseq n ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients (bseq n) - Wd (bseq n)) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients (bseq n) -
            W (bseq n))| +
      |((Real.sqrt mProject) ^ 2 - aseq n ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients (aseq n) - Wd (aseq n)) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients (aseq n) -
            W (aseq n))| +
      ∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        |(c * ((2 * Real.pi * Real.sqrt mProject * x) ^ 2 *
              mode4PhysicalFerrersSeries mProject S.coefficients x -
            (Λ + mode4JacobiG mProject) *
              mode4PhysicalFerrersSeries mProject S.coefficients x) +
          2 * x * Wd x - ((Real.sqrt mProject) ^ 2 - x ^ 2) * Wdd x) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients x - W x)| :=
    fun n => sturm_defect_truncated_energy_bound S hm c W Wd Wdd hW hWd
      hWcont hWddcont (aseq n) (bseq n) (hab n) (haI n) (hbI n)
  -- continuity of the energy integrand inside the open window
  have hcont_gd : ContinuousOn
      (fun u : ℝ => c * mode4PhysicalFerrersFirstDerivativeSeries mProject
        S.coefficients u - Wd u)
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) := by
    intro x hx
    have h1 := (S.physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
      hm hx).continuousAt
    have h2 := (hWd x).continuousAt
    exact ((continuousAt_const.mul h1).sub h2).continuousWithinAt
  have hep_cont : ContinuousOn
      (fun x : ℝ => ((Real.sqrt mProject) ^ 2 - x ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients x - Wd x) ^ 2)
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :=
    (continuousOn_const.sub (continuous_pow 2).continuousOn).mul
      (hcont_gd.pow 2)
  have hIccSub : ∀ n : ℕ, Icc (aseq n) (bseq n) ⊆
      Ioo (-Real.sqrt mProject) (Real.sqrt mProject) := fun n =>
    Icc_subset_Ioo (haI n).1 (hbI n).2
  -- integrability on each compact of the exhaustion
  have hfi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => ((Real.sqrt mProject) ^ 2 - x ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients x - Wd x) ^ 2)
      (Icc (aseq n) (bseq n))
      (volume.restrict (Ioo (-Real.sqrt mProject) (Real.sqrt mProject))) := by
    intro n
    have h1 : IntegrableOn
        (fun x : ℝ => ((Real.sqrt mProject) ^ 2 - x ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients x - Wd x) ^ 2)
        (Icc (aseq n) (bseq n)) volume :=
      (hep_cont.mono (hIccSub n)).integrableOn_compact isCompact_Icc
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_self_of_subset_left (hIccSub n)]
    exact h1
  -- nonnegativity on the open window
  have hnng : ∀ᵐ x ∂(volume.restrict
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject))),
      0 ≤ ((Real.sqrt mProject) ^ 2 - x ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients x - Wd x) ^ 2 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with x hx
    have h1 : x ^ 2 < (Real.sqrt mProject) ^ 2 := by
      nlinarith [hx.1, hx.2]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  -- translate the covered integrals into interval integrals
  have key : ∀ n : ℕ,
      (∫ x in Icc (aseq n) (bseq n),
        ((Real.sqrt mProject) ^ 2 - x ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients x - Wd x) ^ 2
        ∂(volume.restrict (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)))) =
      ∫ x in (aseq n)..(bseq n),
        ((Real.sqrt mProject) ^ 2 - x ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients x - Wd x) ^ 2 := by
    intro n
    rw [Measure.restrict_restrict measurableSet_Icc,
      inter_eq_self_of_subset_left (hIccSub n),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (hab n)]
  -- the a.e. cover
  have hcov : AECover
      (volume.restrict (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)))
      atTop (fun n : ℕ => Icc (aseq n) (bseq n)) :=
    aecover_Ioo_of_Icc ha_nhds hb_nhds
  -- integrability on the open window
  have hint : Integrable
      (fun x : ℝ => ((Real.sqrt mProject) ^ 2 - x ^ 2) *
        (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients x - Wd x) ^ 2)
      (volume.restrict (Ioo (-Real.sqrt mProject) (Real.sqrt mProject))) := by
    apply hcov.integrable_of_integral_bounded_of_nonneg_ae
      ((∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        |(c * ((2 * Real.pi * Real.sqrt mProject * x) ^ 2 *
              mode4PhysicalFerrersSeries mProject S.coefficients x -
            (Λ + mode4JacobiG mProject) *
              mode4PhysicalFerrersSeries mProject S.coefficients x) +
          2 * x * Wd x - ((Real.sqrt mProject) ^ 2 - x ^ 2) * Wdd x) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients x -
            W x)|) + 1) hfi hnng
    filter_upwards [habs_top.eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
      habs_bot.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with n h1 h2
    rw [key n]
    have h3 := hB2 n
    linarith
  constructor
  · exact hint
  -- pass to the limit in the truncated bounds
  · have htend := hcov.integral_tendsto_of_countably_generated hint
    have hlim2 : Tendsto (fun n : ℕ =>
        |((Real.sqrt mProject) ^ 2 - bseq n ^ 2) *
            (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
                S.coefficients (bseq n) - Wd (bseq n)) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients
                (bseq n) - W (bseq n))| +
          |((Real.sqrt mProject) ^ 2 - aseq n ^ 2) *
            (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
                S.coefficients (aseq n) - Wd (aseq n)) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients
                (aseq n) - W (aseq n))| +
          ∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
            |(c * ((2 * Real.pi * Real.sqrt mProject * x) ^ 2 *
                  mode4PhysicalFerrersSeries mProject S.coefficients x -
                (Λ + mode4JacobiG mProject) *
                  mode4PhysicalFerrersSeries mProject S.coefficients x) +
              2 * x * Wd x -
                ((Real.sqrt mProject) ^ 2 - x ^ 2) * Wdd x) *
              (c * mode4PhysicalFerrersSeries mProject S.coefficients x -
                W x)|) atTop
        (𝓝 (0 + 0 +
          ∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
            |(c * ((2 * Real.pi * Real.sqrt mProject * x) ^ 2 *
                  mode4PhysicalFerrersSeries mProject S.coefficients x -
                (Λ + mode4JacobiG mProject) *
                  mode4PhysicalFerrersSeries mProject S.coefficients x) +
              2 * x * Wd x -
                ((Real.sqrt mProject) ^ 2 - x ^ 2) * Wdd x) *
              (c * mode4PhysicalFerrersSeries mProject S.coefficients x -
                W x)|)) :=
      (habs_top.add habs_bot).add tendsto_const_nhds
    have hle := le_of_tendsto_of_tendsto' htend hlim2 (fun n => by
      rw [key n]
      exact hB2 n)
    simpa using hle

/-!
## Part B4: the signed defect energy identity

With flux limits (B3a) and both integrabilities (B2 source, B3b energy) in
hand, the abstract part-A identity applies verbatim: the defect energy
EQUALS minus the signed source integral.  The absolute-value bound of B3b
is superseded — the sign of the source is now available to the ledger.
-/

/-- **The signed defect energy identity.** -/
theorem sturm_defect_energy_identity
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (c : ℝ) (W Wd Wdd : ℝ → ℝ)
    (hW : ∀ y : ℝ, HasDerivAt W (Wd y) y)
    (hWd : ∀ y : ℝ, HasDerivAt Wd (Wdd y) y)
    (hWcont : Continuous W)
    (hWddcont : Continuous Wdd) :
    (∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        ((Real.sqrt mProject) ^ 2 - x ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients x - Wd x) ^ 2) =
      -∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        (c * ((2 * Real.pi * Real.sqrt mProject * x) ^ 2 *
              mode4PhysicalFerrersSeries mProject S.coefficients x -
            (Λ + mode4JacobiG mProject) *
              mode4PhysicalFerrersSeries mProject S.coefficients x) +
          2 * x * Wd x - ((Real.sqrt mProject) ^ 2 - x ^ 2) * Wdd x) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients x - W x) := by
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
    exact (h1.sub h2).congr_deriv rfl
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
  have hphys_closed := sturm_physSeries_continuousOn_closed S hm
  have hsub : Ioo (-lam) lam ⊆ Icc (-lam) lam := Ioo_subset_Icc_self
  have hg_cont_closed : ContinuousOn g (Icc (-lam) lam) := by
    rw [hg]
    exact ((hphys_closed.const_smul c).congr
      (fun x _ => by simp [smul_eq_mul])).sub hWcont.continuousOn
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
  have hint1 : IntegrableOn (fun x : ℝ => r x * g x)
      (Ioo (-lam) lam) volume := by
    apply MeasureTheory.IntegrableOn.mono_set (t := Icc (-lam) lam)
    · exact (hr_cont_closed.mul hg_cont_closed).integrableOn_compact
        isCompact_Icc
    · exact hsub
  have hint2 : IntegrableOn (fun x : ℝ => (lam ^ 2 - x ^ 2) * gd x ^ 2)
      (Ioo (-lam) lam) volume :=
    (sturm_defect_energy_integrable_and_bound S hm hK hsep hΛ c W Wd Wdd
      hW hWd hWcont hWddcont).1
  have hflux_top : Tendsto (fun x : ℝ => (lam ^ 2 - x ^ 2) * gd x * g x)
      (nhdsWithin lam (Iio lam)) (𝓝 0) :=
    sturm_defect_flux_tendsto_zero_top S hm hK hsep hΛ c W Wd hWcont hWdcont
  have hflux_bot : Tendsto (fun x : ℝ => (lam ^ 2 - x ^ 2) * gd x * g x)
      (nhdsWithin (-lam) (Ioi (-lam))) (𝓝 0) :=
    sturm_defect_flux_tendsto_zero_bot S hm hK hsep hΛ c W Wd hWcont hWdcont
  exact sturm_weighted_energy_identity lam hlam0 g gd r hgderiv hrderiv
    hflux_top hflux_bot hint1 hint2

/-!
## Part B5: the rate ledger

Signed pointwise algebra on the source (verified symbolically): with the
cylinder eigenrelation `W″ = (4π²u² − μ)W` and `λ² = m`,

`−r·δ = m(μ − 4π²u²)δ² + (θ − mμ)·(cS)·δ − (u²W″ + 2uW′)·δ`.

The first term is nonpositive OUTSIDE the core `|u| ≤ √μ/(2π)` — the sign
of the cylinder potential pays the whole bulk.  The remaining pieces are
paid by the eigenvalue-defect rate, the mode `L¹` mass, and the transport
`L¹` mass — all entering as explicit hypotheses.
-/

/-- **The defect energy rate ledger.**  The weighted defect energy is
bounded by `m·μ·Cd²·(√μ/π) + Ce·Cphi·Cd + D·Cd`, where `Cd` is the C0
bound on the defect, `Ce` the eigenvalue-defect bound
`|θ − mμ| ≤ Ce`, `Cphi` the mode `L¹` mass, and `D` the transport `L¹`
mass.  With `Cd, Ce = O(λ⁻²)` this is the preflight rate `C²/λ²`. -/
theorem sturm_defect_energy_rate_ledger
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (c : ℝ) (W Wd Wdd : ℝ → ℝ)
    (hW : ∀ y : ℝ, HasDerivAt W (Wd y) y)
    (hWd : ∀ y : ℝ, HasDerivAt Wd (Wdd y) y)
    (hWcont : Continuous W)
    (hWddcont : Continuous Wdd)
    (μ Cd Ce Cphi D : ℝ)
    (hmu : 0 < μ) (hCd : 0 ≤ Cd)
    (hcyl : ∀ u : ℝ, Wdd u = (4 * Real.pi ^ 2 * u ^ 2 - μ) * W u)
    (hC0 : ∀ u ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
      |c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u| ≤ Cd)
    (hEps : |Λ + mode4JacobiG mProject - (mProject : ℝ) * μ| ≤ Ce)
    (hPhi : (∫ u in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
      |c * mode4PhysicalFerrersSeries mProject S.coefficients u|) ≤ Cphi)
    (hWtr : (∫ u in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
      |u ^ 2 * Wdd u + 2 * u * Wd u|) ≤ D) :
    (∫ x in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        ((Real.sqrt mProject) ^ 2 - x ^ 2) *
          (c * mode4PhysicalFerrersFirstDerivativeSeries mProject
              S.coefficients x - Wd x) ^ 2) ≤
      (mProject : ℝ) * μ * Cd ^ 2 * (Real.sqrt μ / Real.pi) +
        Ce * Cphi * Cd + D * Cd := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hlam0 : (0 : ℝ) < Real.sqrt mProject := Real.sqrt_pos.2 hmR
  have hsq : (Real.sqrt (mProject : ℝ)) ^ 2 = (mProject : ℝ) :=
    Real.sq_sqrt hmR.le
  have hpi := Real.pi_pos
  have hCe : (0 : ℝ) ≤ Ce := le_trans (abs_nonneg _) hEps
  have hWdcont : Continuous Wd :=
    continuous_iff_continuousAt.mpr fun x => (hWd x).continuousAt
  -- the signed identity
  have hIdent := sturm_defect_energy_identity S hm hK hsep hΛ c W Wd Wdd
    hW hWd hWcont hWddcont
  rw [hIdent, ← MeasureTheory.integral_neg]
  -- the core radius
  set R : ℝ := Real.sqrt μ / (2 * Real.pi) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact div_pos (Real.sqrt_pos.2 hmu) (by positivity)
  have hR2 : 4 * Real.pi ^ 2 * R ^ 2 = μ := by
    rw [hRdef, div_pow, Real.sq_sqrt hmu.le, mul_pow]
    field_simp
    ring
  -- pointwise ledger majorization on the open window
  have hpoint : ∀ u ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
      -((c * ((2 * Real.pi * Real.sqrt mProject * u) ^ 2 *
            mode4PhysicalFerrersSeries mProject S.coefficients u -
          (Λ + mode4JacobiG mProject) *
            mode4PhysicalFerrersSeries mProject S.coefficients u) +
        2 * u * Wd u - ((Real.sqrt mProject) ^ 2 - u ^ 2) * Wdd u) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u)) ≤
      Set.indicator (Icc (-R) R)
          (fun _ => (mProject : ℝ) * μ * Cd ^ 2) u +
        (Ce * Cd) * |c * mode4PhysicalFerrersSeries mProject
          S.coefficients u| +
        Cd * |u ^ 2 * Wdd u + 2 * u * Wd u| := by
    intro u hu
    have hd := hC0 u hu
    have hd' := abs_le.1 hd
    have hkey :
        -((c * ((2 * Real.pi * Real.sqrt mProject * u) ^ 2 *
              mode4PhysicalFerrersSeries mProject S.coefficients u -
            (Λ + mode4JacobiG mProject) *
              mode4PhysicalFerrersSeries mProject S.coefficients u) +
          2 * u * Wd u - ((Real.sqrt mProject) ^ 2 - u ^ 2) * Wdd u) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u)) =
        (mProject : ℝ) * (μ - 4 * Real.pi ^ 2 * u ^ 2) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients u -
              W u) ^ 2 +
          (Λ + mode4JacobiG mProject - (mProject : ℝ) * μ) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients u) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients u -
              W u) -
          (u ^ 2 * Wdd u + 2 * u * Wd u) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients u -
              W u) := by
      simp only [hcyl, mul_pow]
      rw [hsq]
      ring
    rw [hkey]
    have hcore : (mProject : ℝ) * (μ - 4 * Real.pi ^ 2 * u ^ 2) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients u -
          W u) ^ 2 ≤
        Set.indicator (Icc (-R) R)
          (fun _ => (mProject : ℝ) * μ * Cd ^ 2) u := by
      by_cases hcase : u ∈ Icc (-R) R
      · rw [Set.indicator_of_mem hcase]
        have hu2 : u ^ 2 ≤ R ^ 2 := sq_le_sq' hcase.1 hcase.2
        have hpot0 : 0 ≤ μ - 4 * Real.pi ^ 2 * u ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hu2
            (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2)]
        have hpot1 : μ - 4 * Real.pi ^ 2 * u ^ 2 ≤ μ :=
          sub_le_self _ (by positivity)
        have hgsq : (c * mode4PhysicalFerrersSeries mProject
            S.coefficients u - W u) ^ 2 ≤ Cd ^ 2 :=
          sq_le_sq' (by linarith [hd'.1]) hd'.2
        have := mul_le_mul hpot1 hgsq (sq_nonneg _) hmu.le
        nlinarith [hmR.le]
      · rw [Set.indicator_of_notMem hcase]
        simp only [Set.mem_Icc, not_and_or, not_le] at hcase
        have hu2 : R ^ 2 < u ^ 2 := by
          rcases hcase with h | h
          · nlinarith
          · nlinarith
        have hpotneg : μ - 4 * Real.pi ^ 2 * u ^ 2 ≤ 0 := by
          nlinarith [mul_lt_mul_of_pos_left hu2
            (by positivity : (0:ℝ) < 4 * Real.pi ^ 2)]
        have h1 : (mProject : ℝ) * (μ - 4 * Real.pi ^ 2 * u ^ 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hmR.le hpotneg
        exact mul_nonpos_of_nonpos_of_nonneg h1 (sq_nonneg _)
    have heps_pt : (Λ + mode4JacobiG mProject - (mProject : ℝ) * μ) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients u) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u) ≤
        (Ce * Cd) * |c * mode4PhysicalFerrersSeries mProject
          S.coefficients u| := by
      calc (Λ + mode4JacobiG mProject - (mProject : ℝ) * μ) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients u) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u) ≤
          |(Λ + mode4JacobiG mProject - (mProject : ℝ) * μ) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients u) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients u -
              W u)| := le_abs_self _
        _ = |Λ + mode4JacobiG mProject - (mProject : ℝ) * μ| *
            |c * mode4PhysicalFerrersSeries mProject S.coefficients u| *
            |c * mode4PhysicalFerrersSeries mProject S.coefficients u -
              W u| := by rw [abs_mul, abs_mul]
        _ ≤ Ce * |c * mode4PhysicalFerrersSeries mProject
              S.coefficients u| * Cd := by
            apply mul_le_mul _ hd (abs_nonneg _)
            · exact mul_nonneg hCe (abs_nonneg _)
            · exact mul_le_mul_of_nonneg_right hEps (abs_nonneg _)
        _ = (Ce * Cd) * |c * mode4PhysicalFerrersSeries mProject
              S.coefficients u| := by ring
    have htr_pt : -((u ^ 2 * Wdd u + 2 * u * Wd u) *
        (c * mode4PhysicalFerrersSeries mProject S.coefficients u - W u)) ≤
        Cd * |u ^ 2 * Wdd u + 2 * u * Wd u| := by
      calc -((u ^ 2 * Wdd u + 2 * u * Wd u) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients u -
            W u)) ≤
          |(u ^ 2 * Wdd u + 2 * u * Wd u) *
            (c * mode4PhysicalFerrersSeries mProject S.coefficients u -
              W u)| := neg_le_abs _
        _ = |u ^ 2 * Wdd u + 2 * u * Wd u| *
            |c * mode4PhysicalFerrersSeries mProject S.coefficients u -
              W u| := abs_mul _ _
        _ ≤ |u ^ 2 * Wdd u + 2 * u * Wd u| * Cd :=
            mul_le_mul_of_nonneg_left hd (abs_nonneg _)
        _ = Cd * |u ^ 2 * Wdd u + 2 * u * Wd u| := mul_comm _ _
    linarith [hcore, heps_pt, htr_pt]
  -- integrability of the three majorant pieces
  have hphys_closed := sturm_physSeries_continuousOn_closed S hm
  have hsub : Ioo (-Real.sqrt mProject) (Real.sqrt mProject) ⊆
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := Ioo_subset_Icc_self
  have hint_ind : IntegrableOn
      (fun u : ℝ => Set.indicator (Icc (-R) R)
        (fun _ => (mProject : ℝ) * μ * Cd ^ 2) u)
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) volume := by
    have hconst : IntegrableOn
        (fun _ : ℝ => (mProject : ℝ) * μ * Cd ^ 2)
        (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) volume :=
      MeasureTheory.integrableOn_const
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    exact hconst.indicator measurableSet_Icc
  have hcS_closed : ContinuousOn
      (fun u : ℝ => c * mode4PhysicalFerrersSeries mProject
        S.coefficients u)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) :=
    (hphys_closed.const_smul c).congr (fun x _ => by simp [smul_eq_mul])
  have hint_S : IntegrableOn
      (fun u : ℝ => (Ce * Cd) * |c * mode4PhysicalFerrersSeries mProject
        S.coefficients u|)
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) volume :=
    (((hcS_closed.abs.integrableOn_compact isCompact_Icc).mono_set
      hsub)).const_mul _
  have htr_cont : Continuous
      (fun u : ℝ => u ^ 2 * Wdd u + 2 * u * Wd u) :=
    ((continuous_pow 2).mul hWddcont).add
      ((continuous_const.mul continuous_id').mul hWdcont)
  have hint_tr : IntegrableOn
      (fun u : ℝ => Cd * |u ^ 2 * Wdd u + 2 * u * Wd u|)
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) volume :=
    (((htr_cont.abs.continuousOn.integrableOn_compact
      isCompact_Icc).mono_set hsub)).const_mul _
  -- integrability of the negated source
  have hg_cont_closed : ContinuousOn
      (fun u : ℝ => c * mode4PhysicalFerrersSeries mProject
        S.coefficients u - W u)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) :=
    hcS_closed.sub hWcont.continuousOn
  have hr_cont_closed : ContinuousOn
      (fun u : ℝ => c * ((2 * Real.pi * Real.sqrt mProject * u) ^ 2 *
          mode4PhysicalFerrersSeries mProject S.coefficients u -
        (Λ + mode4JacobiG mProject) *
          mode4PhysicalFerrersSeries mProject S.coefficients u) +
        2 * u * Wd u - ((Real.sqrt mProject) ^ 2 - u ^ 2) * Wdd u)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) := by
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
  have hint_neg : IntegrableOn
      (fun u : ℝ =>
        -((c * ((2 * Real.pi * Real.sqrt mProject * u) ^ 2 *
              mode4PhysicalFerrersSeries mProject S.coefficients u -
            (Λ + mode4JacobiG mProject) *
              mode4PhysicalFerrersSeries mProject S.coefficients u) +
          2 * u * Wd u - ((Real.sqrt mProject) ^ 2 - u ^ 2) * Wdd u) *
          (c * mode4PhysicalFerrersSeries mProject S.coefficients u -
            W u)))
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) volume :=
    (((hr_cont_closed.mul hg_cont_closed).integrableOn_compact
      isCompact_Icc).mono_set hsub).neg
  -- monotone comparison with the majorant (lambda-level ascriptions keep
  -- the integrands out of Pi-form)
  have hint_12 : IntegrableOn
      (fun u : ℝ => Set.indicator (Icc (-R) R)
          (fun _ => (mProject : ℝ) * μ * Cd ^ 2) u +
        (Ce * Cd) * |c * mode4PhysicalFerrersSeries mProject
          S.coefficients u|)
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) volume :=
    hint_ind.add hint_S
  have hint_sum : IntegrableOn
      (fun u : ℝ => Set.indicator (Icc (-R) R)
          (fun _ => (mProject : ℝ) * μ * Cd ^ 2) u +
        (Ce * Cd) * |c * mode4PhysicalFerrersSeries mProject
          S.coefficients u| +
        Cd * |u ^ 2 * Wdd u + 2 * u * Wd u|)
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) volume :=
    hint_12.add hint_tr
  have hmono := MeasureTheory.setIntegral_mono_on hint_neg
    hint_sum measurableSet_Ioo hpoint
  -- split and bound the majorant integral
  rw [MeasureTheory.integral_add hint_12 hint_tr,
    MeasureTheory.integral_add hint_ind hint_S] at hmono
  have hI1 : (∫ u in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
      Set.indicator (Icc (-R) R)
        (fun _ => (mProject : ℝ) * μ * Cd ^ 2) u) ≤
      (mProject : ℝ) * μ * Cd ^ 2 * (Real.sqrt μ / Real.pi) := by
    rw [MeasureTheory.setIntegral_indicator measurableSet_Icc,
      MeasureTheory.setIntegral_const]
    have hvol : volume.real
        (Ioo (-Real.sqrt mProject) (Real.sqrt mProject) ∩ Icc (-R) R) ≤
        2 * R := by
      have h1 : volume.real
          (Ioo (-Real.sqrt mProject) (Real.sqrt mProject) ∩
            Icc (-R) R) ≤ volume.real (Icc (-R) R) :=
        measureReal_mono inter_subset_right
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      rw [Real.volume_real_Icc] at h1
      have h2 : max (R - -R) 0 = 2 * R := by
        rw [max_eq_left (by linarith)]
        ring
      rw [h2] at h1
      exact h1
    have hKnn : (0 : ℝ) ≤ (mProject : ℝ) * μ * Cd ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hvol hKnn
    rw [smul_eq_mul]
    have h4 : 2 * R * ((mProject : ℝ) * μ * Cd ^ 2) =
        (mProject : ℝ) * μ * Cd ^ 2 * (Real.sqrt μ / Real.pi) := by
      rw [hRdef]
      field_simp
    linarith [h3, h4.le, h4.ge]
  have hI2 : (∫ u in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
      (Ce * Cd) * |c * mode4PhysicalFerrersSeries mProject
        S.coefficients u|) ≤ Ce * Cphi * Cd := by
    rw [MeasureTheory.integral_const_mul]
    have h1 := mul_le_mul_of_nonneg_left hPhi
      (mul_nonneg hCe hCd)
    linarith [h1]
  have hI3 : (∫ u in Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
      Cd * |u ^ 2 * Wdd u + 2 * u * Wd u|) ≤ D * Cd := by
    rw [MeasureTheory.integral_const_mul]
    have h1 := mul_le_mul_of_nonneg_left hWtr hCd
    linarith [h1]
  linarith [hmono, hI1, hI2, hI3]

#print axioms sturm_physSeries_continuousOn_closed
#print axioms sturm_defect_truncated_energy_bound
#print axioms sturm_defect_flux_tendsto_zero_top
#print axioms sturm_defect_flux_tendsto_zero_bot
#print axioms sturm_defect_energy_integrable_and_bound
#print axioms sturm_defect_energy_identity
#print axioms sturm_defect_energy_rate_ledger

end Q3.RouteB.D0Pstar
