import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierNonzeroScalar
import Q3.Proofs.RouteB.ProlateSourceRegularity

/-!
# Goal 058 G3: normalized physical Ferrers zero extension

The accepted physical Ferrers source lives naturally on the closed window
`[-sqrt m, sqrt m]`, whereas the production `ProlatePair` stores a function on
the whole real line.  This file performs only that canonical zero extension
and its honest `L2` normalization.  It also transports the already-proved
restricted finite-Fourier eigenrelation through the normalization.

The exact supplier preflight at clean HEAD `cd5504a0` used the query

`physical Ferrers zero extension L2 normalization compact support production
ProlatePair constructor mode zero mode four restricted Fourier real nonzero
scalar`

and returned `no hits`.

No Sturm zero count, scalar sign/order, mode-zero/mode-four identification,
orthogonality, CCM Lemma 7.2, Goal 058 G3, Route B promotion, or RH claim is
proved here.
-/

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB

/-- The accepted physical Ferrers source, extended by zero outside its exact
physical window. -/
noncomputable def Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) (u : ℝ) : ℂ :=
  (Icc (-Real.sqrt mProject) (Real.sqrt mProject)).indicator
    (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) u

/-- Squared `L2` mass of the unnormalized physical Ferrers source on its
closed window. -/
noncomputable def Mode4FerrersRegularEvenProlateSolution.physicalL2Mass
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) : ℝ :=
  ∫ u in (-Real.sqrt mProject)..Real.sqrt mProject,
    (mode4PhysicalFerrersSeries mProject S.coefficients u) ^ 2

/-- Positive real normalization used for the production whole-line mode. -/
noncomputable def Mode4FerrersRegularEvenProlateSolution.physicalL2Normalization
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) : ℝ :=
  Real.sqrt S.physicalL2Mass

/-- Unit-`L2` physical Ferrers mode on the whole real line. -/
noncomputable def Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) (u : ℝ) : ℂ :=
  S.physicalZeroExtension u / (S.physicalL2Normalization : ℂ)

theorem Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension_even
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    Function.Even S.physicalZeroExtension := by
  intro u
  have hseries :
      mode4PhysicalFerrersSeriesComplex mProject S.coefficients (-u) =
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients u := by
    have h := S.even (u / Real.sqrt mProject)
    have hc := congrArg (fun r : ℝ ↦ (r : ℂ)) h
    simpa only [mode4PhysicalFerrersSeriesComplex,
      mode4PhysicalFerrersSeries, neg_div] using hc
  by_cases hu : u ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject)
  · have hneg : -u ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject) :=
      ⟨by linarith [hu.2], by linarith [hu.1]⟩
    simp only [Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      indicator_of_mem hu, indicator_of_mem hneg]
    exact hseries
  · have hneg : -u ∉ Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
      intro h
      exact hu ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      indicator_of_notMem hu, indicator_of_notMem hneg]

theorem Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension_support
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    Function.support S.physicalZeroExtension ⊆
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
  intro u hu
  by_contra hmem
  exact hu (by
    rw [Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      indicator_of_notMem hmem])

theorem Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension_integrable
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    Integrable S.physicalZeroExtension := by
  exact (S.physicalComplex_continuousOn_closed hm).integrableOn_Icc
    |>.integrable_indicator measurableSet_Icc

theorem Mode4FerrersRegularEvenProlateSolution.physicalL2Mass_pos
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    0 < S.physicalL2Mass := by
  have hs : 0 < Real.sqrt (mProject : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hcont : ContinuousOn
      (fun u : ℝ ↦
        (mode4PhysicalFerrersSeries mProject S.coefficients u) ^ 2)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) := by
    have hreal : ContinuousOn
        (mode4PhysicalFerrersSeries mProject S.coefficients)
        (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) := by
      have hc := S.physicalComplex_continuousOn_closed hm
      have hr := Complex.continuous_re.comp_continuousOn hc
      simpa only [mode4PhysicalFerrersSeriesComplex,
        Complex.ofReal_re] using hr
    exact hreal.pow 2
  have hcenter :
      mode4PhysicalFerrersSeries mProject S.coefficients 0 ≠ 0 := by
    simpa only [mode4PhysicalFerrersSeries, zero_div] using
      S.center_value_ne_zero
  unfold Mode4FerrersRegularEvenProlateSolution.physicalL2Mass
  apply intervalIntegral.integral_pos
  · linarith
  · exact hcont
  · intro u _
    positivity
  · refine ⟨0, ?_, sq_pos_of_ne_zero hcenter⟩
    constructor <;> linarith

theorem Mode4FerrersRegularEvenProlateSolution.physicalL2Normalization_pos
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    0 < S.physicalL2Normalization := by
  exact Real.sqrt_pos.2 (S.physicalL2Mass_pos hm)

theorem Mode4FerrersRegularEvenProlateSolution.integral_sqNorm_physicalZeroExtension
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    (∫ u : ℝ, ‖S.physicalZeroExtension u‖ ^ 2) = S.physicalL2Mass := by
  have hfun : (fun u : ℝ ↦ ‖S.physicalZeroExtension u‖ ^ 2) =
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)).indicator
        (fun u : ℝ ↦
          (mode4PhysicalFerrersSeries mProject S.coefficients u) ^ 2) := by
    funext u
    by_cases hu : u ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject)
    · rw [indicator_of_mem hu, Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_mem hu]
      simp [mode4PhysicalFerrersSeriesComplex, Real.norm_eq_abs, sq_abs]
    · rw [indicator_of_notMem hu,
        Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_notMem hu]
      norm_num
  rw [hfun, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le]
  · rfl
  · have hs := Real.sqrt_nonneg (mProject : ℝ)
    linarith

theorem Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension_sqNorm_integrable
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    Integrable (fun u : ℝ ↦ ‖S.physicalZeroExtension u‖ ^ 2) := by
  have hfun : (fun u : ℝ ↦ ‖S.physicalZeroExtension u‖ ^ 2) =
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)).indicator
        (fun u : ℝ ↦
          (mode4PhysicalFerrersSeries mProject S.coefficients u) ^ 2) := by
    funext u
    by_cases hu : u ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject)
    · rw [indicator_of_mem hu, Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_mem hu]
      simp [mode4PhysicalFerrersSeriesComplex, Real.norm_eq_abs, sq_abs]
    · rw [indicator_of_notMem hu,
        Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_notMem hu]
      norm_num
  rw [hfun]
  have hreal : ContinuousOn
      (mode4PhysicalFerrersSeries mProject S.coefficients)
      (Icc (-Real.sqrt mProject) (Real.sqrt mProject)) := by
    have hc := S.physicalComplex_continuousOn_closed hm
    have hr := Complex.continuous_re.comp_continuousOn hc
    simpa only [mode4PhysicalFerrersSeriesComplex,
      Complex.ofReal_re] using hr
  exact (hreal.pow 2).integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode_even
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    Function.Even S.normalizedPhysicalMode := by
  intro u
  simp only [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    S.physicalZeroExtension_even u]

theorem Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode_support
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    Function.support S.normalizedPhysicalMode ⊆
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
  intro u hu
  by_contra hmem
  have hz := S.physicalZeroExtension_support
  have hzero : S.physicalZeroExtension u = 0 := by
    by_contra hne
    exact hmem (hz hne)
  exact hu (by simp [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    hzero])

theorem Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode_integrable
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    Integrable S.normalizedPhysicalMode := by
  simpa only [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    div_eq_mul_inv] using
      (S.physicalZeroExtension_integrable hm).mul_const
        ((S.physicalL2Normalization : ℂ)⁻¹)

theorem Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode_sqNorm_integrable
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    Integrable (fun u : ℝ ↦ ‖S.normalizedPhysicalMode u‖ ^ 2) := by
  have hnorm : 0 < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  have hfun : (fun u : ℝ ↦ ‖S.normalizedPhysicalMode u‖ ^ 2) =
      fun u : ℝ ↦ (S.physicalL2Normalization⁻¹) ^ 2 *
        ‖S.physicalZeroExtension u‖ ^ 2 := by
    funext u
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnorm]
    ring
  rw [hfun]
  exact (S.physicalZeroExtension_sqNorm_integrable hm).const_mul _

theorem Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode_normalized
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    (∫ u : ℝ, ‖S.normalizedPhysicalMode u‖ ^ 2) = 1 := by
  have hmass : 0 < S.physicalL2Mass := S.physicalL2Mass_pos hm
  have hnorm : 0 < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  have hsq : S.physicalL2Normalization ^ 2 = S.physicalL2Mass := by
    exact Real.sq_sqrt hmass.le
  have hfun : (fun u : ℝ ↦ ‖S.normalizedPhysicalMode u‖ ^ 2) =
      fun u : ℝ ↦ (S.physicalL2Normalization⁻¹) ^ 2 *
        ‖S.physicalZeroExtension u‖ ^ 2 := by
    funext u
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnorm]
    ring
  rw [hfun, integral_const_mul,
    S.integral_sqNorm_physicalZeroExtension, ← hsq]
  field_simp [hnorm.ne']

/-- Exact positive whole-line integral of the normalized mode. -/
theorem Mode4FerrersRegularEvenProlateSolution.integral_normalizedPhysicalMode_pos
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ∃ I : ℝ, 0 < I ∧
      (I : ℂ) = ∫ u : ℝ, S.normalizedPhysicalMode u := by
  let s : ℝ := Real.sqrt mProject
  let n : ℝ := S.physicalL2Normalization
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hn : 0 < n := S.physicalL2Normalization_pos hm
  have hscale := intervalIntegral.integral_comp_div
    (f := mode4FerrersSeries S.coefficients)
    (a := -s) (b := s) (c := s) hs.ne'
  have hsource := mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero
    S.coefficients S.coefficients_abs_summable
  have hphysical :
      (∫ u in (-s)..s,
        mode4PhysicalFerrersSeries mProject S.coefficients u) =
        s * (2 * S.coefficients 0) := by
    rw [show (-s) / s = (-1 : ℝ) by field_simp [hs.ne'],
      show s / s = (1 : ℝ) by field_simp [hs.ne'], hsource] at hscale
    simpa only [mode4PhysicalFerrersSeries, s, smul_eq_mul] using hscale
  let I : ℝ := s * (2 * S.coefficients 0) / n
  have hI : 0 < I := by
    dsimp only [I]
    exact div_pos (mul_pos hs (mul_pos (by norm_num) S.coefficient_zero_pos)) hn
  refine ⟨I, hI, ?_⟩
  have hraw :
      (∫ u : ℝ, S.physicalZeroExtension u) =
        ((s * (2 * S.coefficients 0) : ℝ) : ℂ) := by
    unfold Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension
    change
      (∫ u : ℝ,
        (Icc (-s) s).indicator
          (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) u) = _
    rw [
      integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -s ≤ s)]
    change
      (∫ u in (-s)..s,
        (mode4PhysicalFerrersSeries mProject S.coefficients u : ℂ)) = _
    rw [intervalIntegral.integral_ofReal, hphysical]
  unfold Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode
  change (I : ℂ) =
    ∫ u : ℝ, S.physicalZeroExtension u *
      (S.physicalL2Normalization : ℂ)⁻¹
  rw [integral_mul_const, hraw]
  dsimp only [I, n]
  push_cast
  field_simp [hn.ne']

/-- The real nonzero Fourier scalar and its exact restricted eigenrelation
survive the canonical zero extension and `L2` normalization. -/
theorem Mode4FerrersRegularEvenProlateSolution.exists_normalizedPhysicalMode_finiteFourier_eq_real_nonzero_scalar_mul
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ∃ chi : ℝ, chi ≠ 0 ∧
      ∀ x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject),
        D0Pstar.finiteFourierAction (Real.sqrt mProject)
            S.normalizedPhysicalMode x =
          (chi : ℂ) * S.normalizedPhysicalMode x := by
  obtain ⟨chi, hchi, hrelation⟩ :=
    S.exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul hm
  have hn : 0 < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  refine ⟨chi, hchi, ?_⟩
  intro x hx
  have hsourceOn : ∀ y ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject),
      S.normalizedPhysicalMode y =
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients y /
          (S.physicalL2Normalization : ℂ) := by
    intro y hy
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      indicator_of_mem hy]
  calc
    D0Pstar.finiteFourierAction (Real.sqrt mProject)
        S.normalizedPhysicalMode x =
      (S.physicalL2Normalization : ℂ)⁻¹ *
        D0Pstar.finiteFourierAction (Real.sqrt mProject)
          (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) x := by
      unfold D0Pstar.finiteFourierAction
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      rw [hsourceOn y hy]
      ring
    _ = (chi : ℂ) * S.normalizedPhysicalMode x := by
      rw [hrelation x hx, hsourceOn x hx]
      field_simp [hn.ne']

#print axioms Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension
#print axioms Mode4FerrersRegularEvenProlateSolution.physicalL2Mass_pos
#print axioms Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode_normalized
#print axioms Mode4FerrersRegularEvenProlateSolution.integral_normalizedPhysicalMode_pos
#print axioms
  Mode4FerrersRegularEvenProlateSolution.exists_normalizedPhysicalMode_finiteFourier_eq_real_nonzero_scalar_mul

end Q3.RouteB
