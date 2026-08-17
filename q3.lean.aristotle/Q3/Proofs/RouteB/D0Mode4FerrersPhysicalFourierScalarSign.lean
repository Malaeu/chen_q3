import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierNonzeroScalar

/-!
# Goal 058 G3: sign lock for the physical Ferrers Fourier scalar

The accepted physical Ferrers source already has a nonzero real restricted
finite-Fourier scalar.  This file evaluates that eigenrelation at frequency
zero and computes the Fourier-side value from the exact interval mean of the
Ferrers series.  The result is stronger than nonvanishing but deliberately
weaker than positive phase: the Fourier scalar and the center value have the
same sign.

No center-value positivity, scalar ordering between two modes, Sturm zero
count, `ProlatePair` construction, G1/G3 closure, Route promotion, or RH claim
is made here.
-/

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB

private theorem Mode4FerrersRegularEvenProlateSolution.physicalFiniteFourierAction_zero_eq
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    D0Pstar.finiteFourierAction (Real.sqrt mProject)
        (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) 0 =
      (((Real.sqrt mProject) * (2 * S.coefficients 0) : ℝ) : ℂ) := by
  let s : ℝ := Real.sqrt mProject
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hscale := intervalIntegral.integral_comp_div
    (f := mode4FerrersSeries S.coefficients)
    (a := -s) (b := s) (c := s) hs.ne'
  have hsource :=
    mode4FerrersSeries_intervalIntegral_eq_two_mul_coefficient_zero
      S.coefficients S.coefficients_abs_summable
  have hphysical :
      (∫ u in (-s)..s,
        mode4PhysicalFerrersSeries mProject S.coefficients u) =
        s * (2 * S.coefficients 0) := by
    rw [show (-s) / s = (-1 : ℝ) by field_simp [hs.ne'],
      show s / s = (1 : ℝ) by field_simp [hs.ne'], hsource] at hscale
    change
      (∫ u in (-s)..s,
        mode4FerrersSeries S.coefficients (u / s)) =
        s * (2 * S.coefficients 0)
    exact hscale
  unfold D0Pstar.finiteFourierAction D0Pstar.finiteFourierKernel
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -s ≤ s)]
  change
    (∫ u in (-s)..s,
      (mode4PhysicalFerrersSeries mProject S.coefficients u : ℂ)) = _
  rw [intervalIntegral.integral_ofReal, hphysical]
  rfl

/-- Every accepted physical Ferrers solution admits its already-proved real
nonzero finite-Fourier scalar with the additional exact sign information that
its product with the center value is strictly positive.  Equivalently, the
scalar and the center value have the same sign. -/
theorem Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul_and_mul_center_pos
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ∃ chi : ℝ, chi ≠ 0 ∧
      (∀ x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject),
        D0Pstar.finiteFourierAction (Real.sqrt mProject)
            (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) x =
          (chi : ℂ) *
            mode4PhysicalFerrersSeriesComplex mProject S.coefficients x) ∧
      0 < chi * mode4FerrersSeries S.coefficients 0 := by
  obtain ⟨chi, hchi, hrelation⟩ :=
    S.exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul hm
  have hzeroMem : (0 : ℝ) ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
    have hsqrt : 0 ≤ Real.sqrt (mProject : ℝ) := Real.sqrt_nonneg _
    constructor <;> linarith
  have hcenter := hrelation 0 hzeroMem
  rw [S.physicalFiniteFourierAction_zero_eq hm] at hcenter
  have hprod :
      chi * mode4FerrersSeries S.coefficients 0 =
        Real.sqrt mProject * (2 * S.coefficients 0) := by
    have hcenter' := congrArg Complex.re hcenter
    simpa only [mode4PhysicalFerrersSeriesComplex,
      mode4PhysicalFerrersSeries, zero_div, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      hcenter'.symm
  have hs : 0 < Real.sqrt (mProject : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hprodPos :
      0 < Real.sqrt mProject * (2 * S.coefficients 0) := by
    exact mul_pos hs (mul_pos (by norm_num) S.coefficient_zero_pos)
  refine ⟨chi, hchi, hrelation, ?_⟩
  rw [hprod]
  exact hprodPos

/-- The remaining positive-phase question is exactly a center-sign question
for the same source witness. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalFiniteFourier_scalar_pos_iff_center_pos
    {mProject K : ℕ} {Λ chi : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hrelation :
      ∀ x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject),
        D0Pstar.finiteFourierAction (Real.sqrt mProject)
            (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) x =
          (chi : ℂ) *
            mode4PhysicalFerrersSeriesComplex mProject S.coefficients x) :
    0 < chi ↔ 0 < mode4FerrersSeries S.coefficients 0 := by
  have hzeroMem : (0 : ℝ) ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
    have hsqrt : 0 ≤ Real.sqrt (mProject : ℝ) := Real.sqrt_nonneg _
    constructor <;> linarith
  have hcenter := hrelation 0 hzeroMem
  rw [S.physicalFiniteFourierAction_zero_eq hm] at hcenter
  have hprod :
      chi * mode4FerrersSeries S.coefficients 0 =
        Real.sqrt mProject * (2 * S.coefficients 0) := by
    have hcenter' := congrArg Complex.re hcenter
    simpa only [mode4PhysicalFerrersSeriesComplex,
      mode4PhysicalFerrersSeries, zero_div, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      hcenter'.symm
  have hpos :
      0 < Real.sqrt mProject * (2 * S.coefficients 0) := by
    exact mul_pos (Real.sqrt_pos.2 (by positivity))
      (mul_pos (by norm_num) S.coefficient_zero_pos)
  constructor
  · intro hchi
    nlinarith [hprod, hpos]
  · intro hcenterPos
    nlinarith [hprod, hpos]

#print axioms
  Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul_and_mul_center_pos
#print axioms
  Mode4FerrersRegularEvenProlateSolution.physicalFiniteFourier_scalar_pos_iff_center_pos

end Q3.RouteB
