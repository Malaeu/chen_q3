import Q3.Proofs.RouteB.D0Mode4FerrersNormalizedZeroCountTransport

/-!
# Normalized Ferrers actual-mode local fields

This source-free Goal 058 G3 leaf transports the accepted physical Ferrers
regularity and differential equation through the canonical zero extension and
positive normalization.  It supplies the real-valuedness, interior `C²`, and
literal `prolateWaveExpression` fields needed by `IsActualProlateModePair`.

No nodal count, Fourier-scalar positivity/order, actual-mode assembly, G3
closure, Route B promotion, or RH claim is made here.
-/

open Complex MeasureTheory Set
open scoped ContDiff ENat

noncomputable section

namespace Q3.RouteB

theorem normalizedPhysicalMode_im_eq_zero
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (x : ℝ) :
    (S.normalizedPhysicalMode x).im = 0 := by
  rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension]
  by_cases hx : x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject)
  · rw [indicator_of_mem hx, mode4PhysicalFerrersSeriesComplex]
    simp
  · rw [indicator_of_notMem hx]
    simp

theorem normalizedPhysicalMode_contDiffOn_two_open
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ContDiffOn ℝ 2 S.normalizedPhysicalMode
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) := by
  have hcast : ContDiffOn ℝ 2
      (fun x : ℝ =>
        (mode4PhysicalFerrersSeries mProject S.coefficients x : ℂ))
      (Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (S.physical_contDiffOn_two_open hm)
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using h
  apply (hcast.div_const (S.physicalL2Normalization : ℂ)).congr
  intro x hx
  have hxClosed : x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject) :=
    ⟨hx.1.le, hx.2.le⟩
  rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
    indicator_of_mem hxClosed, mode4PhysicalFerrersSeriesComplex]

theorem physicalComplex_prolateWaveExpression_eigenrelation
    {mProject K : ℕ} {Λ x : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hx : x ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    D0Pstar.prolateWaveExpression (Real.sqrt mProject)
        (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) x =
      ((Λ + mode4JacobiG mProject : ℝ) : ℂ) *
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients x := by
  let f : ℝ → ℂ := mode4PhysicalFerrersSeriesComplex mProject S.coefficients
  let df : ℝ → ℂ :=
    mode4PhysicalFerrersFirstDerivativeSeriesComplex mProject S.coefficients
  let lambda : ℝ := Real.sqrt mProject
  let theta : ℝ := Λ + mode4JacobiG mProject
  have hderiv : ∀ y ∈ Ioo (-lambda) lambda,
      fderiv ℝ f y 1 = df y := by
    intro y hy
    have h := S.physicalComplex_hasDerivAt hm (by simpa [lambda] using hy)
    simpa only [fderiv_deriv, f, df] using h.deriv
  have hfun :
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1)) =ᶠ[nhds x]
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (by simpa [lambda] using hx)] with y hy
    rw [hderiv y hy]
  have hflux := S.physicalComplex_flux_hasDerivAt hm hx
  have houter :
      fderiv ℝ
          (fun y : ℝ =>
            (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1)) x 1 =
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) -
            (theta : ℂ)) * f x) := by
    rw [hfun.fderiv_eq]
    simpa only [fderiv_deriv, f, df, lambda, theta] using hflux.deriv
  rw [D0Pstar.prolateWaveExpression]
  change -fderiv ℝ
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1)) x 1 +
      ((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) * f x) =
    (theta : ℂ) * f x
  rw [houter]
  ring

theorem normalizedPhysicalMode_hasDerivAt
    {mProject K : ℕ} {Λ x : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hx : x ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    HasDerivAt S.normalizedPhysicalMode
      (mode4PhysicalFerrersFirstDerivativeSeriesComplex
        mProject S.coefficients x /
          (S.physicalL2Normalization : ℂ)) x := by
  have heq : S.normalizedPhysicalMode =ᶠ[nhds x]
      (fun y : ℝ =>
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients y /
          (S.physicalL2Normalization : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have hyClosed : y ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject) :=
      ⟨hy.1.le, hy.2.le⟩
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      indicator_of_mem hyClosed]
  exact (S.physicalComplex_hasDerivAt hm hx).div_const
    (S.physicalL2Normalization : ℂ) |>.congr_of_eventuallyEq heq

theorem normalizedPhysicalMode_prolateWaveExpression_eigenrelation
    {mProject K : ℕ} {Λ x : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hx : x ∈ Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    D0Pstar.prolateWaveExpression (Real.sqrt mProject)
        S.normalizedPhysicalMode x =
      ((Λ + mode4JacobiG mProject : ℝ) : ℂ) *
        S.normalizedPhysicalMode x := by
  let f : ℝ → ℂ := S.normalizedPhysicalMode
  let df : ℝ → ℂ := fun y =>
    mode4PhysicalFerrersFirstDerivativeSeriesComplex
      mProject S.coefficients y / (S.physicalL2Normalization : ℂ)
  let lambda : ℝ := Real.sqrt mProject
  let theta : ℝ := Λ + mode4JacobiG mProject
  have hderiv : ∀ y ∈ Ioo (-lambda) lambda,
      fderiv ℝ f y 1 = df y := by
    intro y hy
    have h := normalizedPhysicalMode_hasDerivAt S hm
      (by simpa only [lambda] using hy)
    simpa only [fderiv_deriv, f, df] using h.deriv
  have hfun :
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1)) =ᶠ[nhds x]
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (by simpa only [lambda] using hx)]
      with y hy
    rw [hderiv y hy]
  have hfluxRaw := S.physicalComplex_flux_hasDerivAt hm hx
  have hflux : HasDerivAt
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y))
      (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) -
          (theta : ℂ)) * f x) x := by
    have hxClosed : x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject) :=
      ⟨hx.1.le, hx.2.le⟩
    have hfx : f x =
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients x /
          (S.physicalL2Normalization : ℂ) := by
      dsimp only [f]
      rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
        Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        indicator_of_mem hxClosed]
    simpa only [lambda, theta, df, hfx, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using
        hfluxRaw.div_const (S.physicalL2Normalization : ℂ)
  have houter :
      fderiv ℝ
          (fun y : ℝ =>
            (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1)) x 1 =
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) -
            (theta : ℂ)) * f x) := by
    rw [hfun.fderiv_eq]
    simpa only [fderiv_deriv] using hflux.deriv
  rw [D0Pstar.prolateWaveExpression]
  change -fderiv ℝ
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1)) x 1 +
      ((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) * f x) =
    (theta : ℂ) * f x
  rw [houter]
  ring

#print axioms normalizedPhysicalMode_im_eq_zero
#print axioms normalizedPhysicalMode_contDiffOn_two_open
#print axioms physicalComplex_prolateWaveExpression_eigenrelation
#print axioms normalizedPhysicalMode_hasDerivAt
#print axioms normalizedPhysicalMode_prolateWaveExpression_eigenrelation

end Q3.RouteB
