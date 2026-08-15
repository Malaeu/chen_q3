import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierScalarProportionality

/-!
# Goal 058 G3: the physical Ferrers Fourier scalar is real

The preceding source-locked proportionality theorem returns a complex scalar.
At the center, however, the positive-phase Fourier kernel is exactly one and
the physical Ferrers source is real-valued.  Since the accepted source has a
nonzero center value, the imaginary part of that scalar must vanish.

The exact fresh knowledge query

`physical Ferrers finite Fourier scalar real center ratio integral of
real-valued source mode4`

returned `no hits` before this file was written.

This file does not prove that the scalar is nonzero, positive, or ordered
against another mode.  It does not instantiate `ProlatePair`, prove the CCM
floor, or close Goal 058 G3.
-/

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB

/-- The finite-Fourier proportionality scalar of every accepted physical
Ferrers solution can be chosen real on the exact closed physical window. -/
theorem Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_scalar_mul
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ∃ chi : ℝ, ∀ x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject),
      D0Pstar.finiteFourierAction (Real.sqrt mProject)
          (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) x =
        (chi : ℂ) *
          mode4PhysicalFerrersSeriesComplex mProject S.coefficients x := by
  obtain ⟨chi, hchi⟩ :=
    S.exists_physicalFiniteFourierAction_eq_scalar_mul hm
  have hzeroMem : (0 : ℝ) ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
    have hsqrt : 0 ≤ Real.sqrt (mProject : ℝ) := Real.sqrt_nonneg _
    constructor <;> linarith
  have hcenter := hchi 0 hzeroMem
  have hsourceZero :
      mode4PhysicalFerrersSeries mProject S.coefficients 0 ≠ 0 := by
    simpa only [mode4PhysicalFerrersSeries, zero_div] using
      S.center_value_ne_zero
  have him : chi.im = 0 := by
    have himEq := congrArg Complex.im hcenter
    simp only [D0Pstar.finiteFourierAction, D0Pstar.finiteFourierKernel,
      mode4PhysicalFerrersSeriesComplex, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_mul, integral_complex_ofReal,
      Complex.mul_im, Complex.ofReal_im, mul_zero, Complex.ofReal_re,
      zero_add] at himEq
    exact (mul_eq_zero.mp himEq.symm).resolve_right hsourceZero
  have hchiReal : (chi.re : ℂ) = chi := by
    apply Complex.ext
    · simp
    · simp [him]
  refine ⟨chi.re, ?_⟩
  intro x hx
  rw [hchiReal]
  exact hchi x hx

#print axioms
  Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_scalar_mul

end Q3.RouteB
