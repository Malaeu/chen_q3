import Q3.Proofs.RouteB.D0ModeZeroFourFerrersProductionProlatePair

/-!
# Goal 058 G3: selected Ferrers production orthogonality

The selected physical Ferrers witnesses have distinct prolate differential
eigenvalues and satisfy the natural zero-flux endpoint domain.  A direct
Lagrange identity therefore makes their closed-window product integral zero.
This file proves that identity on the singular endpoint interface and
transports it through the canonical whole-line zero extension and `L2`
normalization.

The exact knowledge query at clean HEAD `6fb660f6`,

`prolate endpoint zero flux distinct eigenvalues orthogonality closed interval
production Ferrers modes`,

returned `no hits`.

This closes orthogonality only.  It does not prove the Sturm zero counts or
the positive-phase Fourier scalar sign/order, CCM Lemma 7.2, Goal 058 G3,
Route B promotion, or RH.
-/

open Complex Filter MeasureTheory Set
open scoped ComplexConjugate ContDiff ENat

noncomputable section

namespace Q3.RouteB

/-- Bilinear orthogonality for two endpoint-domain prolate eigenfunctions with
distinct real eigenvalues.  Complex conjugation is intentionally absent: the
selected Ferrers sources are real-valued, and the production sesquilinear
statement is obtained below by exact real complexification. -/
theorem integral_mul_eq_zero_of_prolate_endpointFlux_eigenrelations
    (lambda theta0 theta4 : ℝ)
    (hlambda : 0 < lambda)
    (htheta : theta0 ≠ theta4)
    (phi0 dphi0 phi4 dphi4 : ℝ → ℂ)
    (hphi0 : ContinuousOn phi0 (Icc (-lambda) lambda))
    (hphi4 : ContinuousOn phi4 (Icc (-lambda) lambda))
    (hphi0' : ∀ y ∈ Ioo (-lambda) lambda,
      HasDerivAt phi0 (dphi0 y) y)
    (hphi4' : ∀ y ∈ Ioo (-lambda) lambda,
      HasDerivAt phi4 (dphi4 y) y)
    (hflux0' : ∀ y ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun z : ℝ ↦ (((lambda ^ 2 - z ^ 2 : ℝ) : ℂ) * dphi0 z))
        (((((2 * Real.pi * lambda * y) ^ 2 : ℝ) : ℂ) - (theta0 : ℂ)) *
          phi0 y) y)
    (hflux4' : ∀ y ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun z : ℝ ↦ (((lambda ^ 2 - z ^ 2 : ℝ) : ℂ) * dphi4 z))
        (((((2 * Real.pi * lambda * y) ^ 2 : ℝ) : ℂ) - (theta4 : ℂ)) *
          phi4 y) y)
    (hflux0Plus :
      Tendsto
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dphi0 y))
        (nhdsWithin lambda (Iio lambda)) (nhds 0))
    (hflux0Minus :
      Tendsto
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dphi0 y))
        (nhdsWithin (-lambda) (Ioi (-lambda))) (nhds 0))
    (hflux4Plus :
      Tendsto
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dphi4 y))
        (nhdsWithin lambda (Iio lambda)) (nhds 0))
    (hflux4Minus :
      Tendsto
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dphi4 y))
        (nhdsWithin (-lambda) (Ioi (-lambda))) (nhds 0)) :
    (∫ y in Icc (-lambda) lambda, phi0 y * phi4 y) = 0 := by
  have hspan : -lambda < lambda := by linarith
  have hle : -lambda ≤ lambda := hspan.le
  let p : ℝ → ℂ := fun y ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ))
  let q : ℝ → ℂ :=
    fun y ↦ ((((2 * Real.pi * lambda * y) ^ 2 : ℝ) : ℂ))
  let u0 : ℝ → ℂ := fun y ↦ p y * dphi0 y
  let u4 : ℝ → ℂ := fun y ↦ p y * dphi4 y
  let r0 : ℝ → ℂ := fun y ↦ (q y - (theta0 : ℂ)) * phi0 y
  let r4 : ℝ → ℂ := fun y ↦ (q y - (theta4 : ℂ)) * phi4 y
  have hq : ContDiff ℝ ∞ q := by
    dsimp only [q]
    exact ofRealCLM.contDiff.comp
      ((contDiff_const.mul contDiff_id).pow 2)
  have hu0PlusValue : u0 lambda = 0 := by simp [u0, p]
  have hu0MinusValue : u0 (-lambda) = 0 := by simp [u0, p]
  have hu4PlusValue : u4 lambda = 0 := by simp [u4, p]
  have hu4MinusValue : u4 (-lambda) = 0 := by simp [u4, p]
  have hu0Plus : ContinuousWithinAt u0 (Icc (-lambda) lambda) lambda := by
    rw [continuousWithinAt_Icc_iff_Iic hspan,
      ← continuousWithinAt_Iio_iff_Iic]
    change Tendsto u0 (nhdsWithin lambda (Iio lambda)) (nhds (u0 lambda))
    rw [hu0PlusValue]
    exact hflux0Plus
  have hu0Minus : ContinuousWithinAt u0 (Icc (-lambda) lambda) (-lambda) := by
    rw [continuousWithinAt_Icc_iff_Ici hspan,
      ← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto u0 (nhdsWithin (-lambda) (Ioi (-lambda)))
      (nhds (u0 (-lambda)))
    rw [hu0MinusValue]
    exact hflux0Minus
  have hu4Plus : ContinuousWithinAt u4 (Icc (-lambda) lambda) lambda := by
    rw [continuousWithinAt_Icc_iff_Iic hspan,
      ← continuousWithinAt_Iio_iff_Iic]
    change Tendsto u4 (nhdsWithin lambda (Iio lambda)) (nhds (u4 lambda))
    rw [hu4PlusValue]
    exact hflux4Plus
  have hu4Minus : ContinuousWithinAt u4 (Icc (-lambda) lambda) (-lambda) := by
    rw [continuousWithinAt_Icc_iff_Ici hspan,
      ← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto u4 (nhdsWithin (-lambda) (Ioi (-lambda)))
      (nhds (u4 (-lambda)))
    rw [hu4MinusValue]
    exact hflux4Minus
  have hu0 : ContinuousOn u0 (Icc (-lambda) lambda) := by
    intro y hy
    by_cases hyMinus : y = -lambda
    · simpa [hyMinus] using hu0Minus
    by_cases hyPlus : y = lambda
    · simpa [hyPlus] using hu0Plus
    have hyOpen : y ∈ Ioo (-lambda) lambda :=
      ⟨lt_of_le_of_ne hy.1 (Ne.symm hyMinus),
        lt_of_le_of_ne hy.2 hyPlus⟩
    exact (hflux0' y hyOpen).continuousAt.continuousWithinAt
  have hu4 : ContinuousOn u4 (Icc (-lambda) lambda) := by
    intro y hy
    by_cases hyMinus : y = -lambda
    · simpa [hyMinus] using hu4Minus
    by_cases hyPlus : y = lambda
    · simpa [hyPlus] using hu4Plus
    have hyOpen : y ∈ Ioo (-lambda) lambda :=
      ⟨lt_of_le_of_ne hy.1 (Ne.symm hyMinus),
        lt_of_le_of_ne hy.2 hyPlus⟩
    exact (hflux4' y hyOpen).continuousAt.continuousWithinAt
  have hr0 : ContinuousOn r0 (Icc (-lambda) lambda) := by
    dsimp only [r0]
    exact (hq.continuous.continuousOn.sub continuousOn_const).mul hphi0
  have hr4 : ContinuousOn r4 (Icc (-lambda) lambda) := by
    dsimp only [r4]
    exact (hq.continuous.continuousOn.sub continuousOn_const).mul hphi4
  have hu0' : ∀ y ∈ Ioo (-lambda) lambda, HasDerivAt u0 (r0 y) y := by
    intro y hy
    simpa only [u0, p, r0, q] using hflux0' y hy
  have hu4' : ∀ y ∈ Ioo (-lambda) lambda, HasDerivAt u4 (r4 y) y := by
    intro y hy
    simpa only [u4, p, r4, q] using hflux4' y hy
  let W : ℝ → ℂ := fun y ↦ phi0 y * u4 y - phi4 y * u0 y
  let W' : ℝ → ℂ := fun y ↦
    ((theta0 - theta4 : ℝ) : ℂ) * (phi0 y * phi4 y)
  have hW : ContinuousOn W (Icc (-lambda) lambda) := by
    dsimp only [W]
    exact (hphi0.mul hu4).sub (hphi4.mul hu0)
  have hW' : ∀ y ∈ Ioo (-lambda) lambda, HasDerivAt W (W' y) y := by
    intro y hy
    have hleft := (hphi0' y hy).mul (hu4' y hy)
    have hright := (hphi4' y hy).mul (hu0' y hy)
    have hsub := hleft.sub hright
    convert hsub using 1
    dsimp only [W, W', u0, u4, p, r0, r4, q]
    push_cast
    ring
  have hW'cont : ContinuousOn W' (Icc (-lambda) lambda) := by
    dsimp only [W']
    exact continuousOn_const.mul (hphi0.mul hphi4)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hle hW hW' (hW'cont.intervalIntegrable_of_Icc hle)
  have hWPlus : W lambda = 0 := by
    simp [W, hu0PlusValue, hu4PlusValue]
  have hWMinus : W (-lambda) = 0 := by
    simp [W, hu0MinusValue, hu4MinusValue]
  have hIntW : (∫ y in (-lambda)..lambda, W' y) = 0 := by
    simpa only [hWPlus, hWMinus, sub_self] using hFTC
  have hfactor : ((theta0 - theta4 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr htheta
  have hprod :
      ((theta0 - theta4 : ℝ) : ℂ) *
          (∫ y in (-lambda)..lambda, phi0 y * phi4 y) = 0 := by
    rw [← intervalIntegral.integral_const_mul]
    simpa only [W'] using hIntW
  have hinterval : (∫ y in (-lambda)..lambda, phi0 y * phi4 y) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hfactor
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  exact hinterval

/-- The two selected normalized zero-extended physical Ferrers modes are
orthogonal in the exact production whole-line inner product. -/
theorem exists_modeZero_modeFour_selectedFerrersProductionProlatePair_orthogonal
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    ∃ (S0 : Mode4FerrersRegularEvenProlateSolution mProject K
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0))
      (S4 : Mode4FerrersRegularEvenProlateSolution mProject K
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2))
      (P : D0Pstar.ProlatePair),
      P.h0 = S0.normalizedPhysicalMode ∧
      P.h4 = S4.normalizedPhysicalMode ∧
      (∫ x : ℝ, starRingEnd ℂ (P.h0 x) * P.h4 x) = 0 ∧
      0 < P.I0 ∧ 0 < P.I4 ∧
      P.chi0 ≠ 0 ∧ P.chi2 ≠ 0 ∧
      (∀ x ∈ Icc (-P.pw.lambda) P.pw.lambda,
        D0Pstar.finiteFourierAction P.pw.lambda P.h0 x =
          (P.chi0 : ℂ) * P.h0 x) ∧
      (∀ x ∈ Icc (-P.pw.lambda) P.pw.lambda,
        D0Pstar.finiteFourierAction P.pw.lambda P.h4 x =
          (P.chi2 : ℂ) * P.h4 x) := by
  obtain ⟨S0, S4, P, hpw, hP0, hP4, hI0, hI4, hchi0, hchi2,
      hFourier0, hFourier4, hLambdaOrder⟩ :=
    exists_modeZero_modeFour_selectedFerrersProductionProlatePair
      mProject K hm hK hsep
  let lambda : ℝ := Real.sqrt mProject
  let theta0 : ℝ :=
    mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0 +
      mode4JacobiG mProject
  let theta4 : ℝ :=
    mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 +
      mode4JacobiG mProject
  let phi0 : ℝ → ℂ :=
    mode4PhysicalFerrersSeriesComplex mProject S0.coefficients
  let phi4 : ℝ → ℂ :=
    mode4PhysicalFerrersSeriesComplex mProject S4.coefficients
  let dphi0 : ℝ → ℂ :=
    mode4PhysicalFerrersFirstDerivativeSeriesComplex mProject S0.coefficients
  let dphi4 : ℝ → ℂ :=
    mode4PhysicalFerrersFirstDerivativeSeriesComplex mProject S4.coefficients
  have hlambda : 0 < lambda := Real.sqrt_pos.2 (by positivity)
  have htheta : theta0 ≠ theta4 := by
    dsimp only [theta0, theta4]
    linarith
  have hraw : (∫ x in Icc (-lambda) lambda, phi0 x * phi4 x) = 0 := by
    apply integral_mul_eq_zero_of_prolate_endpointFlux_eigenrelations
      lambda theta0 theta4 hlambda htheta phi0 dphi0 phi4 dphi4
    · simpa only [phi0, lambda] using S0.physicalComplex_continuousOn_closed hm
    · simpa only [phi4, lambda] using S4.physicalComplex_continuousOn_closed hm
    · intro y hy
      simpa only [phi0, dphi0, lambda] using S0.physicalComplex_hasDerivAt hm hy
    · intro y hy
      simpa only [phi4, dphi4, lambda] using S4.physicalComplex_hasDerivAt hm hy
    · intro y hy
      simpa only [phi0, dphi0, lambda, theta0] using
        S0.physicalComplex_flux_hasDerivAt hm hy
    · intro y hy
      simpa only [phi4, dphi4, lambda, theta4] using
        S4.physicalComplex_flux_hasDerivAt hm hy
    · simpa only [dphi0, lambda] using
        (S0.physicalComplex_zeroFlux_at_endpoints hm).1
    · simpa only [dphi0, lambda] using
        (S0.physicalComplex_zeroFlux_at_endpoints hm).2
    · simpa only [dphi4, lambda] using
        (S4.physicalComplex_zeroFlux_at_endpoints hm).1
    · simpa only [dphi4, lambda] using
        (S4.physicalComplex_zeroFlux_at_endpoints hm).2
  have horth :
      (∫ x : ℝ,
        starRingEnd ℂ (S0.normalizedPhysicalMode x) *
          S4.normalizedPhysicalMode x) = 0 := by
    have hfun : (fun x : ℝ ↦
        starRingEnd ℂ (S0.normalizedPhysicalMode x) *
          S4.normalizedPhysicalMode x) =
      (Icc (-lambda) lambda).indicator
        (fun x : ℝ ↦
          (S0.physicalL2Normalization : ℂ)⁻¹ *
            (S4.physicalL2Normalization : ℂ)⁻¹ *
              (phi0 x * phi4 x)) := by
      funext x
      by_cases hx : x ∈ Icc (-lambda) lambda
      · rw [indicator_of_mem hx]
        have hx' : x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
          simpa only [lambda] using hx
        have h0on : S0.normalizedPhysicalMode x =
            phi0 x / (S0.physicalL2Normalization : ℂ) := by
          rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
            Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
            indicator_of_mem hx']
        have h4on : S4.normalizedPhysicalMode x =
            phi4 x / (S4.physicalL2Normalization : ℂ) := by
          rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
            Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
            indicator_of_mem hx']
        rw [h0on, h4on, starRingEnd_apply, Complex.star_def, map_div₀]
        have hstar0 : conj (phi0 x) = phi0 x := by
          dsimp only [phi0, mode4PhysicalFerrersSeriesComplex]
          exact Complex.conj_ofReal _
        have hstarNorm0 :
            conj (S0.physicalL2Normalization : ℂ) =
              (S0.physicalL2Normalization : ℂ) := by
          exact Complex.conj_ofReal _
        rw [hstar0, hstarNorm0, div_eq_mul_inv]
        ring
      · rw [indicator_of_notMem hx]
        have hx' : x ∉ Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
          simpa only [lambda] using hx
        simp [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
          Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
          indicator_of_notMem hx']
    rw [hfun, integral_indicator measurableSet_Icc,
      integral_const_mul, hraw, mul_zero]
  refine ⟨S0, S4, P, hP0, hP4, ?_, hI0, hI4, hchi0, hchi2,
    hFourier0, hFourier4⟩
  simpa only [hP0, hP4] using horth

#print axioms integral_mul_eq_zero_of_prolate_endpointFlux_eigenrelations
#print axioms
  exists_modeZero_modeFour_selectedFerrersProductionProlatePair_orthogonal

end Q3.RouteB
