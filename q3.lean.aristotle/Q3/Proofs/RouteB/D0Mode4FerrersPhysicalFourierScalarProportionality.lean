import Q3.Proofs.RouteB.D0Mode4FerrersCenterValueNonzero
import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierEigenTransport
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Connected.Clopen

/-!
# Goal 058 G3: physical Ferrers finite-Fourier scalar proportionality

This file first proves uniqueness for complex solutions of the same prolate
divergence-form ODE from their value and weighted first derivative at the
center.  It then applies that receiver to the accepted physical Ferrers
solution and its finite-Fourier image.

Fresh supplier preflight at clean HEAD `f5d2f379` covered all 258 current
Route B modules and 2345 declarations with no proof holes or nonstandard
axioms.  The exact initial-value uniqueness plus even-source Fourier query
returned `CANDIDATE_ONLY`.

No zero count, scalar sign/order, `ProlatePair`, CCM Lemma 7.2, denominator
floor, schedule, G1, G3, Route B, or RH conclusion is asserted here.
-/

open Complex Filter MeasureTheory Metric Set
open scoped ContDiff ENat Topology

noncomputable section

namespace Q3.RouteB

private noncomputable def complexProlateFluxFirstOrderCLM
    (lambda theta x : ℝ) :
    (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  let A := (lambda ^ 2 - x ^ 2)⁻¹
  let B := (2 * Real.pi * lambda * x) ^ 2 - theta
  (A • ContinuousLinearMap.snd ℝ ℂ ℂ).prod
    (B • ContinuousLinearMap.fst ℝ ℂ ℂ)

@[simp]
private theorem complexProlateFluxFirstOrderCLM_apply
    (lambda theta x : ℝ) (p : ℂ × ℂ) :
    complexProlateFluxFirstOrderCLM lambda theta x p =
      (((lambda ^ 2 - x ^ 2)⁻¹ : ℝ) • p.2,
        (((2 * Real.pi * lambda * x) ^ 2 - theta : ℝ) • p.1)) := by
  simp [complexProlateFluxFirstOrderCLM]

private theorem complexProlateFluxFirstOrderCLM_continuousAt
    (lambda theta x : ℝ)
    (hx : x ∈ Ioo (-lambda) lambda) :
    ContinuousAt (complexProlateFluxFirstOrderCLM lambda theta) x := by
  have hp : 0 < lambda ^ 2 - x ^ 2 := by
    have hleft : 0 < x + lambda := by linarith [hx.1]
    have hright : 0 < lambda - x := by linarith [hx.2]
    nlinarith [mul_pos hleft hright]
  have hA : ContinuousAt (fun y : ℝ ↦ (lambda ^ 2 - y ^ 2)⁻¹) x := by
    exact (continuousAt_const.sub (continuousAt_id.pow 2)).inv₀ hp.ne'
  have hB :
      ContinuousAt
        (fun y : ℝ ↦ (2 * Real.pi * lambda * y) ^ 2 - theta) x := by
    fun_prop
  have hPair :
      ContinuousAt
        (fun y : ℝ ↦
          ((fun a : ℝ ↦ a • ContinuousLinearMap.snd ℝ ℂ ℂ)
              ((lambda ^ 2 - y ^ 2)⁻¹),
            (fun b : ℝ ↦ b • ContinuousLinearMap.fst ℝ ℂ ℂ)
              ((2 * Real.pi * lambda * y) ^ 2 - theta))) x := by
    exact (hA.smul continuousAt_const).prodMk
      (hB.smul continuousAt_const)
  simpa [complexProlateFluxFirstOrderCLM] using
    ((ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp hPair)

/-- Two complex functions satisfying the same prolate divergence-form ODE on
the open source window agree there when their value and first derivative agree
at the center.  The receiver uses the nonsingular flux state
`(f, (lambda^2-x^2) f')`; it carries no endpoint or spectral assertion. -/
theorem complex_prolate_divergence_solution_unique_of_center
    (lambda theta : ℝ) (hlambda : 0 < lambda)
    (f df g dg : ℝ → ℂ)
    (hf : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt f (df x) x)
    (hg : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt g (dg x) x)
    (hfluxf : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * f x)
        x)
    (hfluxg : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dg y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * g x)
        x)
    (hzero : f 0 = g 0)
    (hderivZero : df 0 = dg 0) :
    Set.EqOn f g (Ioo (-lambda) lambda) := by
  let stateF : ℝ → ℂ × ℂ := fun x ↦
    (f x, (((lambda ^ 2 - x ^ 2 : ℝ) : ℂ) * df x))
  let stateG : ℝ → ℂ × ℂ := fun x ↦
    (g x, (((lambda ^ 2 - x ^ 2 : ℝ) : ℂ) * dg x))
  let vectorField : ℝ → (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
    complexProlateFluxFirstOrderCLM lambda theta
  have hStateFDeriv :
      ∀ x ∈ Ioo (-lambda) lambda,
        HasDerivAt stateF (vectorField x (stateF x)) x := by
    intro x hx
    have hp : 0 < lambda ^ 2 - x ^ 2 := by
      have hleft : 0 < x + lambda := by linarith [hx.1]
      have hright : 0 < lambda - x := by linarith [hx.2]
      nlinarith [mul_pos hleft hright]
    convert (hf x hx).prodMk (hfluxf x hx) using 1
    simp only [stateF, vectorField, complexProlateFluxFirstOrderCLM_apply]
    apply Prod.ext
    · rw [Complex.real_smul]
      push_cast
      have hpC : ((lambda ^ 2 - x ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hp.ne'
      have hpC' : (lambda : ℂ) ^ 2 - (x : ℂ) ^ 2 ≠ 0 := by
        simpa only [ofReal_sub, ofReal_pow] using hpC
      rw [← mul_assoc, inv_mul_cancel₀ hpC', one_mul]
    · simp only [Complex.real_smul, ofReal_sub, ofReal_pow, ofReal_mul]
  have hStateGDeriv :
      ∀ x ∈ Ioo (-lambda) lambda,
        HasDerivAt stateG (vectorField x (stateG x)) x := by
    intro x hx
    have hp : 0 < lambda ^ 2 - x ^ 2 := by
      have hleft : 0 < x + lambda := by linarith [hx.1]
      have hright : 0 < lambda - x := by linarith [hx.2]
      nlinarith [mul_pos hleft hright]
    convert (hg x hx).prodMk (hfluxg x hx) using 1
    simp only [stateG, vectorField, complexProlateFluxFirstOrderCLM_apply]
    apply Prod.ext
    · rw [Complex.real_smul]
      push_cast
      have hpC : ((lambda ^ 2 - x ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hp.ne'
      have hpC' : (lambda : ℂ) ^ 2 - (x : ℂ) ^ 2 ≠ 0 := by
        simpa only [ofReal_sub, ofReal_pow] using hpC
      rw [← mul_assoc, inv_mul_cancel₀ hpC', one_mul]
    · simp only [Complex.real_smul, ofReal_sub, ofReal_pow, ofReal_mul]
  have hStateFContinuous : ContinuousOn stateF (Ioo (-lambda) lambda) :=
    fun x hx ↦ (hStateFDeriv x hx).continuousAt.continuousWithinAt
  have hStateGContinuous : ContinuousOn stateG (Ioo (-lambda) lambda) :=
    fun x hx ↦ (hStateGDeriv x hx).continuousAt.continuousWithinAt
  have hLocalEq :
      ∀ x ∈ Ioo (-lambda) lambda,
        stateF x = stateG x → stateF =ᶠ[nhds x] stateG := by
    intro x hx hxState
    have hFieldContinuous : ContinuousAt vectorField x :=
      complexProlateFluxFirstOrderCLM_continuousAt lambda theta x hx
    have hNormEventually :
        ∀ᶠ y in nhds x, ‖vectorField y‖₊ < ‖vectorField x‖₊ + 1 :=
      hFieldContinuous.nnnorm.tendsto (Iio_mem_nhds (lt_add_one _))
    apply ODE_solution_unique_of_eventually
      (K := ‖vectorField x‖₊ + 1)
      (v := fun y ↦ vectorField y)
      (s := fun _ ↦ Set.univ)
    · filter_upwards [hNormEventually] with y hy
      exact ((vectorField y).lipschitz.weaken hy.le).lipschitzOnWith
    · filter_upwards [isOpen_Ioo.eventually_mem hx] with y hy
      exact ⟨hStateFDeriv y hy, Set.mem_univ _⟩
    · filter_upwards [isOpen_Ioo.eventually_mem hx] with y hy
      exact ⟨hStateGDeriv y hy, Set.mem_univ _⟩
    · exact hxState
  let I : Set ℝ := Ioo (-lambda) lambda
  let Z : Set I := {x | stateF x.1 = stateG x.1}
  letI : PreconnectedSpace I :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  have hFRestrictContinuous : Continuous (fun x : I ↦ stateF x.1) :=
    continuousOn_iff_continuous_restrict.mp hStateFContinuous
  have hGRestrictContinuous : Continuous (fun x : I ↦ stateG x.1) :=
    continuousOn_iff_continuous_restrict.mp hStateGContinuous
  have hZClosed : IsClosed Z := by
    exact isClosed_eq hFRestrictContinuous hGRestrictContinuous
  have hZOpen : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact (continuous_subtype_val.tendsto x) (hLocalEq x.1 x.2 hx)
  have hzeroMem : (0 : ℝ) ∈ Ioo (-lambda) lambda := by
    constructor <;> linarith
  have hZNonempty : Z.Nonempty := by
    refine ⟨⟨0, hzeroMem⟩, ?_⟩
    simp [Z, stateF, stateG, hzero, hderivZero]
  have hZUniv : Z = Set.univ :=
    (show IsClopen Z from ⟨hZClosed, hZOpen⟩).eq_univ hZNonempty
  intro x hx
  have hxZ : (⟨x, hx⟩ : I) ∈ Z := by
    rw [hZUniv]
    exact Set.mem_univ _
  exact congrArg Prod.fst hxZ

private theorem hasDerivAt_finiteFourierKernel_left_for_scalar_proportionality
    (x y : ℝ) :
    HasDerivAt (fun z : ℝ ↦ D0Pstar.finiteFourierKernel z y)
      (D0Pstar.finiteFourierKernel x y *
        (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) x := by
  have hlin :
      HasDerivAt
        (fun z : ℝ ↦ Complex.I * ((2 * Real.pi * z * y : ℝ) : ℂ))
        (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) x := by
    convert
      (ofRealCLM.hasDerivAt (x := x)).const_mul
        (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) using 1
    · funext z
      simp only [ofRealCLM_apply]
      push_cast
      ring
    · simp only [ofRealCLM_apply, ofReal_one]
      push_cast
      ring
  exact hlin.cexp

/-- Differentiation under the finite-Fourier integral needs continuity only on
the actual compact source window. -/
theorem D0Pstar.finiteFourierAction_hasDerivAt_of_continuousOn
    (lambda : ℝ) (phi : ℝ → ℂ)
    (hphi : ContinuousOn phi (Icc (-lambda) lambda)) (x : ℝ) :
    HasDerivAt (D0Pstar.finiteFourierAction lambda phi)
      (∫ y in Icc (-lambda) lambda,
        (D0Pstar.finiteFourierKernel x y *
          (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) * phi y) x := by
  let mu : Measure ℝ := volume.restrict (Icc (-lambda) lambda)
  let F : ℝ → ℝ → ℂ := fun z y ↦
    D0Pstar.finiteFourierKernel z y * phi y
  let F' : ℝ → ℝ → ℂ := fun z y ↦
    (D0Pstar.finiteFourierKernel z y *
      (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) * phi y
  let bound : ℝ → ℝ := fun y ↦
    ‖Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)‖ * ‖phi y‖
  have hF_cont (z : ℝ) : ContinuousOn (F z) (Icc (-lambda) lambda) := by
    dsimp only [F]
    exact
      (by
        unfold D0Pstar.finiteFourierKernel
        fun_prop : Continuous (fun y : ℝ ↦ D0Pstar.finiteFourierKernel z y)).continuousOn.mul
        hphi
  have hF'_cont (z : ℝ) : ContinuousOn (F' z) (Icc (-lambda) lambda) := by
    dsimp only [F']
    exact
      ((by
          unfold D0Pstar.finiteFourierKernel
          fun_prop : Continuous
            (fun y : ℝ ↦
              D0Pstar.finiteFourierKernel z y *
                (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)))).continuousOn).mul
        hphi
  have hbound_cont : ContinuousOn bound (Icc (-lambda) lambda) := by
    dsimp only [bound]
    exact
      ((by fun_prop : Continuous
          (fun y : ℝ ↦
            ‖Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)‖)).continuousOn).mul
        hphi.norm
  have hF_meas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) mu :=
    Filter.Eventually.of_forall fun z ↦
      (hF_cont z).aestronglyMeasurable measurableSet_Icc
  have hF_int : Integrable (F x) mu := by
    simpa only [mu] using (hF_cont x).integrableOn_compact isCompact_Icc
  have hF'_meas : AEStronglyMeasurable (F' x) mu :=
    (hF'_cont x).aestronglyMeasurable measurableSet_Icc
  have hbound_int : Integrable bound mu := by
    simpa only [mu] using hbound_cont.integrableOn_compact isCompact_Icc
  have hbound : ∀ᵐ y ∂mu, ∀ z ∈ ball x 1, ‖F' z y‖ ≤ bound y := by
    filter_upwards [] with y
    intro z _
    dsimp only [F', bound]
    rw [norm_mul, norm_mul]
    have hkernel : ‖D0Pstar.finiteFourierKernel z y‖ = 1 := by
      unfold D0Pstar.finiteFourierKernel
      rw [Complex.norm_exp]
      simp
    rw [hkernel, one_mul]
  have hdiff : ∀ᵐ y ∂mu, ∀ z ∈ ball x 1,
      HasDerivAt (F · y) (F' z y) z := by
    filter_upwards [] with y
    intro z _
    simpa only [F, F'] using
      (hasDerivAt_finiteFourierKernel_left_for_scalar_proportionality z y).mul_const
        (phi y)
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := mu) (F := F) (F' := F') (bound := bound)
      (x₀ := x) (ε := 1) one_pos hF_meas hF_int hF'_meas
      hbound hbound_int hdiff
  simpa only [D0Pstar.finiteFourierAction, mu, F, F'] using hmain.2

/-- The literal first derivative integral of the finite-Fourier action. -/
noncomputable def D0Pstar.finiteFourierFirstDerivative
    (lambda : ℝ) (phi : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Icc (-lambda) lambda,
    (D0Pstar.finiteFourierKernel x y *
      (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) * phi y

/-- The literal second derivative integral of the finite-Fourier action. -/
noncomputable def D0Pstar.finiteFourierSecondDerivative
    (lambda : ℝ) (phi : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Icc (-lambda) lambda,
    ((D0Pstar.finiteFourierKernel x y *
        (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) *
      (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))) * phi y

theorem D0Pstar.finiteFourierAction_hasDerivAt_firstDerivative
    (lambda : ℝ) (phi : ℝ → ℂ)
    (hphi : ContinuousOn phi (Icc (-lambda) lambda)) (x : ℝ) :
    HasDerivAt (D0Pstar.finiteFourierAction lambda phi)
      (D0Pstar.finiteFourierFirstDerivative lambda phi x) x := by
  exact D0Pstar.finiteFourierAction_hasDerivAt_of_continuousOn
    lambda phi hphi x

theorem D0Pstar.finiteFourierFirstDerivative_hasDerivAt_secondDerivative
    (lambda : ℝ) (phi : ℝ → ℂ)
    (hphi : ContinuousOn phi (Icc (-lambda) lambda)) (x : ℝ) :
    HasDerivAt (D0Pstar.finiteFourierFirstDerivative lambda phi)
      (D0Pstar.finiteFourierSecondDerivative lambda phi x) x := by
  let a : ℝ → ℂ := fun y ↦
    Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)
  let psi : ℝ → ℂ := fun y ↦ a y * phi y
  have hpsi : ContinuousOn psi (Icc (-lambda) lambda) := by
    dsimp only [psi, a]
    exact
      ((by fun_prop : Continuous
          (fun y : ℝ ↦ Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))).continuousOn).mul
        hphi
  have h :=
    D0Pstar.finiteFourierAction_hasDerivAt_of_continuousOn
      lambda psi hpsi x
  convert h using 1
  · funext z
    unfold D0Pstar.finiteFourierFirstDerivative
    unfold D0Pstar.finiteFourierAction
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [psi, a]
    ring
  · unfold D0Pstar.finiteFourierSecondDerivative
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [psi, a]
    ring

/-- A finite-Fourier action over a symmetric window is even when its source is
even. -/
theorem D0Pstar.finiteFourierAction_even
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (phi : ℝ → ℂ)
    (hphi : Function.Even phi) :
    Function.Even (D0Pstar.finiteFourierAction lambda phi) := by
  intro x
  have hle : -lambda ≤ lambda := by linarith
  let F : ℝ → ℂ := fun y ↦
    D0Pstar.finiteFourierKernel (-x) y * phi y
  calc
    D0Pstar.finiteFourierAction lambda phi (-x) =
        ∫ y in (-lambda)..lambda, F y := by
      unfold D0Pstar.finiteFourierAction
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    _ = ∫ y in (-lambda)..lambda, F (-y) := by
      symm
      simpa only [neg_neg] using
        (intervalIntegral.integral_comp_neg (f := F) (a := -lambda) (b := lambda))
    _ = ∫ y in (-lambda)..lambda,
          D0Pstar.finiteFourierKernel x y * phi y := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only [F]
      rw [hphi y]
      unfold D0Pstar.finiteFourierKernel
      congr 2
      push_cast
      ring
    _ = D0Pstar.finiteFourierAction lambda phi x := by
      unfold D0Pstar.finiteFourierAction
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]

private theorem derivative_value_zero_of_even
    (f : ℝ → ℂ) (d : ℂ) (heven : Function.Even f)
    (hderiv : HasDerivAt f d 0) :
    d = 0 := by
  have hneg : HasDerivAt (fun x : ℝ ↦ f (-x)) (-d) 0 := by
    have hAtNegZero : HasDerivAt f d (-0) := by simpa using hderiv
    convert hAtNegZero.scomp 0 (hasDerivAt_neg 0) using 1
    all_goals norm_num
  have hfun : (fun x : ℝ ↦ f (-x)) = f := by
    funext x
    exact heven x
  rw [hfun] at hneg
  exact CharZero.neg_eq_self_iff.mp (hneg.unique hderiv)

private theorem Mode4FerrersRegularEvenProlateSolution.physicalComplex_even
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ) :
    Function.Even
      (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) := by
  intro u
  have hevenReal := S.even (u / Real.sqrt mProject)
  have hevenComplex := congrArg (fun r : ℝ ↦ (r : ℂ)) hevenReal
  simpa only [mode4PhysicalFerrersSeriesComplex,
    mode4PhysicalFerrersSeries, neg_div] using hevenComplex

/-- The finite-Fourier image of every accepted physical Ferrers solution is a
complex scalar multiple of that solution on the exact closed physical window.

The scalar is constructed from the center ratio.  This theorem does not prove
that it is real, nonzero, positive, ordered against another mode, or equal to
the source-normalized `chi0`/`chi2`. -/
theorem Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_scalar_mul
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ∃ chi : ℂ, ∀ x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject),
      D0Pstar.finiteFourierAction (Real.sqrt mProject)
          (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) x =
        chi * mode4PhysicalFerrersSeriesComplex mProject S.coefficients x := by
  let lambda : ℝ := Real.sqrt mProject
  let theta : ℝ := Λ + mode4JacobiG mProject
  let f : ℝ → ℂ :=
    mode4PhysicalFerrersSeriesComplex mProject S.coefficients
  let df : ℝ → ℂ :=
    mode4PhysicalFerrersFirstDerivativeSeriesComplex mProject S.coefficients
  let g : ℝ → ℂ := D0Pstar.finiteFourierAction lambda f
  let dg : ℝ → ℂ := D0Pstar.finiteFourierFirstDerivative lambda f
  let ddg : ℝ → ℂ := D0Pstar.finiteFourierSecondDerivative lambda f
  have hlambda : 0 < lambda := Real.sqrt_pos.2 (by positivity)
  have hzeroMem : (0 : ℝ) ∈ Ioo (-lambda) lambda := by
    constructor <;> linarith
  have hfContinuous : ContinuousOn f (Icc (-lambda) lambda) := by
    simpa only [f, lambda] using S.physicalComplex_continuousOn_closed hm
  have hfDeriv : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt f (df x) x := by
    intro x hx
    simpa only [f, df, lambda] using S.physicalComplex_hasDerivAt hm hx
  have hfFlux : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * df y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * f x)
        x := by
    intro x hx
    simpa only [f, df, lambda, theta, sub_mul] using
      S.physicalComplex_flux_hasDerivAt hm hx
  have hgDeriv : ∀ x : ℝ, HasDerivAt g (dg x) x := by
    intro x
    exact D0Pstar.finiteFourierAction_hasDerivAt_firstDerivative
      lambda f hfContinuous x
  have hdgDeriv : ∀ x : ℝ, HasDerivAt dg (ddg x) x := by
    intro x
    exact D0Pstar.finiteFourierFirstDerivative_hasDerivAt_secondDerivative
      lambda f hfContinuous x
  have hgFlux : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dg y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * g x)
        x := by
    intro x hx
    have hp :
        HasDerivAt (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ)))
          (((-2 * x : ℝ) : ℂ)) x := by
      convert
        ((hasDerivAt_const x (lambda ^ 2)).sub (hasDerivAt_pow 2 x)).ofReal_comp using 1
      all_goals norm_num
    have hprod := hp.mul (hdgDeriv x)
    have heigen :=
      S.physicalFiniteFourierAction_preservesProlateWaveEigenrelation hm x
    have hderivEq : ∀ y : ℝ, deriv g y = dg y := by
      intro y
      exact (hgDeriv y).deriv
    have hprodDeriv :
        deriv
          (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dg y)) x =
          (((-2 * x : ℝ) : ℂ) * dg x +
            (((lambda ^ 2 - x ^ 2 : ℝ) : ℂ) * ddg x)) := by
      exact hprod.deriv
    have heigen' :
        -deriv
            (fun y : ℝ ↦
              (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * dg y)) x +
            ((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) * g x) =
          (theta : ℂ) * g x := by
      simpa only [D0Pstar.prolateWaveExpression, fderiv_deriv,
        g, f, lambda, theta, hderivEq] using heigen
    convert hprod using 1
    rw [hprodDeriv] at heigen'
    linear_combination heigen'
  have hfEven : Function.Even f := by
    simpa only [f] using S.physicalComplex_even
  have hgEven : Function.Even g := by
    exact D0Pstar.finiteFourierAction_even lambda hlambda.le f hfEven
  have hdfZero : df 0 = 0 :=
    derivative_value_zero_of_even f (df 0) hfEven (hfDeriv 0 hzeroMem)
  have hdgZero : dg 0 = 0 :=
    derivative_value_zero_of_even g (dg 0) hgEven (hgDeriv 0)
  have hfZero : f 0 ≠ 0 := by
    have hcenter :
        (mode4FerrersSeries S.coefficients 0 : ℂ) ≠ 0 := by
      exact_mod_cast S.center_value_ne_zero
    simpa only [f, mode4PhysicalFerrersSeriesComplex,
      mode4PhysicalFerrersSeries, zero_div] using hcenter
  let chi : ℂ := g 0 / f 0
  have hchiCenter : chi * f 0 = g 0 := by
    dsimp only [chi]
    exact div_mul_cancel₀ (g 0) hfZero
  let sf : ℝ → ℂ := fun x ↦ chi * f x
  let sdf : ℝ → ℂ := fun x ↦ chi * df x
  have hsfDeriv : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt sf (sdf x) x := by
    intro x hx
    simpa only [sf, sdf] using (hfDeriv x hx).const_mul chi
  have hsfFlux : ∀ x ∈ Ioo (-lambda) lambda,
      HasDerivAt
        (fun y : ℝ ↦ (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * sdf y))
        (((((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) - (theta : ℂ)) * sf x)
        x := by
    intro x hx
    have h := (hfFlux x hx).const_mul chi
    convert h using 1
    · funext y
      dsimp only [sdf]
      ring
    · dsimp only [sf]
      ring
  have heqOpen : Set.EqOn sf g (Ioo (-lambda) lambda) :=
    complex_prolate_divergence_solution_unique_of_center
      lambda theta hlambda sf sdf g dg hsfDeriv
      (fun x _ ↦ hgDeriv x) hsfFlux hgFlux hchiCenter
      (by simp [sdf, hdfZero, hdgZero])
  have hsfContinuous : ContinuousOn sf (Icc (-lambda) lambda) := by
    exact continuousOn_const.mul hfContinuous
  have hgContinuous : ContinuousOn g (Icc (-lambda) lambda) :=
    fun x _ ↦ (hgDeriv x).continuousAt.continuousWithinAt
  have heqClosed : Set.EqOn sf g (Icc (-lambda) lambda) := by
    apply heqOpen.of_subset_closure
      hsfContinuous hgContinuous Ioo_subset_Icc_self
    rw [closure_Ioo (by linarith : -lambda ≠ lambda)]
  refine ⟨chi, ?_⟩
  intro x hx
  change g x = chi * f x
  exact (heqClosed hx).symm

#print axioms complex_prolate_divergence_solution_unique_of_center
#print axioms D0Pstar.finiteFourierAction_hasDerivAt_of_continuousOn
#print axioms D0Pstar.finiteFourierFirstDerivative
#print axioms D0Pstar.finiteFourierSecondDerivative
#print axioms D0Pstar.finiteFourierAction_hasDerivAt_firstDerivative
#print axioms D0Pstar.finiteFourierFirstDerivative_hasDerivAt_secondDerivative
#print axioms D0Pstar.finiteFourierAction_even
#print axioms
  Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_scalar_mul

end Q3.RouteB
