import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierRealScalar
import Q3.Proofs.RouteB.ProlateFiniteFourierNonvanishing
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Goal 058 G3: the physical Ferrers Fourier scalar is nonzero

The real proportionality theorem alone does not exclude scalar zero because
its equality is restricted to the physical window.  This file supplies the
missing analytic-continuation bridge for a compact-window Fourier integral.
It then combines that bridge with the existing Fourier-inversion
nonvanishing theorem.

The declared full EnvDump before this write covered all `260/260` current
Route B modules and `2354` declarations, with no stale modules, proof holes,
or nonstandard dependencies; six source-less orphan oleans were excluded.
The exact supplier preflight query

`finite Fourier compact window entire extension analytic identity theorem
nonzero on interior interval Fourier inversion`

returned `CANDIDATE_ONLY` on that complete environment.

This file proves nonzero real scalar proportionality only.  It does not prove
the scalar sign or mode-zero/mode-four ordering, instantiate `ProlatePair`,
prove the CCM floor, or close Goal 058 G3.
-/

open Complex Filter MeasureTheory Metric Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- Entire extension of the finite-Fourier action in its frequency argument.
On the real axis it agrees exactly with `finiteFourierAction`. -/
noncomputable def finiteFourierEntire
    (lambda : ℝ) (phi : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ y in Icc (-lambda) lambda,
    Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * z * Complex.I) * phi y

/-- A continuous compact-window source has an everywhere complex
differentiable finite-Fourier extension. -/
theorem finiteFourierEntire_differentiable
    (lambda : ℝ) (phi : ℝ → ℂ)
    (hphi : ContinuousOn phi (Icc (-lambda) lambda)) :
    Differentiable ℂ (finiteFourierEntire lambda phi) := by
  intro z0
  let F : ℂ → ℝ → ℂ := fun z y ↦
    Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * z * Complex.I) * phi y
  let F' : ℂ → ℝ → ℂ := fun z y ↦
    ((((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * z * Complex.I)) * phi y
  let B : ℝ → ℝ := fun y ↦
    (2 * Real.pi * |y|) *
      Real.exp ((2 * Real.pi * |y|) * (‖z0‖ + 1)) * ‖phi y‖
  have hFint (z : ℂ) : Integrable (F z)
      (volume.restrict (Icc (-lambda) lambda)) := by
    have hcont : ContinuousOn (F z) (Icc (-lambda) lambda) := by
      dsimp only [F]
      fun_prop
    exact hcont.integrableOn_Icc
  have hF'int (z : ℂ) : Integrable (F' z)
      (volume.restrict (Icc (-lambda) lambda)) := by
    have hcont : ContinuousOn (F' z) (Icc (-lambda) lambda) := by
      dsimp only [F']
      fun_prop
    exact hcont.integrableOn_Icc
  have hBint : Integrable B
      (volume.restrict (Icc (-lambda) lambda)) := by
    have hA : Continuous (fun y : ℝ ↦ 2 * Real.pi * |y|) := by
      fun_prop
    have hE : Continuous
        (fun y : ℝ ↦ Real.exp ((2 * Real.pi * |y|) * (‖z0‖ + 1))) := by
      fun_prop
    have hcont : ContinuousOn B (Icc (-lambda) lambda) := by
      exact (hA.continuousOn.mul hE.continuousOn).mul hphi.norm
    exact hcont.integrableOn_Icc
  have hbound : ∀ᵐ y ∂volume.restrict (Icc (-lambda) lambda),
      ∀ z ∈ ball z0 1, ‖F' z y‖ ≤ B y := by
    refine (ae_restrict_mem measurableSet_Icc).mono ?_
    intro y _ z hz
    have hzNorm : ‖z‖ ≤ ‖z0‖ + 1 := by
      calc
        ‖z‖ = ‖(z - z0) + z0‖ := by ring_nf
        _ ≤ ‖z - z0‖ + ‖z0‖ := norm_add_le _ _
        _ ≤ ‖z0‖ + 1 := by
          rw [mem_ball, dist_eq_norm] at hz
          linarith
    have hcoef :
        ‖(((2 * Real.pi * y : ℝ) : ℂ) * z * Complex.I)‖ ≤
          (2 * Real.pi * |y|) * (‖z0‖ + 1) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
      have hpi : 0 ≤ 2 * Real.pi := by positivity
      rw [abs_mul, abs_of_nonneg hpi]
      exact mul_le_mul_of_nonneg_left hzNorm
        (mul_nonneg hpi (abs_nonneg y))
    dsimp only [F', B]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hexp :
        Real.exp ((((2 * Real.pi * y : ℝ) : ℂ) * z * Complex.I).re) ≤
          Real.exp ((2 * Real.pi * |y|) * (‖z0‖ + 1)) := by
      apply Real.exp_le_exp.mpr
      exact (Complex.re_le_norm _).trans hcoef
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hpi]
    gcongr
  have hdiff : ∀ᵐ y ∂volume.restrict (Icc (-lambda) lambda),
      ∀ z ∈ ball z0 1, HasDerivAt (F · y) (F' z y) z := by
    refine (ae_restrict_mem measurableSet_Icc).mono ?_
    intro y _ z _
    dsimp only [F, F']
    convert
      ((Complex.hasDerivAt_exp
        (((2 * Real.pi * y : ℝ) : ℂ) * z * Complex.I)).comp z
          (((hasDerivAt_id z).const_mul
            ((2 * Real.pi * y : ℝ) : ℂ)).mul_const Complex.I)).mul_const
        (phi y) using 1
    ring
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Icc (-lambda) lambda))
      (F := F) (F' := F') (bound := B) (x₀ := z0)
      (by positivity : (0 : ℝ) < 1)
      (Eventually.of_forall fun z ↦ (hFint z).aestronglyMeasurable)
      (hFint z0) (hF'int z0).aestronglyMeasurable hbound hBint hdiff
  simpa only [finiteFourierEntire, F] using hmain.2.differentiableAt

/-- The entire extension agrees with the project positive-phase finite
Fourier action on the real axis. -/
theorem finiteFourierEntire_ofReal
    (lambda x : ℝ) (phi : ℝ → ℂ) :
    finiteFourierEntire lambda phi (x : ℂ) =
      finiteFourierAction lambda phi x := by
  unfold finiteFourierEntire finiteFourierAction
  apply integral_congr_ae
  filter_upwards [] with y
  unfold finiteFourierKernel
  congr 2
  push_cast
  ring

/-- A continuous compact-window source with a nonzero interior value has a
nonzero finite-Fourier value already inside that same open window. -/
theorem exists_finiteFourierAction_ne_zero_on_Ioo
    (lambda : ℝ) (phi : ℝ → ℂ) (x0 : ℝ)
    (hlambda : 0 < lambda)
    (hphi : ContinuousOn phi (Icc (-lambda) lambda))
    (hx0 : x0 ∈ Ioo (-lambda) lambda)
    (hne : phi x0 ≠ 0) :
    ∃ x ∈ Ioo (-lambda) lambda,
      finiteFourierAction lambda phi x ≠ 0 := by
  by_contra hwindow
  push_neg at hwindow
  let E : ℂ → ℂ := finiteFourierEntire lambda phi
  have hEdiff : Differentiable ℂ E := by
    exact finiteFourierEntire_differentiable lambda phi hphi
  have hclosure : (0 : ℂ) ∈ closure ({z : ℂ | E z = 0} \ {(0 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro epsilon hepsilon
    let t : ℝ := min (lambda / 2) (epsilon / 2)
    have ht : 0 < t := lt_min (half_pos hlambda) (half_pos hepsilon)
    have htLambda : t < lambda :=
      (min_le_left _ _).trans_lt (half_lt_self hlambda)
    have htEpsilon : t < epsilon :=
      (min_le_right _ _).trans_lt (half_lt_self hepsilon)
    refine ⟨(t : ℂ), ?_, ?_⟩
    · constructor
      · change finiteFourierEntire lambda phi (t : ℂ) = 0
        rw [finiteFourierEntire_ofReal]
        exact hwindow t ⟨by linarith, htLambda⟩
      · simpa only [Set.mem_singleton_iff, Complex.ofReal_eq_zero] using
          ht.ne'
    · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht] using htEpsilon
  have hanalytic : AnalyticOnNhd ℂ E univ :=
    hEdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hzeroOn : Set.EqOn E 0 univ := by
    apply hanalytic.eqOn_of_preconnected_of_mem_closure
      analyticOnNhd_const isPreconnected_univ (mem_univ 0)
    simpa only [Pi.zero_apply] using hclosure
  have hzeroAll (x : ℝ) : finiteFourierAction lambda phi x = 0 := by
    rw [← finiteFourierEntire_ofReal]
    exact hzeroOn (mem_univ (x : ℂ))
  obtain ⟨x, hx⟩ :=
    finiteFourierAction_ne_zero_of_integrableOn_continuousAt
      lambda phi x0 hphi.integrableOn_Icc hx0
      (hphi.continuousAt
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx0)
          Ioo_subset_Icc_self)) hne
  exact hx (hzeroAll x)

#print axioms finiteFourierEntire
#print axioms finiteFourierEntire_differentiable
#print axioms finiteFourierEntire_ofReal
#print axioms exists_finiteFourierAction_ne_zero_on_Ioo

end Q3.RouteB.D0Pstar

namespace Q3.RouteB

/-- Every accepted physical Ferrers solution has a nonzero real
finite-Fourier proportionality scalar on the exact closed physical window. -/
theorem Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ∃ chi : ℝ, chi ≠ 0 ∧
      ∀ x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject),
        D0Pstar.finiteFourierAction (Real.sqrt mProject)
            (mode4PhysicalFerrersSeriesComplex mProject S.coefficients) x =
          (chi : ℂ) *
            mode4PhysicalFerrersSeriesComplex mProject S.coefficients x := by
  obtain ⟨chi, hchi⟩ :=
    S.exists_physicalFiniteFourierAction_eq_real_scalar_mul hm
  let lambda : ℝ := Real.sqrt mProject
  let phi : ℝ → ℂ :=
    mode4PhysicalFerrersSeriesComplex mProject S.coefficients
  have hlambda : 0 < lambda := Real.sqrt_pos.2 (by positivity)
  have hphi : ContinuousOn phi (Icc (-lambda) lambda) := by
    simpa only [phi, lambda] using S.physicalComplex_continuousOn_closed hm
  have hzeroMem : (0 : ℝ) ∈ Ioo (-lambda) lambda := by
    constructor <;> linarith
  have hphiZero : phi 0 ≠ 0 := by
    have hcenter : (mode4FerrersSeries S.coefficients 0 : ℂ) ≠ 0 := by
      exact_mod_cast S.center_value_ne_zero
    simpa only [phi, mode4PhysicalFerrersSeriesComplex,
      mode4PhysicalFerrersSeries, zero_div] using hcenter
  have hchiZero : chi ≠ 0 := by
    intro hzero
    obtain ⟨x, hxmem, hxne⟩ :=
      D0Pstar.exists_finiteFourierAction_ne_zero_on_Ioo
        lambda phi 0 hlambda hphi hzeroMem hphiZero
    have hxclosed : x ∈
        Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
      simpa only [lambda] using ⟨hxmem.1.le, hxmem.2.le⟩
    have hxrel := hchi x hxclosed
    rw [hzero, Complex.ofReal_zero, zero_mul] at hxrel
    exact hxne (by simpa only [phi, lambda] using hxrel)
  exact ⟨chi, hchiZero, hchi⟩

#print axioms
  Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul

end Q3.RouteB
