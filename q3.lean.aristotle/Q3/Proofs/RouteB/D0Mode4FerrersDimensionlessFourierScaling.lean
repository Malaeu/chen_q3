import Q3.Proofs.RouteB.D0Mode4FerrersNormalizedActualModeLocalFields

/-!
# Goal 058 G3: dimensionless-to-physical finite-Fourier scaling

This source-free leaf proves the exact change of variables between the
dimensionless Slepian convention on `[-1,1]` and the production physical
window.  In particular, a dimensionless plus-phase Fourier scalar `mu`
becomes the physical scalar `sqrt mProject * mu` after the existing positive
normalization.

No dimensionless source eigenrelation, scalar positivity or order, nodal
count, actual-mode assembly, G3 closure, Route B promotion, or RH claim is
made here.
-/

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB

/-- The dimensionless Slepian bandwidth in project coordinates. -/
noncomputable def mode4SlepianC (mProject : ℕ) : ℝ :=
  2 * Real.pi * (mProject : ℝ)

/-- The dimensionless plus-phase finite-Fourier action attached to the
already selected Ferrers coefficient carrier. -/
noncomputable def selectedFerrersDimensionlessFourierAction
    (c : ℝ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∫ s in Icc (-1 : ℝ) 1,
    Complex.exp (Complex.I * ((c * t * s : ℝ) : ℂ)) *
      (mode4FerrersSeries a s : ℂ)

/-- Exact finite-Fourier change of variables from the physical Ferrers mode
to its dimensionless selected carrier. -/
theorem physicalFerrers_finiteFourierAction_eq_scale_dimensionless
    {mProject K : ℕ} {Λ t : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    D0Pstar.finiteFourierAction (Real.sqrt mProject)
        (mode4PhysicalFerrersSeriesComplex mProject S.coefficients)
        (Real.sqrt mProject * t) =
      (Real.sqrt mProject : ℂ) *
        selectedFerrersDimensionlessFourierAction
          (mode4SlepianC mProject) S.coefficients t := by
  let s : ℝ := Real.sqrt mProject
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsq : s ^ 2 = (mProject : ℝ) := Real.sq_sqrt (by positivity)
  let F : ℝ → ℂ := fun u =>
    Complex.exp
      (Complex.I * ((mode4SlepianC mProject * t * u : ℝ) : ℂ)) *
        (mode4FerrersSeries S.coefficients u : ℂ)
  have hscale := intervalIntegral.integral_comp_div
    (f := F) (a := -s) (b := s) (c := s) hs.ne'
  have hleft :
      (∫ y in (-s)..s,
        D0Pstar.finiteFourierKernel (s * t) y *
          mode4PhysicalFerrersSeriesComplex
            mProject S.coefficients y) =
        s • ∫ u in (-1 : ℝ)..1, F u := by
    have hneg : -s / s = (-1 : ℝ) := by field_simp [hs.ne']
    have hpos : s / s = (1 : ℝ) := by field_simp [hs.ne']
    rw [hneg, hpos] at hscale
    calc
      (∫ y in (-s)..s,
        D0Pstar.finiteFourierKernel (s * t) y *
          mode4PhysicalFerrersSeriesComplex
            mProject S.coefficients y) =
          ∫ y in (-s)..s, F (y / s) := by
            apply intervalIntegral.integral_congr
            intro y _hy
            dsimp only [F]
            rw [D0Pstar.finiteFourierKernel,
              mode4PhysicalFerrersSeriesComplex,
              mode4PhysicalFerrersSeries]
            have harg :
                2 * Real.pi * (s * t) * y =
                  mode4SlepianC mProject * t * (y / s) := by
              rw [mode4SlepianC, ← hsq]
              field_simp [hs.ne']
            rw [harg]
      _ = s • ∫ u in (-1 : ℝ)..1, F u := hscale
  rw [D0Pstar.finiteFourierAction]
  change (∫ y in Icc (-s) s,
    D0Pstar.finiteFourierKernel (s * t) y *
      mode4PhysicalFerrersSeriesComplex mProject S.coefficients y) = _
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -s ≤ s)]
  rw [hleft]
  change (s : ℂ) * (∫ u in (-1 : ℝ)..1, F u) = _
  congr 1
  rw [selectedFerrersDimensionlessFourierAction,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/-- The same exact scaling after the existing canonical positive physical
`L²` normalization. -/
theorem normalizedPhysicalMode_finiteFourierAction_eq_scale_dimensionless
    {mProject K : ℕ} {Λ t : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    D0Pstar.finiteFourierAction (Real.sqrt mProject)
        S.normalizedPhysicalMode (Real.sqrt mProject * t) =
      (Real.sqrt mProject : ℂ) *
        selectedFerrersDimensionlessFourierAction
          (mode4SlepianC mProject) S.coefficients t /
            (S.physicalL2Normalization : ℂ) := by
  let s : ℝ := Real.sqrt mProject
  have hinside : ∀ y ∈ Icc (-s) s,
      S.normalizedPhysicalMode y =
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients y /
          (S.physicalL2Normalization : ℂ) := by
    intro y hy
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension]
    rw [indicator_of_mem (by simpa only [s] using hy)]
  rw [D0Pstar.finiteFourierAction]
  have hcongr :
      (∫ y in Icc (-s) s,
        D0Pstar.finiteFourierKernel (s * t) y *
          S.normalizedPhysicalMode y) =
      (∫ y in Icc (-s) s,
        (D0Pstar.finiteFourierKernel (s * t) y *
          mode4PhysicalFerrersSeriesComplex mProject S.coefficients y) /
            (S.physicalL2Normalization : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    change D0Pstar.finiteFourierKernel (s * t) y *
        S.normalizedPhysicalMode y =
      (D0Pstar.finiteFourierKernel (s * t) y *
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients y) /
          (S.physicalL2Normalization : ℂ)
    rw [hinside y hy]
    ring
  change (∫ y in Icc (-s) s,
    D0Pstar.finiteFourierKernel (s * t) y *
      S.normalizedPhysicalMode y) = _
  rw [hcongr]
  simp only [div_eq_mul_inv]
  rw [integral_mul_const]
  rw [show
      (∫ y in Icc (-s) s,
        D0Pstar.finiteFourierKernel (s * t) y *
          mode4PhysicalFerrersSeriesComplex mProject S.coefficients y) =
        (s : ℂ) * selectedFerrersDimensionlessFourierAction
          (mode4SlepianC mProject) S.coefficients t by
    simpa only [s, D0Pstar.finiteFourierAction] using
      physicalFerrers_finiteFourierAction_eq_scale_dimensionless S hm]

/-- A dimensionless plus-phase eigenrelation transports to the exact
physical normalized eigenrelation with scalar `sqrt mProject * mu`. -/
theorem normalizedPhysicalMode_finiteFourier_eq_lambda_mul_of_dimensionless
    {mProject K : ℕ} {Λ t : ℝ} {mu : ℂ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsource : selectedFerrersDimensionlessFourierAction
        (mode4SlepianC mProject) S.coefficients t =
      mu * (mode4FerrersSeries S.coefficients t : ℂ)) :
    D0Pstar.finiteFourierAction (Real.sqrt mProject)
        S.normalizedPhysicalMode (Real.sqrt mProject * t) =
      ((Real.sqrt mProject : ℂ) * mu) *
        S.normalizedPhysicalMode (Real.sqrt mProject * t) := by
  rw [normalizedPhysicalMode_finiteFourierAction_eq_scale_dimensionless
    S hm, hsource]
  have hmem : Real.sqrt mProject * t ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
    have hs : 0 ≤ Real.sqrt (mProject : ℝ) := Real.sqrt_nonneg _
    constructor
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
    indicator_of_mem hmem, mode4PhysicalFerrersSeriesComplex,
    mode4PhysicalFerrersSeries]
  rw [show Real.sqrt mProject * t / Real.sqrt mProject = t by field_simp]
  ring

#print axioms physicalFerrers_finiteFourierAction_eq_scale_dimensionless
#print axioms normalizedPhysicalMode_finiteFourierAction_eq_scale_dimensionless
#print axioms normalizedPhysicalMode_finiteFourier_eq_lambda_mul_of_dimensionless

end Q3.RouteB
