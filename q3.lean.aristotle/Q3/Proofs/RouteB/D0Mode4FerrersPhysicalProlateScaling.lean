import Q3.Proofs.RouteB.D0Mode4FerrersRegularEvenProlateSolution

/-!
# Goal 058 G3: physical scaling of the accepted mode-four Ferrers solution

This file transports the dimensionless interval `(-1,1)` to the physical
window `(-sqrt m, sqrt m)`.  The scaled first- and second-derivative series are
proved to be the actual derivatives, and the stored dimensionless prolate ODE
is converted to the exact physical `PW_lambda` equation with
`lambda = sqrt m`.

The local knowledge preflight at `Goal058.G3.Mode4PhysicalScale` found the
source-pinned scale in the current architecture memorandum but no existing
Lean supplier.  This file consumes an already accepted solution or an already
proved matching root.  It does not prove root existence, ordered mode-four
selection, a finite-Fourier eigenrelation, or CCM Lemma 7.2.
-/

namespace Q3.RouteB

noncomputable def mode4PhysicalFerrersSeries
    (mProject : ℕ) (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  mode4FerrersSeries a (u / Real.sqrt mProject)

noncomputable def mode4PhysicalFerrersFirstDerivativeSeries
    (mProject : ℕ) (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  (Real.sqrt mProject)⁻¹ *
    mode4FerrersFirstDerivativeSeries a (u / Real.sqrt mProject)

noncomputable def mode4PhysicalFerrersSecondDerivativeSeries
    (mProject : ℕ) (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  (mProject : ℝ)⁻¹ *
    mode4FerrersSecondDerivativeSeries a (u / Real.sqrt mProject)

private theorem mode4Physical_scale_mem_Ioo
    {mProject : ℕ} (hm : 2 ≤ mProject) {u : ℝ}
    (hu : u ∈ Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    u / Real.sqrt mProject ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hs : 0 < Real.sqrt (mProject : ℝ) := Real.sqrt_pos.2 hmR
  constructor
  · rw [lt_div_iff₀ hs]
    simpa using hu.1
  · exact (div_lt_one hs).2 hu.2

/-- Physical-window `C²` regularity obtained by composing the accepted
dimensionless solution with `u ↦ u / sqrt(mProject)`. -/
theorem Mode4FerrersRegularEvenProlateSolution.physical_contDiffOn_two_open
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    ContDiffOn ℝ 2
      (mode4PhysicalFerrersSeries mProject S.coefficients)
      (Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) := by
  have hscale : ContDiff ℝ 2 (fun u : ℝ => u / Real.sqrt mProject) :=
    contDiff_id.div_const _
  have hmap : Set.MapsTo (fun u : ℝ => u / Real.sqrt mProject)
      (Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject))
      (Set.Ioo (-1 : ℝ) 1) :=
    fun _ hu => mode4Physical_scale_mem_Ioo hm hu
  simpa [mode4PhysicalFerrersSeries, Function.comp_def] using
    S.contDiffOn_two_open.comp hscale.contDiffOn hmap

/-- The declared physical first-derivative series is the actual derivative of
the scaled Ferrers series. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalFerrersSeries_hasDerivAt_firstDerivativeSeries
    {mProject K : ℕ} {Λ u : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hu : u ∈ Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    HasDerivAt
      (mode4PhysicalFerrersSeries mProject S.coefficients)
      (mode4PhysicalFerrersFirstDerivativeSeries
        mProject S.coefficients u)
      u := by
  have hs : 0 < Real.sqrt (mProject : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hscale : HasDerivAt (fun z : ℝ => z / Real.sqrt mProject)
      (1 / Real.sqrt mProject) u :=
    (hasDerivAt_id u).div_const _
  have h := (S.ferrersSeries_hasDerivAt_firstDerivativeSeries
    (u / Real.sqrt mProject) (mode4Physical_scale_mem_Ioo hm hu)).comp
      u hscale
  simpa [mode4PhysicalFerrersSeries,
    mode4PhysicalFerrersFirstDerivativeSeries, one_div, mul_comm] using h

/-- The declared physical second-derivative series is the actual derivative
of the scaled first-derivative series. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
    {mProject K : ℕ} {Λ u : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hu : u ∈ Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    HasDerivAt
      (mode4PhysicalFerrersFirstDerivativeSeries mProject S.coefficients)
      (mode4PhysicalFerrersSecondDerivativeSeries
        mProject S.coefficients u)
      u := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hmne : (mProject : ℝ) ≠ 0 := hmR.ne'
  have hs : 0 < Real.sqrt (mProject : ℝ) := Real.sqrt_pos.2 hmR
  have hsne : Real.sqrt (mProject : ℝ) ≠ 0 := hs.ne'
  have hsq : (Real.sqrt (mProject : ℝ)) ^ 2 = (mProject : ℝ) :=
    Real.sq_sqrt hmR.le
  have hscale : HasDerivAt (fun z : ℝ => z / Real.sqrt mProject)
      (1 / Real.sqrt mProject) u :=
    (hasDerivAt_id u).div_const _
  have hinner :=
    (S.firstDerivativeSeries_hasDerivAt_secondDerivativeSeries
      (u / Real.sqrt mProject)
      (mode4Physical_scale_mem_Ioo hm hu)).comp u hscale
  have h :=
    (hasDerivAt_const u (Real.sqrt (mProject : ℝ))⁻¹).mul hinner
  have h' :
      HasDerivAt
        (mode4PhysicalFerrersFirstDerivativeSeries
          mProject S.coefficients)
        ((Real.sqrt (mProject : ℝ))⁻¹ *
          (mode4FerrersSecondDerivativeSeries S.coefficients
            (u / Real.sqrt mProject) *
            (Real.sqrt (mProject : ℝ))⁻¹))
        u := by
    simpa [mode4PhysicalFerrersFirstDerivativeSeries, one_div,
      Function.comp_def] using h
  have hinv : (mProject : ℝ)⁻¹ =
      (Real.sqrt (mProject : ℝ))⁻¹ *
        (Real.sqrt (mProject : ℝ))⁻¹ := by
    field_simp [hmne, hsne]
    exact hsq
  convert h' using 1
  simp only [mode4PhysicalFerrersSecondDerivativeSeries, hinv]
  ring

/-- Exact physical prolate ODE on `(-sqrt m, sqrt m)`.  The potential is
literally `(2*pi*sqrt(m)*u)^2`, so the dimensionless parameter remains
`mode4JacobiG m = (2*pi*m)^2`. -/
theorem Mode4FerrersRegularEvenProlateSolution.physicalProlateDifferentialEquation
    {mProject K : ℕ} {Λ u : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject)
    (hu : u ∈ Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) :
    -((mProject : ℝ) - u ^ 2) *
          mode4PhysicalFerrersSecondDerivativeSeries
            mProject S.coefficients u +
        2 * u *
          mode4PhysicalFerrersFirstDerivativeSeries
            mProject S.coefficients u +
        (2 * Real.pi * Real.sqrt mProject * u) ^ 2 *
          mode4PhysicalFerrersSeries mProject S.coefficients u =
      (Λ + mode4JacobiG mProject) *
        mode4PhysicalFerrersSeries mProject S.coefficients u := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  let s : ℝ := Real.sqrt (mProject : ℝ)
  have hs : 0 < s := by exact Real.sqrt_pos.2 hmR
  have hsne : s ≠ 0 := hs.ne'
  have hsq : s ^ 2 = (mProject : ℝ) := by
    exact Real.sq_sqrt hmR.le
  have hODE := S.prolateDifferentialEquation
    (u / Real.sqrt mProject) (mode4Physical_scale_mem_Ioo hm hu)
  change
    -(1 - (u / s) ^ 2) *
          mode4FerrersSecondDerivativeSeries S.coefficients (u / s) +
        2 * (u / s) *
          mode4FerrersFirstDerivativeSeries S.coefficients (u / s) +
        mode4JacobiG mProject * (u / s) ^ 2 *
          mode4FerrersSeries S.coefficients (u / s) =
      (Λ + mode4JacobiG mProject) *
        mode4FerrersSeries S.coefficients (u / s) at hODE
  change
    -((mProject : ℝ) - u ^ 2) *
          ((mProject : ℝ)⁻¹ *
            mode4FerrersSecondDerivativeSeries S.coefficients (u / s)) +
        2 * u *
          (s⁻¹ *
            mode4FerrersFirstDerivativeSeries S.coefficients (u / s)) +
        (2 * Real.pi * s * u) ^ 2 *
          mode4FerrersSeries S.coefficients (u / s) =
      (Λ + mode4JacobiG mProject) *
        mode4FerrersSeries S.coefficients (u / s)
  dsimp [mode4JacobiG] at hODE ⊢
  rw [← hsq] at hODE ⊢
  field_simp [hsne] at hODE ⊢
  ring_nf at hODE ⊢
  exact hODE

/-- Root-conditioned physical scaling wrapper.  This exposes the normalized
coefficient row, actual physical regularity, and exact physical ODE without
adding a source-mode or Fourier hypothesis. -/
theorem exists_mode4MatchedNormalizedPhysicalProlateRow_of_root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    ∃ a : ℕ → ℝ,
      0 < a 0 ∧
      Summable (fun q => |a q|) ∧
      Summable (fun q => (a q) ^ 2) ∧
      HasSum (fun q => (a q) ^ 2 / (4 * (q : ℝ) + 1)) 1 ∧
      ContDiffOn ℝ 2 (mode4PhysicalFerrersSeries mProject a)
        (Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject)) ∧
      ∀ u ∈ Set.Ioo (-Real.sqrt mProject) (Real.sqrt mProject),
        -((mProject : ℝ) - u ^ 2) *
              mode4PhysicalFerrersSecondDerivativeSeries mProject a u +
            2 * u *
              mode4PhysicalFerrersFirstDerivativeSeries mProject a u +
            (2 * Real.pi * Real.sqrt mProject * u) ^ 2 *
              mode4PhysicalFerrersSeries mProject a u =
          (Λ + mode4JacobiG mProject) *
            mode4PhysicalFerrersSeries mProject a u := by
  obtain ⟨S⟩ := exists_mode4FerrersRegularEvenProlateSolution_of_root
    mProject K Λ hm hK hsep hΛ hroot
  exact ⟨S.coefficients, S.coefficient_zero_pos,
    S.coefficients_abs_summable, S.coefficients_sq_summable,
    S.normalized, S.physical_contDiffOn_two_open hm,
    fun u hu => S.physicalProlateDifferentialEquation hm hu⟩

#print axioms Mode4FerrersRegularEvenProlateSolution.physical_contDiffOn_two_open
#print axioms Mode4FerrersRegularEvenProlateSolution.physicalFerrersSeries_hasDerivAt_firstDerivativeSeries
#print axioms Mode4FerrersRegularEvenProlateSolution.physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
#print axioms Mode4FerrersRegularEvenProlateSolution.physicalProlateDifferentialEquation
#print axioms exists_mode4MatchedNormalizedPhysicalProlateRow_of_root

end Q3.RouteB
