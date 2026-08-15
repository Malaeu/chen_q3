import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalNormalizedZeroExtension
import Q3.Proofs.RouteB.ProlateActualModeSourceLock

/-!
# Normalized Ferrers zero-count transport

This file is source-free plumbing for Goal 058 G3.  It identifies the interior
zero set of the normalized physical zero extension with the scaled image of
the dimensionless Ferrers zero set.  Consequently, normalization and zero
extension cannot create endpoint or exterior zeros in `prolateInteriorZeros`.

The final helper records uniqueness of a real restricted finite-Fourier
scalar whenever the common eigenfunction is nonzero at one point.  No
dimensionless nodal count, scalar positivity, scalar ordering, G3 closure,
Route B promotion, or RH claim is proved here.
-/

open Set

noncomputable section

namespace Q3.RouteB

theorem normalizedPhysicalMode_interiorZeros_eq_image
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    D0Pstar.prolateInteriorZeros (Real.sqrt mProject)
        S.normalizedPhysicalMode =
      (fun t : ℝ ↦ Real.sqrt mProject * t) ''
        {t : ℝ | t ∈ Ioo (-1 : ℝ) 1 ∧
          mode4FerrersSeries S.coefficients t = 0} := by
  have hs : 0 < Real.sqrt (mProject : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hs0 : Real.sqrt (mProject : ℝ) ≠ 0 := hs.ne'
  ext x
  constructor
  · rintro ⟨hx, hzero⟩
    let t : ℝ := x / Real.sqrt mProject
    have ht : t ∈ Ioo (-1 : ℝ) 1 := by
      dsimp only [t]
      constructor
      · rw [lt_div_iff₀ hs]
        simpa using hx.1
      · exact (div_lt_one hs).2 hx.2
    have hxClosed : x ∈ Icc (-Real.sqrt mProject) (Real.sqrt mProject) :=
      ⟨hx.1.le, hx.2.le⟩
    have hnorm : (S.physicalL2Normalization : ℂ) ≠ 0 := by
      exact_mod_cast (S.physicalL2Normalization_pos hm).ne'
    have hseries : mode4FerrersSeries S.coefficients t = 0 := by
      have hc :
          (mode4PhysicalFerrersSeries mProject S.coefficients x : ℂ) = 0 := by
        rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
          Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
          indicator_of_mem hxClosed] at hzero
        exact (div_eq_zero_iff.mp hzero).resolve_right hnorm
      exact_mod_cast hc
    refine ⟨t, ⟨ht, hseries⟩, ?_⟩
    dsimp only [t]
    field_simp
  · rintro ⟨t, ⟨ht, hzero⟩, rfl⟩
    have hx : Real.sqrt mProject * t ∈
        Ioo (-Real.sqrt mProject) (Real.sqrt mProject) := by
      constructor
      · nlinarith [ht.1]
      · nlinarith [ht.2]
    refine ⟨hx, ?_⟩
    have hxClosed : Real.sqrt mProject * t ∈
        Icc (-Real.sqrt mProject) (Real.sqrt mProject) := ⟨hx.1.le, hx.2.le⟩
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      indicator_of_mem hxClosed]
    have hscale :
        Real.sqrt mProject * t / Real.sqrt mProject = t := by
      field_simp
    rw [mode4PhysicalFerrersSeriesComplex, mode4PhysicalFerrersSeries,
      hscale, hzero]
    norm_num

theorem normalizedPhysicalMode_interiorZeros_ncard_eq
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    (D0Pstar.prolateInteriorZeros (Real.sqrt mProject)
        S.normalizedPhysicalMode).ncard =
      {t : ℝ | t ∈ Ioo (-1 : ℝ) 1 ∧
        mode4FerrersSeries S.coefficients t = 0}.ncard := by
  rw [normalizedPhysicalMode_interiorZeros_eq_image S hm]
  apply Set.ncard_image_of_injective
  intro a b hab
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne' hab

theorem normalizedPhysicalMode_zero_ne
    {mProject K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) :
    S.normalizedPhysicalMode 0 ≠ 0 := by
  have hzeroMem : (0 : ℝ) ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
    have hs := Real.sqrt_nonneg (mProject : ℝ)
    constructor <;> linarith
  rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
    Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
    indicator_of_mem hzeroMem, mode4PhysicalFerrersSeriesComplex,
    mode4PhysicalFerrersSeries]
  have hs0 : Real.sqrt (mProject : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by positivity)).ne'
  have hn0 : (S.physicalL2Normalization : ℂ) ≠ 0 := by
    exact_mod_cast (S.physicalL2Normalization_pos hm).ne'
  rw [zero_div]
  exact div_ne_zero (by exact_mod_cast S.center_value_ne_zero) hn0

theorem finiteFourier_real_scalar_unique_at
    {lambda chi psi : ℝ} {f : ℝ → ℂ} {x : ℝ}
    (hfx : f x ≠ 0)
    (hchi : D0Pstar.finiteFourierAction lambda f x = (chi : ℂ) * f x)
    (hpsi : D0Pstar.finiteFourierAction lambda f x = (psi : ℂ) * f x) :
    chi = psi := by
  have hmul : (chi : ℂ) * f x = (psi : ℂ) * f x := hchi.symm.trans hpsi
  have hcast : (chi : ℂ) = (psi : ℂ) := mul_right_cancel₀ hfx hmul
  exact_mod_cast hcast

#print axioms normalizedPhysicalMode_interiorZeros_eq_image
#print axioms normalizedPhysicalMode_interiorZeros_ncard_eq
#print axioms normalizedPhysicalMode_zero_ne
#print axioms finiteFourier_real_scalar_unique_at

end Q3.RouteB
