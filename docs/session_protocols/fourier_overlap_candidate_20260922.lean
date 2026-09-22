import Mathlib
open MeasureTheory Set
open scoped FourierTransform
noncomputable section
namespace Q3OverlapProbe
private def B : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := -(innerSL ℝ).toLinearMap₁₂
private theorem B_cont : Continuous (fun p : ℝ × ℝ => B p.1 p.2) := by
  change Continuous (fun p : ℝ × ℝ => -(inner ℝ p.1 p.2))
  fun_prop
private theorem B_flip : B.flip = B := by
  ext
  simp [B]
def F (f : ℝ → ℂ) : ℝ → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume B f

theorem F_eq_inverse (f : ℝ → ℂ) : F f = 𝓕⁻ f := by
  funext x
  simp [F, B, VectorFourier.fourierIntegral, Real.fourierInv_eq]

theorem swap (f D : ℝ → ℂ) (hf : Integrable f) (hD : Integrable D) :
    (∫ x, F f x * D x) = ∫ x, f x * F D x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := B) Real.continuous_fourierChar B_cont hf hD
  simpa only [B_flip, smul_eq_mul] using h

theorem product_integrable (f D : ℝ → ℂ) (hf : Integrable f) (hD : Integrable D) :
    Integrable (fun x => F f x * D x) := by
  have hcont : Continuous (F f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar B_cont hf
  apply (hD.norm.const_mul (∫ x, ‖f x‖)).mono'
    (hcont.aestronglyMeasurable.mul hD.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖F f x * D x‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) (norm_nonneg _)

theorem overlap (f D : ℝ → ℂ) (s : Set ℝ) (χ : ℂ)
    (hs : MeasurableSet s) (hf : Integrable f) (hD : Integrable D)
    (hfixed : F D = D)
    (heigen : ∀ x ∈ s, F f x = χ * f x)
    (hsupp : ∀ x ∉ s, f x = 0) :
    (1-χ) * (∫ x, f x * D x) = ∫ x in sᶜ, F f x * D x := by
  have hsplit := integral_add_compl hs (product_integrable f D hf hD)
  have hswap := swap f D hf hD
  rw [hfixed] at hswap
  have hin : (∫ x in s, F f x * D x) = χ * (∫ x, f x * D x) := by
    calc
      (∫ x in s, F f x * D x) = ∫ x in s, χ * (f x * D x) := by
        apply setIntegral_congr_fun hs
        intro x hx
        change F f x * D x = χ * (f x * D x)
        rw [heigen x hx, mul_assoc]
      _ = χ * (∫ x in s, f x * D x) := integral_const_mul _ _
      _ = χ * (∫ x, f x * D x) := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hsupp x hx])]
  rw [hin, hswap] at hsplit
  linear_combination -hsplit

theorem overlap_bound (f D : ℝ → ℂ) (s : Set ℝ) (χ : ℂ)
    (hs : MeasurableSet s) (hf : Integrable f) (hD : Integrable D)
    (hfixed : F D = D)
    (heigen : ∀ x ∈ s, F f x = χ * f x)
    (hsupp : ∀ x ∉ s, f x = 0) :
    ‖1-χ‖ * ‖∫ x, f x * D x‖ ≤
      (∫ x, ‖f x‖) * (∫ x in sᶜ, ‖D x‖) := by
  rw [← norm_mul, overlap f D s χ hs hf hD hfixed heigen hsupp]
  calc
    ‖∫ x in sᶜ, F f x * D x‖ ≤ ∫ x in sᶜ, ‖F f x * D x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in sᶜ, (∫ y, ‖f y‖) * ‖D x‖ := by
      apply integral_mono_ae
        ((product_integrable f D hf hD).norm.restrict)
        ((hD.norm.const_mul _).restrict)
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _
#print axioms overlap
#print axioms overlap_bound

theorem exterior_moment_bound (D : ℝ → ℂ) (lam : ℝ) (hlam : 0 < lam)
    (hD : Integrable D) (hM : Integrable (fun x : ℝ => x^2 * ‖D x‖)) :
    (∫ x in (Icc (-lam) lam)ᶜ, ‖D x‖) ≤ (∫ x : ℝ, x^2 * ‖D x‖) / lam^2 := by
  have hlam2 : 0 < lam^2 := sq_pos_of_pos hlam
  apply (le_div_iff₀ hlam2).mpr
  rw [← integral_mul_const]
  calc
    (∫ x in (Icc (-lam) lam)ᶜ, ‖D x‖ * lam^2) ≤
        ∫ x in (Icc (-lam) lam)ᶜ, x^2 * ‖D x‖ := by
      apply setIntegral_mono_on (hD.norm.mul_const _).integrableOn hM.integrableOn
        measurableSet_Icc.compl
      intro x hx
      have hx' : x < -lam ∨ lam < x := by simpa only [mem_compl_iff, mem_Icc, not_and_or, not_le] using hx
      have hs : lam^2 ≤ x^2 := by rcases hx' with h | h <;> nlinarith
      nlinarith [norm_nonneg (D x)]
    _ ≤ ∫ x : ℝ, x^2 * ‖D x‖ := by
      exact setIntegral_le_integral hM (Filter.Eventually.of_forall (fun x => by positivity))
#print axioms exterior_moment_bound

theorem chi_bound_of_overlap_floor (f D : ℝ → ℂ) (lam J : ℝ) (χ : ℂ)
    (hlam : 0 < lam) (hJ : 0 < J)
    (hf : Integrable f) (hD : Integrable D)
    (hM : Integrable (fun x : ℝ => x^2 * ‖D x‖))
    (hfixed : F D = D)
    (heigen : ∀ x ∈ Icc (-lam) lam, F f x = χ * f x)
    (hsupp : ∀ x ∉ Icc (-lam) lam, f x = 0)
    (hfloor : J/2 ≤ ‖∫ x, f x * D x‖) :
    ‖1-χ‖ ≤ (2*(∫ x, ‖f x‖)*(∫ x : ℝ, x^2*‖D x‖)/J)/lam^2 := by
  have hb := overlap_bound f D (Icc (-lam) lam) χ measurableSet_Icc hf hD hfixed heigen hsupp
  have ht := exterior_moment_bound D lam hlam hD hM
  have hL : 0 ≤ ∫ x, ‖f x‖ := integral_nonneg (fun x => norm_nonneg _)
  have ha := mul_le_mul_of_nonneg_left hfloor (norm_nonneg (1-χ))
  have hc := mul_le_mul_of_nonneg_left ht hL
  have hx : ‖1-χ‖*(J/2) ≤ (∫ x, ‖f x‖)*((∫ x : ℝ, x^2*‖D x‖)/lam^2) :=
    ha.trans (hb.trans hc)
  rw [← mul_div_assoc (∫ x, ‖f x‖) (∫ x : ℝ, x^2*‖D x‖) (lam^2)] at hx
  have hy := (le_div_iff₀ (sq_pos_of_pos hlam)).mp hx
  apply (le_div_iff₀ (sq_pos_of_pos hlam)).mpr
  apply (le_div_iff₀ hJ).mpr
  nlinarith
#print axioms chi_bound_of_overlap_floor
end Q3OverlapProbe


