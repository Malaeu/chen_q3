import Mathlib
import Q3.Proofs.RouteB.ProlateSourceRegularity
import Q3.Proofs.RouteB.G6N1CenterAnchorScalarLock
import Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
import Q3.Proofs.RouteB.G6N1SelectedFerrersW5RateAssembly
open MeasureTheory Set
open scoped FourierTransform ContDiff
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

theorem source_l1_of_window_error (f D : ℝ → ℂ) (lam ε : ℝ)
    (hlam : 0 ≤ lam) (hf : Integrable f) (hD : Integrable D)
    (hsupp : ∀ x ∉ Icc (-lam) lam, f x = 0)
    (herr : ∀ x ∈ Icc (-lam) lam, ‖f x-D x‖ ≤ ε) :
    (∫ x, ‖f x‖) ≤ (∫ x, ‖D x‖)+2*lam*ε := by
  have hc : IntegrableOn (fun _ : ℝ => ε) (Icc (-lam) lam) := integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsize : (∫ _ : ℝ in Icc (-lam) lam, ε) = 2*lam*ε := by
    rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (by linarith : 0 ≤ lam - -lam)]
    simp only [smul_eq_mul]
    ring
  calc
    (∫ x, ‖f x‖) = ∫ x in Icc (-lam) lam, ‖f x‖ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp [hsupp x hx]
    _ ≤ ∫ x in Icc (-lam) lam, (‖D x‖+ε) := by
      apply setIntegral_mono_on hf.norm.integrableOn (hD.norm.integrableOn.add hc) measurableSet_Icc
      intro x hx
      change ‖f x‖ ≤ ‖D x‖ + ε
      have he := herr x hx
      have ht := norm_sub_norm_le (f x) (D x)
      linarith
    _ = (∫ x in Icc (-lam) lam, ‖D x‖)+2*lam*ε := by
      rw [integral_add hD.norm.integrableOn hc, hsize]
    _ ≤ _ := by
      have h := setIntegral_le_integral (s := Icc (-lam) lam) hD.norm
        (Filter.Eventually.of_forall (fun x => norm_nonneg _))
      linarith
#print axioms source_l1_of_window_error

theorem source_l1_uniform (f D : ℝ → ℂ) (lam C : ℝ)
    (hlam : 1 ≤ lam) (hC : 0 ≤ C) (hf : Integrable f) (hD : Integrable D)
    (hsupp : ∀ x ∉ Icc (-lam) lam, f x = 0)
    (herr : ∀ x ∈ Icc (-lam) lam, ‖f x-D x‖ ≤ C/lam^2) :
    (∫ x, ‖f x‖) ≤ (∫ x, ‖D x‖)+2*C := by
  have hp : 0 < lam := by linarith
  have h := source_l1_of_window_error f D lam (C/lam^2) hp.le hf hD hsupp herr
  have hb : 2*lam*(C/lam^2) ≤ 2*C := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    have hg := mul_le_mul_of_nonneg_left (show lam ≤ lam^2 by nlinarith) hC
    nlinarith
  linarith
#print axioms source_l1_uniform

theorem source_product_integrable (f D : ℝ → ℂ) (lam ε : ℝ)
    (hε : 0 ≤ ε) (hf : Integrable f) (hD : Integrable D)
    (hDD : Integrable (fun x => D x * D x))
    (hsupp : ∀ x ∉ Icc (-lam) lam, f x = 0)
    (herr : ∀ x ∈ Icc (-lam) lam, ‖f x-D x‖ ≤ ε) :
    Integrable (fun x => f x * D x) := by
  apply (hDD.norm.add (hD.norm.const_mul ε)).mono'
    (hf.aestronglyMeasurable.mul hD.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖f x * D x‖ ≤ ‖D x * D x‖+ε*‖D x‖
  by_cases hx : x ∈ Icc (-lam) lam
  · have h1 := herr x hx
    have h2 := norm_sub_norm_le (f x) (D x)
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg (D x)]
  · simp only [hsupp x hx, zero_mul, norm_zero]
    positivity

theorem overlap_error_bound (f D : ℝ → ℂ) (lam ε : ℝ)
    (hlam : 0 < lam) (hε : 0 ≤ ε) (hf : Integrable f) (hD : Integrable D)
    (hDD : Integrable (fun x => D x * D x))
    (hQ : Integrable (fun x : ℝ => x^2 * ‖D x * D x‖))
    (hsupp : ∀ x ∉ Icc (-lam) lam, f x = 0)
    (herr : ∀ x ∈ Icc (-lam) lam, ‖f x-D x‖ ≤ ε) :
    ‖(∫ x, f x*D x)-(∫ x, D x*D x)‖ ≤
      ε*(∫ x, ‖D x‖)+(∫ x : ℝ, x^2*‖D x*D x‖)/lam^2 := by
  have hp := source_product_integrable f D lam ε hε hf hD hDD hsupp herr
  have hd := hp.sub hDD
  have hi : ‖∫ x in Icc (-lam) lam, (f x*D x-D x*D x)‖ ≤ ε*(∫ x, ‖D x‖) := by
    calc
      _ ≤ ∫ x in Icc (-lam) lam, ‖f x*D x-D x*D x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in Icc (-lam) lam, ε*‖D x‖ := by
        apply setIntegral_mono_on hd.norm.integrableOn
          (hD.norm.const_mul ε).integrableOn measurableSet_Icc
        intro x hx
        change ‖f x*D x-D x*D x‖ ≤ ε*‖D x‖
        rw [← sub_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (herr x hx) (norm_nonneg _)
      _ = ε*(∫ x in Icc (-lam) lam, ‖D x‖) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hD.norm
        (Filter.Eventually.of_forall (fun x => norm_nonneg _))) hε
  have ho : ‖∫ x in (Icc (-lam) lam)ᶜ, (f x*D x-D x*D x)‖ ≤
      (∫ x : ℝ, x^2*‖D x*D x‖)/lam^2 := by
    have heq : (∫ x in (Icc (-lam) lam)ᶜ, (f x*D x-D x*D x)) =
        -(∫ x in (Icc (-lam) lam)ᶜ, D x*D x) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Icc.compl
      intro x hx
      simp [hsupp x hx]
    rw [heq, norm_neg]
    exact (norm_integral_le_integral_norm _).trans
      (exterior_moment_bound (fun x => D x*D x) lam hlam hDD hQ)
  have hsplit := integral_add_compl (s := Icc (-lam) lam) (f := fun x => f x*D x-D x*D x) measurableSet_Icc hd
  rw [← integral_sub hp hDD, ← hsplit]
  exact (norm_add_le _ _).trans (add_le_add hi ho)
#print axioms overlap_error_bound

theorem chi_bound_from_mode_error (f D : ℝ → ℂ) (lam C J : ℝ) (χ : ℂ)
    (hlam : 1 ≤ lam) (hC : 0 ≤ C) (hJ : 0 < J)
    (hJeq : J = ‖∫ x, D x*D x‖)
    (hf : Integrable f) (hD : Integrable D)
    (hDD : Integrable (fun x => D x*D x))
    (hM : Integrable (fun x : ℝ => x^2*‖D x‖))
    (hQ : Integrable (fun x : ℝ => x^2*‖D x*D x‖))
    (hfixed : F D = D)
    (heigen : ∀ x ∈ Icc (-lam) lam, F f x = χ*f x)
    (hsupp : ∀ x ∉ Icc (-lam) lam, f x = 0)
    (herr : ∀ x ∈ Icc (-lam) lam, ‖f x-D x‖ ≤ C/lam^2)
    (hlarge : 2*(C*(∫ x, ‖D x‖)+(∫ x : ℝ, x^2*‖D x*D x‖)) ≤ J*lam^2) :
    ‖1-χ‖ ≤ (2*((∫ x, ‖D x‖)+2*C)*(∫ x : ℝ, x^2*‖D x‖)/J)/lam^2 := by
  have hp : 0 < lam := by linarith
  have he := overlap_error_bound f D lam (C/lam^2) hp (by positivity) hf hD hDD hQ hsupp herr
  have hsmall : (C/lam^2)*(∫ x, ‖D x‖)+(∫ x : ℝ, x^2*‖D x*D x‖)/lam^2 ≤ J/2 := by
    rw [div_mul_eq_mul_div, ← add_div]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  have hr := norm_sub_norm_le (∫ x, D x*D x) (∫ x, f x*D x)
  rw [norm_sub_rev, ← hJeq] at hr
  have hfloor : J/2 ≤ ‖∫ x, f x*D x‖ := by linarith [he.trans hsmall]
  have hb := chi_bound_of_overlap_floor f D lam J χ hp hJ hf hD hM hfixed heigen hsupp hfloor
  have hL := source_l1_uniform f D lam C hlam hC hf hD hsupp herr
  have hM0 : 0 ≤ ∫ x : ℝ, x^2*‖D x‖ := integral_nonneg (fun x => by positivity)
  apply hb.trans
  gcongr
#print axioms chi_bound_from_mode_error

theorem F_eq_finiteFourierAction (f : ℝ → ℂ) (lam : ℝ)
    (hsupp : ∀ x ∉ Icc (-lam) lam, f x = 0) (x : ℝ) :
    F f x = Q3.RouteB.D0Pstar.finiteFourierAction lam f x := by
  have heq : F f x = ∫ y : ℝ, Q3.RouteB.D0Pstar.finiteFourierKernel x y * f y := by
    unfold F VectorFourier.fourierIntegral B
    simp only [LinearMap.neg_apply, ContinuousLinearMap.toLinearMap₁₂_apply,
      innerSL_apply_apply, neg_neg, Circle.smul_def, Real.fourierChar_apply,
      smul_eq_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    congr 1
    unfold Q3.RouteB.D0Pstar.finiteFourierKernel
    congr 1
    have hinner : inner ℝ y x = x*y := rfl
    rw [hinner]
    push_cast
    ring
  rw [heq]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  simp [hsupp y hy]
#print axioms F_eq_finiteFourierAction

theorem scaled_finite_eigen (f : ℝ → ℂ) (lam : ℝ) (a χ : ℂ)
    (hsupp : ∀ x ∉ Icc (-lam) lam, f x = 0)
    (heigen : ∀ x ∈ Icc (-lam) lam,
      Q3.RouteB.D0Pstar.finiteFourierAction lam f x = χ*f x) :
    ∀ x ∈ Icc (-lam) lam, F (fun y => a*f y) x = χ*(a*f x) := by
  intro x hx
  rw [F_eq_finiteFourierAction _ lam (fun y hy => by simp [hsupp y hy])]
  have hs : Q3.RouteB.D0Pstar.finiteFourierAction lam (fun y => a*f y) x =
      a * Q3.RouteB.D0Pstar.finiteFourierAction lam f x := by
    unfold Q3.RouteB.D0Pstar.finiteFourierAction
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [hs, heigen x hx]
  ring

open Q3.RouteB.D0Pstar in
theorem selected_anchored_eigen (k : ℕ) :
    (∀ x ∈ Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda,
      F (fun y => centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 y) x =
        ((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
          (centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 x)) ∧
    (∀ x ∈ Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda,
      F (fun y => centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 y) x =
        ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
          (centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 x)) := by
  obtain ⟨_, _, _, _, _, _, _, h0, h4, _⟩ := selectedFerrersPreAnchorPair_spec k
  constructor
  · apply scaled_finite_eigen _ _ _ _ _ h0
    intro x hx
    by_contra hne
    exact hx ((selectedFerrersPreAnchorPair k).h0_support hne)
  · apply scaled_finite_eigen _ _ _ _ _ h4
    intro x hx
    by_contra hne
    exact hx ((selectedFerrersPreAnchorPair k).h4_support hne)
#print axioms selected_anchored_eigen
open Q3.RouteB Q3.RouteB.D0Pstar

def cylinderTarget (n : ℕ) (x : ℝ) : ℂ :=
  (parabolicCylinderD n (projectCylinderArgument x) : ℂ)

theorem target_zero_gaussian (x : ℝ) :
    cylinderTarget 0 x = Complex.exp (-Real.pi * (x : ℂ)^2) := by
  unfold cylinderTarget
  rw [parabolicCylinderD_zero_projectArgument, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem target_zero_fixed : F (cylinderTarget 0) = cylinderTarget 0 := by
  have hfourier : 𝓕 (cylinderTarget 0) = cylinderTarget 0 := by
    simp_rw [funext target_zero_gaussian]
    simpa using (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num))
  rw [F_eq_inverse]
  funext x
  rw [Real.fourierInv_eq_fourier_neg, hfourier]
  simp [cylinderTarget, parabolicCylinderD_zero_projectArgument]

theorem target_zero_moment (n : ℕ) :
    Integrable (fun x : ℝ => x^n • cylinderTarget 0 x) := by
  have hr : Integrable (fun x : ℝ => x^n * Real.exp (-Real.pi*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos
        (show (-1 : ℝ) < (n : ℝ) by
          exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)))
  have hc : Integrable (fun x : ℝ => ((x^n * Real.exp (-Real.pi*x^2) : ℝ) : ℂ)) := hr.ofReal
  convert hc using 1
  funext x
  simp [cylinderTarget, parabolicCylinderD_zero_projectArgument,
    Complex.real_smul]

theorem target_four_decomposition : cylinderTarget 4 =
    fun x => (16 : ℂ) * explicitCCMLimitH x + 3 * cylinderTarget 0 x := by
  funext x
  rw [target_zero_gaussian]
  unfold cylinderTarget explicitCCMLimitH
  rw [parabolicCylinderD_four_projectArgument]
  push_cast
  ring

theorem ccm_integrable : Integrable explicitCCMLimitH := by
  have h := ((target_zero_moment 4).const_mul ((Real.pi : ℂ)^2)).sub
    ((target_zero_moment 2).const_mul (3*(Real.pi : ℂ)/2))
  convert h using 1
  funext x
  simp only [Pi.sub_apply, Complex.real_smul]
  rw [target_zero_gaussian]
  unfold explicitCCMLimitH
  push_cast
  ring

theorem target_four_fixed : F (cylinderTarget 4) = cylinderTarget 4 := by
  have h0 : Integrable (cylinderTarget 0) := by
    simpa using target_zero_moment 0
  have hsum : cylinderTarget 4 =
      (16 : ℂ) • explicitCCMLimitH + (3 : ℂ) • cylinderTarget 0 := by
    exact target_four_decomposition
  have h0f : 𝓕 (cylinderTarget 0) = cylinderTarget 0 := by
    simp_rw [funext target_zero_gaussian]
    simpa using (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num))
  have hadd {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
      𝓕 (f+g) = 𝓕 f + 𝓕 g :=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner hf hg
  have hsmul (c : ℂ) (f : ℝ → ℂ) : 𝓕 (c • f) = c • 𝓕 f :=
    VectorFourier.fourierIntegral_const_smul _ _ _ _ _
  have h4f : 𝓕 (cylinderTarget 4) = cylinderTarget 4 := by
    rw [hsum, hadd (ccm_integrable.smul (16 : ℂ)) (h0.smul (3 : ℂ))]
    rw [hsmul, hsmul, fourier_explicitCCMLimitH, h0f]
  rw [F_eq_inverse]
  funext x
  rw [Real.fourierInv_eq_fourier_neg, h4f]
  simp [cylinderTarget, parabolicCylinderD_four_projectArgument]
  <;> ring

#print axioms target_four_fixed
#print axioms target_zero_fixed
#print axioms target_zero_moment
theorem target_four_moment (n : ℕ) :
    Integrable (fun x : ℝ => x^n • cylinderTarget 4 x) := by
  have h := (((target_zero_moment (n+4)).const_mul (16*(Real.pi : ℂ)^2)).sub
    ((target_zero_moment (n+2)).const_mul (24*(Real.pi : ℂ)))).add
    ((target_zero_moment n).const_mul 3)
  convert h using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Complex.real_smul]
  unfold cylinderTarget
  rw [parabolicCylinderD_four_projectArgument, parabolicCylinderD_zero_projectArgument]
  push_cast
  ring

theorem target_four_weighted_norm :
    Integrable (fun x : ℝ => x^2 * ‖cylinderTarget 4 x‖) := by
  have h := (target_four_moment 2).norm
  simpa [norm_smul, Real.norm_eq_abs, abs_sq] using h

#print axioms target_four_moment
#print axioms target_four_weighted_norm
theorem double_gaussian_moment (n : ℕ) :
    Integrable (fun x : ℝ => x^n * Real.exp (-(2*Real.pi)*x^2)) := by
  simpa only [Real.rpow_natCast] using
    (integrable_rpow_mul_exp_neg_mul_sq (mul_pos (by norm_num) Real.pi_pos)
      (show (-1 : ℝ) < (n : ℝ) by
        exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)))

theorem target_four_square_moment (n : ℕ) :
    Integrable (fun x : ℝ => x^n *
      (parabolicCylinderD 4 (projectCylinderArgument x))^2) := by
  have h := (((((double_gaussian_moment (n+8)).const_mul (256*Real.pi^4)).sub
    ((double_gaussian_moment (n+6)).const_mul (768*Real.pi^3))).add
    ((double_gaussian_moment (n+4)).const_mul (672*Real.pi^2))).sub
    ((double_gaussian_moment (n+2)).const_mul (144*Real.pi))).add
    ((double_gaussian_moment n).const_mul 9)
  convert h using 1
  funext x
  rw [parabolicCylinderD_four_projectArgument, mul_pow]
  rw [show (Real.exp (-Real.pi*x^2))^2 = Real.exp (-(2*Real.pi)*x^2) by
    rw [sq, ← Real.exp_add]; congr 1; ring]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem target_four_square_weighted_norm :
    Integrable (fun x : ℝ => x^2 * ‖cylinderTarget 4 x * cylinderTarget 4 x‖) := by
  convert target_four_square_moment 2 using 1
  funext x
  simp [cylinderTarget, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, ← sq, abs_sq]

#print axioms target_four_square_moment
#print axioms target_four_square_weighted_norm
theorem target_zero_square_moment (n : ℕ) :
    Integrable (fun x : ℝ => x^n *
      (parabolicCylinderD 0 (projectCylinderArgument x))^2) := by
  convert double_gaussian_moment n using 1
  funext x
  rw [parabolicCylinderD_zero_projectArgument, sq, ← Real.exp_add]
  congr 2
  ring

theorem target_square_positive (n : ℕ) (hn : n = 0 ∨ n = 4) :
    0 < ∫ x : ℝ, (parabolicCylinderD n (projectCylinderArgument x))^2 := by
  have hi : Integrable (fun x : ℝ =>
      (parabolicCylinderD n (projectCylinderArgument x))^2) := by
    rcases hn with rfl | rfl
    · simpa using target_zero_square_moment 0
    · simpa using target_four_square_moment 0
  apply integral_pos_of_integrable_nonneg_nonzero (x := (0 : ℝ)) _ hi
      (fun x => sq_nonneg _) _
  · rcases hn with rfl | rfl
    · simp_rw [parabolicCylinderD_zero_projectArgument]
      fun_prop
    · simp_rw [parabolicCylinderD_four_projectArgument]
      fun_prop
  · rcases hn with rfl | rfl
    · norm_num [parabolicCylinderD_zero_projectArgument]
    · norm_num [parabolicCylinderD_four_projectArgument]

#print axioms target_zero_square_moment
#print axioms target_square_positive
theorem target_analytic_inputs (n : ℕ) (hn : n = 0 ∨ n = 4) :
    Integrable (cylinderTarget n) ∧
    Integrable (fun x => cylinderTarget n x * cylinderTarget n x) ∧
    Integrable (fun x : ℝ => x^2 * ‖cylinderTarget n x‖) ∧
    Integrable (fun x : ℝ => x^2 * ‖cylinderTarget n x * cylinderTarget n x‖) ∧
    0 < ‖∫ x, cylinderTarget n x * cylinderTarget n x‖ := by
  have hm (j : ℕ) : Integrable (fun x : ℝ => x^j • cylinderTarget n x) := by
    rcases hn with rfl | rfl
    · exact target_zero_moment j
    · exact target_four_moment j
  have hq (j : ℕ) : Integrable (fun x : ℝ => x^j *
      (parabolicCylinderD n (projectCylinderArgument x))^2) := by
    rcases hn with rfl | rfl
    · exact target_zero_square_moment j
    · exact target_four_square_moment j
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using hm 0
  · have hr : Integrable (fun x : ℝ =>
        (parabolicCylinderD n (projectCylinderArgument x))^2) := by simpa using hq 0
    have hc : Integrable (fun x : ℝ =>
        (((parabolicCylinderD n (projectCylinderArgument x))^2 : ℝ) : ℂ)) := hr.ofReal
    simpa [cylinderTarget, sq] using hc
  · simpa [norm_smul, Real.norm_eq_abs] using (hm 2).norm
  · convert hq 2 using 1
    funext x
    simp [cylinderTarget, ← Complex.ofReal_mul, ← sq]
  · have heq : (∫ x, cylinderTarget n x * cylinderTarget n x) =
        (((∫ x : ℝ, (parabolicCylinderD n (projectCylinderArgument x))^2) : ℝ) : ℂ) := by
      have ht := integral_complex_ofReal (μ := volume)
        (f := fun x : ℝ => (parabolicCylinderD n (projectCylinderArgument x))^2)
      simpa only [cylinderTarget, sq, Complex.ofReal_mul] using ht
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (target_square_positive n hn)]
    exact target_square_positive n hn

#print axioms target_analytic_inputs
theorem selected_anchored_integrable (k : ℕ) :
    Integrable (fun y => centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 y) ∧
    Integrable (fun y => centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 y) := by
  exact ⟨(selectedFerrersPreAnchorPair k).h0_integrable.const_mul _,
    (selectedFerrersPreAnchorPair k).h4_integrable.const_mul _⟩

#print axioms selected_anchored_integrable
theorem scheduled_chi_rate (n : ℕ) (hn : n = 0 ∨ n = 4)
    (f : ℕ → ℝ → ℂ) (χ : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, Integrable (f k))
    (heigen : ∀ k, ∀ x ∈ Icc (-(selectedFerrersPaperLambda k))
        (selectedFerrersPaperLambda k), F (f k) x = χ k * f k x)
    (hsupp : ∀ k, ∀ x ∉ Icc (-(selectedFerrersPaperLambda k))
        (selectedFerrersPaperLambda k), f k x = 0)
    (herr : ∀ᶠ k in Filter.atTop, ∀ x ∈ Icc (-(selectedFerrersPaperLambda k))
        (selectedFerrersPaperLambda k), ‖f k x-cylinderTarget n x‖ ≤
          C/(selectedFerrersPaperLambda k)^2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k in Filter.atTop,
      ‖1-χ k‖ ≤ A/(selectedFerrersPaperLambda k)^2 := by
  obtain ⟨hD,hDD,hM,hQ,hJ⟩ := target_analytic_inputs n hn
  let D := cylinderTarget n
  let J := ‖∫ x, D x*D x‖
  let L := ∫ x, ‖D x‖
  let M := ∫ x : ℝ, x^2*‖D x‖
  let Q := ∫ x : ℝ, x^2*‖D x*D x‖
  have hJp : 0 < J := hJ
  have hL : 0 ≤ L := integral_nonneg (fun x => norm_nonneg _)
  have hMp : 0 ≤ M := integral_nonneg (fun x => by positivity)
  refine ⟨2*(L+2*C)*M/J, by positivity, ?_⟩
  obtain ⟨K,hK⟩ := exists_nat_ge (2*(C*L+Q)/J)
  filter_upwards [herr, Filter.eventually_ge_atTop K] with k hk hkK
  have hlam : 1 ≤ selectedFerrersPaperLambda k := by
    rw [selectedFerrersPaperLambda,
      show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show 1 ≤ k+2 by omega)
  have hbig : 2*(C*L+Q) ≤ J*(selectedFerrersPaperLambda k)^2 := by
    rw [mul_comm J]
    apply (div_le_iff₀ hJp).mp
    rw [selectedFerrersPaperLambda_sq]
    exact hK.trans (by exact_mod_cast (show K ≤ k+2 by omega))
  have hfixed : F D = D := by
    rcases hn with rfl | rfl
    · exact target_zero_fixed
    · exact target_four_fixed
  exact chi_bound_from_mode_error (f k) D _ C J (χ k) hlam hC hJp rfl
    (hf k) hD hDD hM hQ hfixed (heigen k) (hsupp k) hk hbig

#print axioms scheduled_chi_rate
theorem selected_chi_rate_of_mode_rate
    (C0 C4 : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Icc (-(selectedFerrersPaperLambda k)) (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 x -
          cylinderTarget 0 x‖ ≤ C0 / (selectedFerrersPaperLambda k)^2 ∧
        ‖centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 x -
          cylinderTarget 4 x‖ ≤ C4 / (selectedFerrersPaperLambda k)^2) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ᶠ k in Filter.atTop,
      |1-(selectedFerrersPreAnchorPair k).chi0| ≤ Cχ/(selectedFerrersPaperLambda k)^2 ∧
      |1-(selectedFerrersPreAnchorPair k).chi2| ≤ Cχ/(selectedFerrersPaperLambda k)^2 := by
  have hzero := scheduled_chi_rate 0 (Or.inl rfl)
    (fun k x => centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 x)
    (fun k => ((selectedFerrersPreAnchorPair k).chi0 : ℂ)) C0 hC0
    (fun k => (selected_anchored_integrable k).1)
    (fun k => by simpa only [selectedFerrersPreAnchorPair_lambda_eq_paperLambda] using
      (selected_anchored_eigen k).1)
    (fun k x hx => by
      have hz : (selectedFerrersPreAnchorPair k).h0 x = 0 := by
        by_contra hne
        apply hx
        simpa only [selectedFerrersPreAnchorPair_lambda_eq_paperLambda] using
          (selectedFerrersPreAnchorPair k).h0_support hne
      simp [hz])
    (hmode.mono (fun k hk x hx => (hk x hx).1))
  have hfour := scheduled_chi_rate 4 (Or.inr rfl)
    (fun k x => centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 x)
    (fun k => ((selectedFerrersPreAnchorPair k).chi2 : ℂ)) C4 hC4
    (fun k => (selected_anchored_integrable k).2)
    (fun k => by simpa only [selectedFerrersPreAnchorPair_lambda_eq_paperLambda] using
      (selected_anchored_eigen k).2)
    (fun k x hx => by
      have hz : (selectedFerrersPreAnchorPair k).h4 x = 0 := by
        by_contra hne
        apply hx
        simpa only [selectedFerrersPreAnchorPair_lambda_eq_paperLambda] using
          (selectedFerrersPreAnchorPair k).h4_support hne
      simp [hz])
    (hmode.mono (fun k hk x hx => (hk x hx).2))
  obtain ⟨A,hA,hAr⟩ := hzero
  obtain ⟨B,hB,hBr⟩ := hfour
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  filter_upwards [hAr,hBr] with k hk0 hk4
  have hden : 0 ≤ (selectedFerrersPaperLambda k)^2 := sq_nonneg _
  constructor
  · have hh : |1-(selectedFerrersPreAnchorPair k).chi0| ≤
        A/(selectedFerrersPaperLambda k)^2 := by
      simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hk0
    exact hh.trans (div_le_div_of_nonneg_right (le_max_left _ _) hden)
  · have hh : |1-(selectedFerrersPreAnchorPair k).chi2| ≤
        B/(selectedFerrersPaperLambda k)^2 := by
      simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hk4
    exact hh.trans (div_le_div_of_nonneg_right (le_max_right _ _) hden)

#print axioms selected_chi_rate_of_mode_rate
theorem selected_projection_tail_of_mode_theta
    (S : ProlateCanonicalSourceData)
    (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S)
    (C0 C4 Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    SelectedProjectionTailDecay S := by
  obtain ⟨Cχ,hCχ,hχ⟩ := selected_chi_rate_of_mode_rate C0 C4 hC0 hC4 hmode
  exact selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
    S hFamily C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ

#print axioms selected_projection_tail_of_mode_theta
theorem compact_flux_green
    (a b : ℝ) (f df φ dφ p flux dflux testflux dtestflux : ℝ → ℂ)
    (hf : ContinuousOn f (uIcc a b)) (hφ : ContinuousOn φ (uIcc a b))
    (hflux : ContinuousOn flux (uIcc a b))
    (htest : ContinuousOn testflux (uIcc a b))
    (hdf : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (df x) x)
    (hdφ : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt φ (dφ x) x)
    (hdflux : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt flux (dflux x) x)
    (hdtest : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt testflux (dtestflux x) x)
    (hidf : IntervalIntegrable df volume a b)
    (hidφ : IntervalIntegrable dφ volume a b)
    (hidflux : IntervalIntegrable dflux volume a b)
    (hidtest : IntervalIntegrable dtestflux volume a b)
    (hfluxeq : ∀ x, flux x = p x * df x)
    (htesteq : ∀ x, testflux x = p x * dφ x)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hta : testflux a = 0) (htb : testflux b = 0) :
    (∫ x in a..b, φ x * dflux x) = ∫ x in a..b, f x * dtestflux x := by
  have hleft := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hφ hflux hdφ hdflux hidφ hidflux
  have hright := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hf htest hdf hdtest hidf hidtest
  rw [hφa,hφb] at hleft
  rw [hta,htb] at hright
  simp only [zero_mul,mul_zero,sub_zero,zero_sub] at hleft hright
  rw [hleft,hright]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [hfluxeq,htesteq]
  ring

#print axioms compact_flux_green
theorem target_zero_oscillator (x : ℝ) :
    -deriv (deriv (fun y => parabolicCylinderD 0 (projectCylinderArgument y))) x +
      4*Real.pi^2*x^2 * parabolicCylinderD 0 (projectCylinderArgument x) =
      2*Real.pi * parabolicCylinderD 0 (projectCylinderArgument x) := by
  have heq : (fun y => parabolicCylinderD 0 (projectCylinderArgument y)) = ctW0 := by
    funext y
    simp [parabolicCylinderD_zero_projectArgument, ctW0]
  change -deriv (deriv (fun y => parabolicCylinderD 0 (projectCylinderArgument y))) x +
      4*Real.pi^2*x^2 * (fun y => parabolicCylinderD 0 (projectCylinderArgument y)) x =
      2*Real.pi * (fun y => parabolicCylinderD 0 (projectCylinderArgument y)) x
  rw [heq, show deriv ctW0 = ctW0d from funext (fun y => (ctW0_hasDerivAt' y).deriv),
    (ctW0d_hasDerivAt x).deriv]
  exact ctW0_cylinder_eigenrelation x

theorem target_four_oscillator (x : ℝ) :
    -deriv (deriv (fun y => parabolicCylinderD 4 (projectCylinderArgument y))) x +
      4*Real.pi^2*x^2 * parabolicCylinderD 4 (projectCylinderArgument x) =
      18*Real.pi * parabolicCylinderD 4 (projectCylinderArgument x) := by
  have heq : (fun y => parabolicCylinderD 4 (projectCylinderArgument y)) = ctW4 := by
    funext y
    simp [parabolicCylinderD_four_projectArgument, ctW4]
    ring
  change -deriv (deriv (fun y => parabolicCylinderD 4 (projectCylinderArgument y))) x +
      4*Real.pi^2*x^2 * (fun y => parabolicCylinderD 4 (projectCylinderArgument y)) x =
      18*Real.pi * (fun y => parabolicCylinderD 4 (projectCylinderArgument y)) x
  rw [heq, show deriv ctW4 = ctW4d from funext (fun y => (ctW4_hasDerivAt' y).deriv),
    (ctW4d_hasDerivAt x).deriv]
  exact ctW4_cylinder_eigenrelation x

#print axioms target_zero_oscillator
#print axioms target_four_oscillator
theorem compact_theta_defect_identity
    (a b : ℝ) (m θ e : ℂ) (f D φ ddφ V T : ℝ → ℂ)
    (hf : ContinuousOn f (uIcc a b)) (hD : ContinuousOn D (uIcc a b))
    (hφ : ContinuousOn φ (uIcc a b)) (hddφ : ContinuousOn ddφ (uIcc a b))
    (hV : ContinuousOn V (uIcc a b)) (hT : ContinuousOn T (uIcc a b))
    (hweak : (∫ x in a..b, φ x * ((m*V x-θ)*f x)) =
      ∫ x in a..b, f x*(m*ddφ x-T x))
    (horth : (∫ x in a..b, D x*(-ddφ x+(V x-e)*φ x)) = 0) :
    (θ-e*m)*(∫ x in a..b, f x*φ x) =
      m*(∫ x in a..b, (f x-D x)*(-ddφ x+(V x-e)*φ x)) +
      ∫ x in a..b, f x*T x := by
  have hfp := (hf.mul hφ).intervalIntegrable (μ := volume)
  have hfv := ((hf.mul hV).mul hφ).intervalIntegrable (μ := volume)
  have hfd := (hf.mul hddφ).intervalIntegrable (μ := volume)
  have hft := (hf.mul hT).intervalIntegrable (μ := volume)
  have hA : ContinuousOn (fun x => -ddφ x+(V x-e)*φ x) (uIcc a b) :=
    hddφ.neg.add ((hV.sub continuousOn_const).mul hφ)
  have hfa := (hf.mul hA).intervalIntegrable (μ := volume)
  have hda := (hD.mul hA).intervalIntegrable (μ := volume)
  have hl : (fun x => φ x*((m*V x-θ)*f x)) =
      (fun x => m*(f x*V x*φ x)-θ*(f x*φ x)) := by funext x; ring
  have hr : (fun x => f x*(m*ddφ x-T x)) =
      (fun x => m*(f x*ddφ x)-f x*T x) := by funext x; ring
  rw [hl,hr,intervalIntegral.integral_sub (hfv.const_mul m) (hfp.const_mul θ),
    intervalIntegral.integral_sub (hfd.const_mul m) hft,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hweak
  have herr : (∫ x in a..b, (f x-D x)*(-ddφ x+(V x-e)*φ x)) =
      -(∫ x in a..b, f x*ddφ x)+(∫ x in a..b, f x*V x*φ x)-
        e*(∫ x in a..b, f x*φ x) := by
    have hex : (fun x => (f x-D x)*(-ddφ x+(V x-e)*φ x)) =
        (fun x => f x*(-ddφ x+(V x-e)*φ x)-D x*(-ddφ x+(V x-e)*φ x)) := by
      funext x; ring
    rw [hex,intervalIntegral.integral_sub hfa hda,horth,sub_zero]
    have heq : (fun x => f x*(-ddφ x+(V x-e)*φ x)) =
        (fun x => - (f x*ddφ x) + f x*V x*φ x-e*(f x*φ x)) := by
      funext x; ring
    have hneg : IntervalIntegrable (fun x => -(f x*ddφ x)) volume a b := hfd.neg
    have hsum : IntervalIntegrable (fun x => -(f x*ddφ x)+f x*V x*φ x) volume a b :=
      hneg.add hfv
    rw [heq,intervalIntegral.integral_sub hsum (hfp.const_mul e),
      intervalIntegral.integral_add hneg hfv,intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
  rw [herr]
  linear_combination -hweak

#print axioms compact_theta_defect_identity
theorem theta_defect_bound_from_weak_pairing
    (m θ e J A B : ℝ) (I U V : ℂ)
    (hm : 0 < m) (hJ : 0 < J)
    (hidentity : (((θ-e*m : ℝ) : ℂ))*I = (m:ℂ)*U+V)
    (hfloor : J/2 ≤ ‖I‖) (hU : ‖U‖ ≤ A/m) (hV : ‖V‖ ≤ B) :
    |θ-e*m| ≤ 2*(A+B)/J := by
  have hn : |θ-e*m| *‖I‖ ≤ A+B := calc
    |θ-e*m| *‖I‖ = ‖(((θ-e*m : ℝ) : ℂ))*I‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    _ = ‖(m:ℂ)*U+V‖ := congrArg norm hidentity
    _ ≤ ‖(m:ℂ)*U‖+‖V‖ := norm_add_le _ _
    _ = m*‖U‖+‖V‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm]
    _ ≤ m*(A/m)+B := add_le_add (mul_le_mul_of_nonneg_left hU hm.le) hV
    _ = A+B := by field_simp
  apply (le_div_iff₀ hJ).mpr
  have hh := mul_le_mul_of_nonneg_left hfloor (abs_nonneg (θ-e*m))
  nlinarith

#print axioms theta_defect_bound_from_weak_pairing
def compactTest (n : ℕ) (x : ℝ) : ℝ :=
  (1-x^2)^3 * parabolicCylinderD n (projectCylinderArgument x)

theorem compactTest_contDiff (n : ℕ) (hn : n = 0 ∨ n = 4) :
    ContDiff ℝ ∞ (compactTest n) := by
  rcases hn with rfl | rfl
  · unfold compactTest
    simp_rw [parabolicCylinderD_zero_projectArgument]
    fun_prop
  · unfold compactTest
    simp_rw [parabolicCylinderD_four_projectArgument]
    fun_prop

theorem compactTest_hasDerivAt (n : ℕ) (hn : n = 0 ∨ n = 4) (x : ℝ) :
    HasDerivAt (compactTest n)
      ((-6*x*(1-x^2)^2)*parabolicCylinderD n (projectCylinderArgument x) +
        (1-x^2)^3 * deriv (fun y => parabolicCylinderD n (projectCylinderArgument y)) x) x := by
  have hw : HasDerivAt (fun y : ℝ => (1-y^2)^3) (-6*x*(1-x^2)^2) x := by
    convert (((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).pow 2)).pow 3) using 1 <;> simp only [Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring
  have hd : Differentiable ℝ (fun y => parabolicCylinderD n (projectCylinderArgument y)) := by
    rcases hn with rfl | rfl
    · simp_rw [parabolicCylinderD_zero_projectArgument]
      fun_prop
    · simp_rw [parabolicCylinderD_four_projectArgument]
      fun_prop
  exact hw.mul (hd x).hasDerivAt

theorem compactTest_boundary (n : ℕ) (hn : n = 0 ∨ n = 4) :
    compactTest n (-1) = 0 ∧ compactTest n 1 = 0 ∧
    deriv (compactTest n) (-1) = 0 ∧ deriv (compactTest n) 1 = 0 := by
  rw [(compactTest_hasDerivAt n hn (-1)).deriv, (compactTest_hasDerivAt n hn 1).deriv]
  norm_num [compactTest]

theorem compactTest_overlap_positive (n : ℕ) (hn : n = 0 ∨ n = 4) :
    0 < ∫ x in (-1:ℝ)..1,
      parabolicCylinderD n (projectCylinderArgument x)*compactTest n x := by
  have hc : Continuous (fun x => parabolicCylinderD n (projectCylinderArgument x)) := by
    rcases hn with rfl | rfl
    · simp_rw [parabolicCylinderD_zero_projectArgument]
      fun_prop
    · simp_rw [parabolicCylinderD_four_projectArgument]
      fun_prop
  have hh := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0:ℝ)) (g := fun x =>
      parabolicCylinderD n (projectCylinderArgument x)*compactTest n x)
    (a := -1) (b := 1) (by norm_num) continuousOn_const
    (hc.mul (compactTest_contDiff n hn).continuous).continuousOn
    (by
      intro x hx
      have hw : 0 ≤ 1-x^2 := by nlinarith [hx.1, hx.2]
      dsimp only
      unfold compactTest
      nlinarith [mul_nonneg (pow_nonneg hw 3)
        (sq_nonneg (parabolicCylinderD n (projectCylinderArgument x)))])
    (by
      refine ⟨0, by norm_num, ?_⟩
      rcases hn with rfl | rfl
      · norm_num [compactTest, parabolicCylinderD_zero_projectArgument]
      · norm_num [compactTest, parabolicCylinderD_four_projectArgument])
  simpa using hh

#print axioms compactTest_contDiff
#print axioms compactTest_boundary
#print axioms compactTest_overlap_positive
theorem oscillator_test_orthogonality
    (a b e : ℝ) (D φ V : ℝ → ℝ)
    (hD : ContDiff ℝ ∞ D) (hφ : ContDiff ℝ ∞ φ)
    (hode : ∀ x, -deriv (deriv D) x+V x*D x=e*D x)
    (hφa : φ a=0) (hφb : φ b=0)
    (hda : deriv φ a=0) (hdb : deriv φ b=0) :
    (∫ x in a..b, D x*(-deriv (deriv φ) x+(V x-e)*φ x)) = 0 := by
  have hDd := (contDiff_infty_iff_deriv.mp hD).2
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hDdd := (contDiff_infty_iff_deriv.mp hDd).2
  have hφdd := (contDiff_infty_iff_deriv.mp hφd).2
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hφ.continuous.continuousOn hDd.continuous.continuousOn
    (fun x _ => ((contDiff_infty_iff_deriv.mp hφ).1 x).hasDerivAt)
    (fun x _ => ((contDiff_infty_iff_deriv.mp hDd).1 x).hasDerivAt)
    (hφd.continuous.intervalIntegrable (μ := volume) a b)
    (hDdd.continuous.intervalIntegrable (μ := volume) a b)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hD.continuous.continuousOn hφd.continuous.continuousOn
    (fun x _ => ((contDiff_infty_iff_deriv.mp hD).1 x).hasDerivAt)
    (fun x _ => ((contDiff_infty_iff_deriv.mp hφd).1 x).hasDerivAt)
    (hDd.continuous.intervalIntegrable (μ := volume) a b)
    (hφdd.continuous.intervalIntegrable (μ := volume) a b)
  rw [hφa,hφb] at h1
  rw [hda,hdb] at h2
  simp only [zero_mul,mul_zero,sub_zero,zero_sub] at h1 h2
  have hg : (∫ x in a..b, φ x*deriv (deriv D) x) =
      ∫ x in a..b, D x*deriv (deriv φ) x := by
    rw [h1,h2]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    ring
  have heq : (fun x => D x*(-deriv (deriv φ) x+(V x-e)*φ x)) =
      (fun x => φ x*deriv (deriv D) x-D x*deriv (deriv φ) x) := by
    funext x
    linear_combination φ x * hode x
  rw [heq,intervalIntegral.integral_sub
    ((hφ.continuous.mul hDdd.continuous).intervalIntegrable a b)
    ((hD.continuous.mul hφdd.continuous).intervalIntegrable a b),hg,sub_self]

#print axioms oscillator_test_orthogonality
theorem compactTest_orthogonality (n : ℕ) (hn : n = 0 ∨ n = 4) :
    (∫ x in (-1:ℝ)..1, parabolicCylinderD n (projectCylinderArgument x) *
      (-deriv (deriv (compactTest n)) x +
        (4*Real.pi^2*x^2-2*Real.pi*(2*(n:ℝ)+1))*compactTest n x)) = 0 := by
  have hD : ContDiff ℝ ∞ (fun x => parabolicCylinderD n (projectCylinderArgument x)) := by
    rcases hn with rfl | rfl
    · simp_rw [parabolicCylinderD_zero_projectArgument]
      fun_prop
    · simp_rw [parabolicCylinderD_four_projectArgument]
      fun_prop
  obtain ⟨ha,hb,hda,hdb⟩ := compactTest_boundary n hn
  apply oscillator_test_orthogonality (-1) 1 (2*Real.pi*(2*(n:ℝ)+1)) _ _
    (fun x => 4*Real.pi^2*x^2) hD (compactTest_contDiff n hn) _ ha hb hda hdb
  intro x
  rcases hn with rfl | rfl
  · simpa using target_zero_oscillator x
  · convert target_four_oscillator x using 1 <;> norm_num <;> ring <;> simp

#print axioms compactTest_orthogonality
theorem compactTest_complex_orthogonality (n : ℕ) (hn : n = 0 ∨ n = 4) :
    (∫ x in (-1:ℝ)..1, cylinderTarget n x *
      (-((deriv (deriv (compactTest n)) x : ℝ) : ℂ) +
        ((4*Real.pi^2*x^2-2*Real.pi*(2*(n:ℝ)+1) : ℝ) : ℂ) *
          (compactTest n x : ℂ))) = 0 := by
  have hc : (∫ x in (-1:ℝ)..1,
      ((parabolicCylinderD n (projectCylinderArgument x) *
        (-deriv (deriv (compactTest n)) x +
          (4*Real.pi^2*x^2-2*Real.pi*(2*(n:ℝ)+1))*compactTest n x) : ℝ) : ℂ)) = 0 := by
    rw [intervalIntegral.integral_ofReal, compactTest_orthogonality n hn]
    norm_num
  simpa only [cylinderTarget,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_neg] using hc

theorem compactTest_complex_overlap_positive (n : ℕ) (hn : n = 0 ∨ n = 4) :
    0 < ‖∫ x in (-1:ℝ)..1, cylinderTarget n x * (compactTest n x : ℂ)‖ := by
  have heq : (∫ x in (-1:ℝ)..1, cylinderTarget n x * (compactTest n x : ℂ)) =
      (((∫ x in (-1:ℝ)..1, parabolicCylinderD n (projectCylinderArgument x) *
        compactTest n x) : ℝ) : ℂ) := by
    simp only [cylinderTarget, ← Complex.ofReal_mul]
    exact intervalIntegral.integral_ofReal
  rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (compactTest_overlap_positive n hn)]
  exact compactTest_overlap_positive n hn

#print axioms compactTest_complex_orthogonality
#print axioms compactTest_complex_overlap_positive
def prolateFlux (lam : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((lam^2-x^2 : ℝ) : ℂ) * deriv f x

theorem prolateFlux_contDiffOn (lam : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Ioo (-lam) lam)) :
    ContDiffOn ℝ 1 (prolateFlux lam f) (Ioo (-lam) lam) := by
  have hd : ContDiffOn ℝ 1 (deriv f) (Ioo (-lam) lam) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  unfold prolateFlux
  apply ContDiffOn.mul _ hd
  have hw : ContDiff ℝ 1 (fun x : ℝ => lam^2-x^2) := by fun_prop
  simpa only [Function.comp_apply,Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff.comp hw).contDiffOn

theorem prolateFlux_hasDerivAt (lam θ : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f (Ioo (-lam) lam))
    (hode : ∀ x ∈ Ioo (-lam) lam, prolateWaveExpression lam f x = (θ:ℂ)*f x)
    (x : ℝ) (hx : x ∈ Ioo (-lam) lam) :
    HasDerivAt (prolateFlux lam f)
      ((((2*Real.pi*lam*x)^2 : ℝ) : ℂ)*f x-(θ:ℂ)*f x) x := by
  have hd := ((prolateFlux_contDiffOn lam f hf).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioo.mem_nhds hx)
  apply hd.hasDerivAt.congr_deriv
  have he := hode x hx
  simp only [prolateWaveExpression, fderiv_deriv] at he
  change -deriv (prolateFlux lam f) x +
    (((2*Real.pi*lam*x)^2 : ℝ) : ℂ)*f x = (θ:ℂ)*f x at he
  linear_combination -he

theorem normalized_mode_flux_hasDerivAt
    {m K : ℕ} {Λ : ℝ} (S : Mode4FerrersRegularEvenProlateSolution m K Λ)
    (hm : 2 ≤ m) (x : ℝ) (hx : x ∈ Ioo (-Real.sqrt m) (Real.sqrt m)) :
    HasDerivAt (prolateFlux (Real.sqrt m) S.normalizedPhysicalMode)
      (((((2*Real.pi*Real.sqrt m*x)^2 : ℝ) : ℂ) -
        ((Λ+mode4JacobiG m : ℝ) : ℂ))*S.normalizedPhysicalMode x) x := by
  have hh := prolateFlux_hasDerivAt (Real.sqrt m) (Λ+mode4JacobiG m)
    S.normalizedPhysicalMode (normalizedPhysicalMode_contDiffOn_two_open S hm)
    (fun y hy => normalizedPhysicalMode_prolateWaveExpression_eigenrelation S hm hy) x hx
  convert hh using 1 <;> ring

#print axioms prolateFlux_hasDerivAt
#print axioms normalized_mode_flux_hasDerivAt
theorem prolate_compact_weak (lam θ : ℝ) (f φ : ℝ → ℂ)
    (hlam : 1 < lam) (hf : ContDiffOn ℝ 2 f (Ioo (-lam) lam))
    (hode : ∀ x ∈ Ioo (-lam) lam, prolateWaveExpression lam f x = (θ:ℂ)*f x)
    (hφ : ContDiff ℝ ∞ φ)
    (hφa : φ (-1)=0) (hφb : φ 1=0)
    (hda : deriv φ (-1)=0) (hdb : deriv φ 1=0) :
    (∫ x in (-1:ℝ)..1, φ x *
      (((((2*Real.pi*lam*x)^2 : ℝ) : ℂ)-(θ:ℂ))*f x)) =
    ∫ x in (-1:ℝ)..1, f x *
      (((lam^2-x^2 : ℝ) : ℂ)*deriv (deriv φ) x - ((2*x:ℝ):ℂ)*deriv φ x) := by
  have hsub : uIcc (-1:ℝ) 1 ⊆ Ioo (-lam) lam := by
    rw [uIcc_of_le (by norm_num)]
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hopen : Ioo (min (-1:ℝ) 1) (max (-1:ℝ) 1) ⊆ Ioo (-lam) lam := by
    intro x hx
    apply hsub
    exact Ioo_subset_Icc_self hx
  have hdfc := hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hφdd := (contDiff_infty_iff_deriv.mp hφd).2
  have hp : Continuous (fun x : ℝ => ((lam^2-x^2 : ℝ):ℂ)) := by fun_prop
  have htf : Continuous (fun x : ℝ => ((lam^2-x^2 : ℝ):ℂ)*deriv φ x) :=
    hp.mul hφd.continuous
  have hdtf : Continuous (fun x : ℝ => ((lam^2-x^2 : ℝ):ℂ)*deriv (deriv φ) x -
      ((2*x:ℝ):ℂ)*deriv φ x) := by
    exact (hp.mul hφdd.continuous).sub
      ((show Continuous (fun x : ℝ => ((2*x:ℝ):ℂ)) by fun_prop).mul hφd.continuous)
  apply compact_flux_green (-1) 1 f (deriv f) φ (deriv φ)
    (fun x => ((lam^2-x^2 : ℝ):ℂ)) (prolateFlux lam f)
    (fun x => (((((2*Real.pi*lam*x)^2 : ℝ):ℂ)-(θ:ℂ))*f x))
    (fun x => ((lam^2-x^2 : ℝ):ℂ)*deriv φ x)
    (fun x => ((lam^2-x^2 : ℝ):ℂ)*deriv (deriv φ) x - ((2*x:ℝ):ℂ)*deriv φ x)
    (hf.continuousOn.mono hsub) hφ.continuous.continuousOn
    ((prolateFlux_contDiffOn lam f hf).continuousOn.mono hsub) htf.continuousOn
  · intro x hx
    exact ((hf.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds (hopen hx))).hasDerivAt
  · intro x hx
    exact ((contDiff_infty_iff_deriv.mp hφ).1 x).hasDerivAt
  · intro x hx
    convert prolateFlux_hasDerivAt lam θ f hf hode x (hopen hx) using 1 <;> ring
  · intro x hx
    have hw : HasDerivAt (fun y : ℝ => ((lam^2-y^2 : ℝ):ℂ)) ((-2*x:ℝ):ℂ) x := by
      convert (((hasDerivAt_const x (lam^2)).sub ((hasDerivAt_id x).pow 2)).ofReal_comp) using 1
      simp only [id_eq]
      push_cast
      ring
    convert hw.mul (((contDiff_infty_iff_deriv.mp hφd).1 x).hasDerivAt) using 1
    push_cast
    ring
  · exact (hdfc.mono hsub).intervalIntegrable
  · exact hφd.continuous.intervalIntegrable _ _
  · have hc : ContinuousOn (fun x => (((((2*Real.pi*lam*x)^2 : ℝ):ℂ)-(θ:ℂ))*f x))
        (uIcc (-1:ℝ) 1) := by
      apply ContinuousOn.mul _ (hf.continuousOn.mono hsub)
      fun_prop
    exact hc.intervalIntegrable
  · exact hdtf.intervalIntegrable _ _
  · intro x; rfl
  · intro x; rfl
  · exact hφa
  · exact hφb
  · simp [hda]
  · simp [hdb]

#print axioms prolate_compact_weak
theorem normalized_mode_compact_weak
    {m K : ℕ} {Λ : ℝ} (S : Mode4FerrersRegularEvenProlateSolution m K Λ)
    (hm : 2 ≤ m) (α : ℂ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hφa : φ (-1)=0) (hφb : φ 1=0)
    (hda : deriv φ (-1)=0) (hdb : deriv φ 1=0) :
    (∫ x in (-1:ℝ)..1, φ x *
      (((((2*Real.pi*Real.sqrt m*x)^2 : ℝ) : ℂ)-((Λ+mode4JacobiG m:ℝ):ℂ))*
        (α*S.normalizedPhysicalMode x))) =
    ∫ x in (-1:ℝ)..1, (α*S.normalizedPhysicalMode x) *
      (((((Real.sqrt m)^2-x^2) : ℝ) : ℂ)*deriv (deriv φ) x - ((2*x:ℝ):ℂ)*deriv φ x) := by
  have hlam : 1 < Real.sqrt (m:ℝ) := by
    rw [show (1:ℝ)=Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_lt_sqrt (by norm_num)
    exact_mod_cast (show 1 < m by omega)
  have hh := prolate_compact_weak (Real.sqrt m) (Λ+mode4JacobiG m)
    S.normalizedPhysicalMode φ hlam (normalizedPhysicalMode_contDiffOn_two_open S hm)
    (fun x hx => normalizedPhysicalMode_prolateWaveExpression_eigenrelation S hm hx)
    hφ hφa hφb hda hdb
  have he := congrArg (fun z : ℂ => α*z) hh
  dsimp only at he
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul] at he
  convert he using 1 <;> apply intervalIntegral.integral_congr <;> intro x hx <;>
    dsimp only <;> ring

#print axioms normalized_mode_compact_weak
def CompactWeakODE (m θ : ℝ) (f φ : ℝ → ℂ) : Prop :=
  (∫ x in (-1:ℝ)..1, φ x * (((m*(4*Real.pi^2*x^2)-θ : ℝ):ℂ)*f x)) =
    ∫ x in (-1:ℝ)..1, f x * ((m:ℂ)*deriv (deriv φ) x -
      ((x^2:ℝ):ℂ)*deriv (deriv φ) x-((2*x:ℝ):ℂ)*deriv φ x)

theorem normalized_mode_weak_ode
    {m K : ℕ} {Λ : ℝ} (S : Mode4FerrersRegularEvenProlateSolution m K Λ)
    (hm : 2 ≤ m) (α : ℂ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hφa : φ (-1)=0) (hφb : φ 1=0)
    (hda : deriv φ (-1)=0) (hdb : deriv φ 1=0) :
    CompactWeakODE (m:ℝ) (Λ+mode4JacobiG m) (fun x => α*S.normalizedPhysicalMode x) φ := by
  have hh := normalized_mode_compact_weak S hm α φ hφ hφa hφb hda hdb
  have hp (x : ℝ) : (2*Real.pi*Real.sqrt m*x)^2 = (m:ℝ)*(4*Real.pi^2*x^2) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    calc
      _ = 4*Real.pi^2*(Real.sqrt m)^2*x^2 := by ring
      _ = _ := by rw [hs]; ring
  simp only [hp,Real.sq_sqrt (Nat.cast_nonneg m : (0:ℝ) ≤ m)] at hh
  unfold CompactWeakODE
  convert hh using 1 <;> apply intervalIntegral.integral_congr <;> intro x hx <;>
    dsimp only <;> push_cast <;> ring

theorem selected_anchored_weak_ode (k : ℕ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hφa : φ (-1)=0) (hφb : φ 1=0)
    (hda : deriv φ (-1)=0) (hdb : deriv φ 1=0) :
    CompactWeakODE (k+2:ℕ)
      (mode4ClassicalEvenEigenvalue (mode4JacobiG (k+2)) 0 + mode4JacobiG (k+2))
      (fun x => centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 x) φ ∧
    CompactWeakODE (k+2:ℕ)
      (mode4ClassicalEvenEigenvalue (mode4JacobiG (k+2)) 2 + mode4JacobiG (k+2))
      (fun x => centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 x) φ := by
  constructor
  · rw [selectedFerrersPreAnchorPair_h0_eq_selectedMode]
    exact normalized_mode_weak_ode (selectedFerrersPreAnchorSolution0 k) (by omega)
      (centerAnchorScalarZero k) φ hφ hφa hφb hda hdb
  · rw [selectedFerrersPreAnchorPair_h4_eq_selectedMode]
    exact normalized_mode_weak_ode (selectedFerrersPreAnchorSolution4 k) (by omega)
      (centerAnchorScalarFour k) φ hφ hφa hφb hda hdb

#print axioms normalized_mode_weak_ode
#print axioms selected_anchored_weak_ode
theorem complex_compactTest_regular (n : ℕ) (hn : n = 0 ∨ n = 4) :
    ContDiff ℝ ∞ (fun x => (compactTest n x : ℂ)) ∧
    (compactTest n (-1) : ℂ) = 0 ∧ (compactTest n 1 : ℂ) = 0 ∧
    deriv (fun x => (compactTest n x : ℂ)) (-1) = 0 ∧
    deriv (fun x => (compactTest n x : ℂ)) 1 = 0 := by
  have hd (x : ℝ) : deriv (fun y => (compactTest n y : ℂ)) x =
      ((deriv (compactTest n) x : ℝ) : ℂ) :=
    (((contDiff_infty_iff_deriv.mp (compactTest_contDiff n hn)).1 x).hasDerivAt.ofReal_comp).deriv
  obtain ⟨ha,hb,hda,hdb⟩ := compactTest_boundary n hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply,Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp (compactTest_contDiff n hn)
  · simp [ha]
  · simp [hb]
  · rw [hd,hda]; norm_num
  · rw [hd,hdb]; norm_num

theorem selected_anchored_concrete_test_weak (k : ℕ) :
    CompactWeakODE (k+2:ℕ)
      (mode4ClassicalEvenEigenvalue (mode4JacobiG (k+2)) 0 + mode4JacobiG (k+2))
      (fun x => centerAnchorScalarZero k * (selectedFerrersPreAnchorPair k).h0 x)
      (fun x => (compactTest 0 x : ℂ)) ∧
    CompactWeakODE (k+2:ℕ)
      (mode4ClassicalEvenEigenvalue (mode4JacobiG (k+2)) 2 + mode4JacobiG (k+2))
      (fun x => centerAnchorScalarFour k * (selectedFerrersPreAnchorPair k).h4 x)
      (fun x => (compactTest 4 x : ℂ)) := by
  obtain ⟨hc0,ha0,hb0,hda0,hdb0⟩ := complex_compactTest_regular 0 (Or.inl rfl)
  obtain ⟨hc4,ha4,hb4,hda4,hdb4⟩ := complex_compactTest_regular 4 (Or.inr rfl)
  exact ⟨(selected_anchored_weak_ode k _ hc0 ha0 hb0 hda0 hdb0).1,
    (selected_anchored_weak_ode k _ hc4 ha4 hb4 hda4 hdb4).2⟩

#print axioms selected_anchored_concrete_test_weak
theorem complex_compactTest_derivatives (n : ℕ) (hn : n = 0 ∨ n = 4) :
    deriv (fun x => (compactTest n x : ℂ)) =
      (fun x => ((deriv (compactTest n) x : ℝ):ℂ)) ∧
    deriv (deriv (fun x => (compactTest n x : ℂ))) =
      (fun x => ((deriv (deriv (compactTest n)) x : ℝ):ℂ)) := by
  have hc := compactTest_contDiff n hn
  have hd := (contDiff_infty_iff_deriv.mp hc).2
  have hfirst : deriv (fun x => (compactTest n x : ℂ)) =
      (fun x => ((deriv (compactTest n) x : ℝ):ℂ)) := by
    funext x
    exact (((contDiff_infty_iff_deriv.mp hc).1 x).hasDerivAt.ofReal_comp).deriv
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
  funext x
  exact (((contDiff_infty_iff_deriv.mp hd).1 x).hasDerivAt.ofReal_comp).deriv

#print axioms complex_compactTest_derivatives
theorem compact_product_error_bound (f D g : ℝ → ℂ) (ε : ℝ)
    (hf : ContinuousOn f (Icc (-1) 1)) (hD : ContinuousOn D (Icc (-1) 1))
    (hg : ContinuousOn g (Icc (-1) 1))
    (herr : ∀ x ∈ Icc (-1:ℝ) 1, ‖f x-D x‖ ≤ ε) :
    ‖∫ x in (-1:ℝ)..1, (f x-D x)*g x‖ ≤ ε*(∫ x in (-1:ℝ)..1, ‖g x‖) := by
  have hab : (-1:ℝ) ≤ 1 := by norm_num
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  calc
    (∫ x in (-1:ℝ)..1, ‖(f x-D x)*g x‖) ≤ ∫ x in (-1:ℝ)..1, ε*‖g x‖ := by
      apply intervalIntegral.integral_mono_on hab
        (((hf.sub hD).mul hg).norm.intervalIntegrable_of_Icc hab)
        ((continuousOn_const.mul hg.norm).intervalIntegrable_of_Icc hab)
      intro x hx
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (herr x hx) (norm_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem compact_overlap_floor (f D φ : ℝ → ℂ) (ε J : ℝ)
    (hf : ContinuousOn f (Icc (-1) 1)) (hD : ContinuousOn D (Icc (-1) 1))
    (hφ : ContinuousOn φ (Icc (-1) 1))
    (hJ : J = ‖∫ x in (-1:ℝ)..1, D x*φ x‖)
    (herr : ∀ x ∈ Icc (-1:ℝ) 1, ‖f x-D x‖ ≤ ε)
    (hsmall : ε*(∫ x in (-1:ℝ)..1, ‖φ x‖) ≤ J/2) :
    J/2 ≤ ‖∫ x in (-1:ℝ)..1, f x*φ x‖ := by
  have hh := compact_product_error_bound f D φ ε hf hD hφ herr
  have heq : (∫ x in (-1:ℝ)..1, (f x-D x)*φ x) =
      (∫ x in (-1:ℝ)..1, f x*φ x)-(∫ x in (-1:ℝ)..1, D x*φ x) := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub
      ((hf.mul hφ).intervalIntegrable_of_Icc (by norm_num))
      ((hD.mul hφ).intervalIntegrable_of_Icc (by norm_num))
  rw [heq] at hh
  have hr := norm_sub_norm_le (∫ x in (-1:ℝ)..1, D x*φ x)
    (∫ x in (-1:ℝ)..1, f x*φ x)
  rw [norm_sub_rev, ← hJ] at hr
  linarith

theorem compact_source_pairing_bound (f D T : ℝ → ℂ) (ε : ℝ)
    (hf : ContinuousOn f (Icc (-1) 1)) (hD : ContinuousOn D (Icc (-1) 1))
    (hT : ContinuousOn T (Icc (-1) 1))
    (herr : ∀ x ∈ Icc (-1:ℝ) 1, ‖f x-D x‖ ≤ ε) :
    ‖∫ x in (-1:ℝ)..1, f x*T x‖ ≤
      ‖∫ x in (-1:ℝ)..1, D x*T x‖+ε*(∫ x in (-1:ℝ)..1, ‖T x‖) := by
  have hh := compact_product_error_bound f D T ε hf hD hT herr
  have heq : (∫ x in (-1:ℝ)..1, f x*T x) =
      (∫ x in (-1:ℝ)..1, D x*T x)+(∫ x in (-1:ℝ)..1, (f x-D x)*T x) := by
    rw [← intervalIntegral.integral_add
      ((hD.mul hT).intervalIntegrable_of_Icc (by norm_num))
      (((hf.sub hD).mul hT).intervalIntegrable_of_Icc (by norm_num))]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hh)

#print axioms compact_product_error_bound
#print axioms compact_overlap_floor
#print axioms compact_source_pairing_bound
theorem compact_theta_bound_of_mode_error
    (m θ e C J : ℝ) (f D φ A T : ℝ → ℂ)
    (hm : 1 ≤ m) (hC : 0 ≤ C) (hJ : 0 < J)
    (hf : ContinuousOn f (Icc (-1) 1)) (hD : ContinuousOn D (Icc (-1) 1))
    (hφ : ContinuousOn φ (Icc (-1) 1)) (hA : ContinuousOn A (Icc (-1) 1))
    (hT : ContinuousOn T (Icc (-1) 1))
    (hJeq : J = ‖∫ x in (-1:ℝ)..1, D x*φ x‖)
    (herr : ∀ x ∈ Icc (-1:ℝ) 1, ‖f x-D x‖ ≤ C/m)
    (hlarge : 2*C*(∫ x in (-1:ℝ)..1, ‖φ x‖) ≤ J*m)
    (hidentity : (((θ-e*m : ℝ):ℂ))*(∫ x in (-1:ℝ)..1, f x*φ x) =
      (m:ℂ)*(∫ x in (-1:ℝ)..1, (f x-D x)*A x) +
      ∫ x in (-1:ℝ)..1, f x*T x) :
    |θ-e*m| ≤ 2*(C*(∫ x in (-1:ℝ)..1, ‖A x‖) +
      (‖∫ x in (-1:ℝ)..1, D x*T x‖+C*(∫ x in (-1:ℝ)..1, ‖T x‖)))/J := by
  have hmp : 0 < m := by linarith
  have hsmall : (C/m)*(∫ x in (-1:ℝ)..1, ‖φ x‖) ≤ J/2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmp).mpr
    nlinarith
  have hfloor := compact_overlap_floor f D φ (C/m) J hf hD hφ hJeq herr hsmall
  have hU := compact_product_error_bound f D A (C/m) hf hD hA herr
  rw [div_mul_eq_mul_div] at hU
  have hV := compact_source_pairing_bound f D T (C/m) hf hD hT herr
  have hP : 0 ≤ ∫ x in (-1:ℝ)..1, ‖T x‖ :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => norm_nonneg _)
  have hVC : ‖∫ x in (-1:ℝ)..1, f x*T x‖ ≤
      ‖∫ x in (-1:ℝ)..1, D x*T x‖+C*(∫ x in (-1:ℝ)..1, ‖T x‖) :=
    hV.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (div_le_self hC hm) hP))
  exact theta_defect_bound_from_weak_pairing m θ e J _ _ _ _ _ hmp hJ hidentity hfloor hU hVC

#print axioms compact_theta_bound_of_mode_error
theorem scheduled_theta_bound
    (θ : ℕ → ℝ) (f : ℕ → ℝ → ℂ) (e C J : ℝ) (D φ A T : ℝ → ℂ)
    (hC : 0 ≤ C) (hJ : 0 < J)
    (hf : ∀ k, ContinuousOn (f k) (Icc (-1) 1))
    (hD : ContinuousOn D (Icc (-1) 1)) (hφ : ContinuousOn φ (Icc (-1) 1))
    (hA : ContinuousOn A (Icc (-1) 1)) (hT : ContinuousOn T (Icc (-1) 1))
    (hJeq : J = ‖∫ x in (-1:ℝ)..1, D x*φ x‖)
    (herr : ∀ᶠ k in Filter.atTop, ∀ x ∈ Icc (-1:ℝ) 1,
      ‖f k x-D x‖ ≤ C/((k+2:ℕ):ℝ))
    (hidentity : ∀ᶠ k in Filter.atTop,
      (((θ k-e*((k+2:ℕ):ℝ) : ℝ):ℂ))*(∫ x in (-1:ℝ)..1, f k x*φ x) =
        (((k+2:ℕ):ℝ):ℂ)*(∫ x in (-1:ℝ)..1, (f k x-D x)*A x) +
          ∫ x in (-1:ℝ)..1, f k x*T x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in Filter.atTop, |θ k-e*((k+2:ℕ):ℝ)| ≤ B := by
  let B := 2*(C*(∫ x in (-1:ℝ)..1, ‖A x‖) +
    (‖∫ x in (-1:ℝ)..1, D x*T x‖+C*(∫ x in (-1:ℝ)..1, ‖T x‖)))/J
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  obtain ⟨K,hK⟩ := exists_nat_ge (2*C*(∫ x in (-1:ℝ)..1, ‖φ x‖)/J)
  filter_upwards [herr,hidentity,Filter.eventually_ge_atTop K] with k hk hid hkK
  have hm : (1:ℝ) ≤ ((k+2:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ k+2 by omega)
  have hlarge : 2*C*(∫ x in (-1:ℝ)..1, ‖φ x‖) ≤ J*((k+2:ℕ):ℝ) := by
    rw [mul_comm J]
    apply (div_le_iff₀ hJ).mp
    exact hK.trans (by exact_mod_cast (show K ≤ k+2 by omega))
  have hb := compact_theta_bound_of_mode_error ((k+2:ℕ):ℝ) (θ k) e C J
    (f k) D φ A T hm hC hJ (hf k) hD hφ hA hT hJeq hk hlarge hid
  exact hb.trans (le_max_right _ _)

#print axioms scheduled_theta_bound
end Q3OverlapProbe
