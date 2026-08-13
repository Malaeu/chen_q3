import Q3.Proofs.RouteB.D0KTrialStage2
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option linter.mathlibStandardSet false

open Complex MeasureTheory
open scoped FourierTransform

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Fourier invariance of the explicit CCM limiting packet

The source formula is CCM Eq. (7.1), pinned locally at
`literature/zotero/H8ULBMAL/fulltext.md:1262-1267`:

`h(x) = (pi / 2) * x^2 * (2 * pi * x^2 - 3) * exp (-pi * x^2)`.

The proof derives the second and fourth Gaussian moments from Mathlib's
Fourier/derivative identity.  It does not assume Fourier invariance as an
input.  The Poisson summation transport to `E_star` is a separate downstream
step.
-/

/-- The literal polynomial-Gaussian limiting packet of CCM Eq. (7.1). -/
noncomputable def explicitCCMLimitH (x : ℝ) : ℂ :=
  (((Real.pi / 2) * x ^ 2 * (2 * Real.pi * x ^ 2 - 3) : ℝ) : ℂ) *
    Complex.exp (-Real.pi * (x : ℂ) ^ 2)

private noncomputable def gaussianPi (x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (x : ℂ) ^ 2)

private lemma integrable_moment_gaussianPi (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n • gaussianPi x) := by
  have hreal :
      Integrable (fun x : ℝ => x ^ n * Real.exp (-Real.pi * x ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos
      (show (-1 : ℝ) < (n : ℝ) by
        exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
    simpa only [Real.rpow_natCast] using h
  have hc :
      Integrable (fun x : ℝ =>
        ((x ^ n * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ)) :=
    hreal.ofReal
  convert hc using 1
  funext x
  unfold gaussianPi
  rw [Complex.real_smul]
  rw [show -Real.pi * (x : ℂ) ^ 2 =
      ((-Real.pi * x ^ 2 : ℝ) : ℂ) by norm_cast]
  rw [← Complex.ofReal_exp]
  exact (Complex.ofReal_mul _ _).symm

private lemma hasDerivAt_gaussianPi (x : ℝ) :
    HasDerivAt gaussianPi ((-2 * Real.pi * x : ℂ) * gaussianPi x) x := by
  unfold gaussianPi
  have h :=
    (((hasDerivAt_pow 2 (x : ℂ)).const_mul (-(Real.pi : ℂ))).cexp).comp_ofReal
  convert h using 1 <;> ring

private lemma deriv_gaussianPi :
    deriv gaussianPi = fun x : ℝ => (-2 * Real.pi * x : ℂ) * gaussianPi x := by
  funext x
  exact (hasDerivAt_gaussianPi x).deriv

private noncomputable def gaussianP2 (x : ℝ) : ℂ :=
  ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi : ℝ) : ℂ)

private noncomputable def gaussianP3 (x : ℝ) : ℂ :=
  ((-8 * Real.pi ^ 3 * x ^ 3 + 12 * Real.pi ^ 2 * x : ℝ) : ℂ)

private noncomputable def gaussianP4 (x : ℝ) : ℂ :=
  ((16 * Real.pi ^ 4 * x ^ 4 - 48 * Real.pi ^ 3 * x ^ 2 +
    12 * Real.pi ^ 2 : ℝ) : ℂ)

private lemma hasDerivAt_gaussianP2 (x : ℝ) :
    HasDerivAt gaussianP2 (8 * (Real.pi : ℂ) ^ 2 * x) x := by
  unfold gaussianP2
  have h :
      HasDerivAt (fun y : ℝ => 4 * Real.pi ^ 2 * y ^ 2 - 2 * Real.pi)
        (8 * Real.pi ^ 2 * x) x := by
    convert (((hasDerivAt_pow 2 x).const_mul (4 * Real.pi ^ 2)).sub_const
      (2 * Real.pi)) using 1 <;> ring
  convert h.ofReal_comp using 1 <;> norm_cast

private lemma hasDerivAt_gaussianP3 (x : ℝ) :
    HasDerivAt gaussianP3
      (-24 * (Real.pi : ℂ) ^ 3 * (x : ℂ) ^ 2 + 12 * Real.pi ^ 2) x := by
  unfold gaussianP3
  have h :
      HasDerivAt
        (fun y : ℝ => -8 * Real.pi ^ 3 * y ^ 3 + 12 * Real.pi ^ 2 * y)
        (-24 * Real.pi ^ 3 * x ^ 2 + 12 * Real.pi ^ 2) x := by
    convert (((hasDerivAt_pow 3 x).const_mul (-8 * Real.pi ^ 3)).add
      ((hasDerivAt_id x).const_mul (12 * Real.pi ^ 2))) using 1 <;> ring
  convert h.ofReal_comp using 1 <;> norm_cast

private lemma deriv_gaussianP2_mul_gaussianPi :
    deriv (fun x => gaussianP2 x * gaussianPi x) =
      fun x => gaussianP3 x * gaussianPi x := by
  funext x
  have h := (hasDerivAt_gaussianP2 x).mul (hasDerivAt_gaussianPi x)
  change deriv (gaussianP2 * gaussianPi) x = _
  rw [h.deriv]
  unfold gaussianP2 gaussianP3
  push_cast
  ring

private lemma deriv_gaussianP3_mul_gaussianPi :
    deriv (fun x => gaussianP3 x * gaussianPi x) =
      fun x => gaussianP4 x * gaussianPi x := by
  funext x
  have h := (hasDerivAt_gaussianP3 x).mul (hasDerivAt_gaussianPi x)
  change deriv (gaussianP3 * gaussianPi) x = _
  rw [h.deriv]
  unfold gaussianP3 gaussianP4
  push_cast
  ring

private lemma iteratedDeriv_two_gaussianPi :
    iteratedDeriv 2 gaussianPi = fun x => gaussianP2 x * gaussianPi x := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [deriv_gaussianPi]
  funext x
  have ha :
      HasDerivAt (fun y : ℝ => (-2 * Real.pi * y : ℂ)) (-2 * Real.pi) x := by
    have hr : HasDerivAt (fun y : ℝ => -2 * Real.pi * y) (-2 * Real.pi) x := by
      convert (hasDerivAt_id x).const_mul (-2 * Real.pi) using 1 <;> ring
    convert hr.ofReal_comp using 1 <;> push_cast <;> ring
  have h := ha.mul (hasDerivAt_gaussianPi x)
  change deriv ((fun y : ℝ => (-2 * Real.pi * y : ℂ)) * gaussianPi) x = _
  rw [h.deriv]
  unfold gaussianP2
  push_cast
  ring

private lemma iteratedDeriv_four_gaussianPi :
    iteratedDeriv 4 gaussianPi = fun x => gaussianP4 x * gaussianPi x := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
  rw [iteratedDeriv_two_gaussianPi, deriv_gaussianP2_mul_gaussianPi,
    deriv_gaussianP3_mul_gaussianPi]

private noncomputable def fourierMoment2 (x : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 2 • gaussianPi x

private noncomputable def fourierMoment4 (x : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 4 • gaussianPi x

private lemma integrable_fourierMoment2 : Integrable fourierMoment2 := by
  have h :=
    (integrable_moment_gaussianPi 2).const_mul ((-2 * (Real.pi : ℂ) * I) ^ 2)
  convert h using 1
  funext x
  unfold fourierMoment2
  rw [Complex.real_smul]
  simp only [smul_eq_mul]
  push_cast
  ring

private lemma integrable_fourierMoment4 : Integrable fourierMoment4 := by
  have h :=
    (integrable_moment_gaussianPi 4).const_mul ((-2 * (Real.pi : ℂ) * I) ^ 4)
  convert h using 1
  funext x
  unfold fourierMoment4
  rw [Complex.real_smul]
  simp only [smul_eq_mul]
  push_cast
  ring

private lemma fourier_add_integrable {f k : ℝ → ℂ}
    (hf : Integrable f) (hk : Integrable k) :
    𝓕 (f + k) = 𝓕 f + 𝓕 k := by
  exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar
    continuous_inner hf hk

private lemma fourier_const_smul (c : ℂ) (f : ℝ → ℂ) :
    𝓕 (c • f) = c • 𝓕 f := by
  exact VectorFourier.fourierIntegral_const_smul _ _ _ _ _

private lemma fourier_gaussianPi : 𝓕 gaussianPi = gaussianPi := by
  unfold gaussianPi
  simpa using (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num))

private lemma fourier_fourierMoment2 :
    𝓕 fourierMoment2 = fun x => gaussianP2 x * gaussianPi x := by
  have h := Real.iteratedDeriv_fourier (f := gaussianPi) (N := (4 : ℕ∞))
    (fun n _ => integrable_moment_gaussianPi n) (n := 2) (by norm_num)
  rw [fourier_gaussianPi, iteratedDeriv_two_gaussianPi] at h
  exact h.symm

private lemma fourier_fourierMoment4 :
    𝓕 fourierMoment4 = fun x => gaussianP4 x * gaussianPi x := by
  have h := Real.iteratedDeriv_fourier (f := gaussianPi) (N := (4 : ℕ∞))
    (fun n _ => integrable_moment_gaussianPi n) (n := 4) (by norm_num)
  rw [fourier_gaussianPi, iteratedDeriv_four_gaussianPi] at h
  exact h.symm

private noncomputable def spectralCCMLimitH : ℝ → ℂ :=
  (1 / (16 * (Real.pi : ℂ) ^ 2)) • fourierMoment4 +
    (3 / (8 * (Real.pi : ℂ))) • fourierMoment2

private lemma spectralCCMLimitH_eq_explicitCCMLimitH :
    spectralCCMLimitH = explicitCCMLimitH := by
  funext x
  unfold spectralCCMLimitH fourierMoment4 fourierMoment2 explicitCCMLimitH gaussianPi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hI2 : I ^ 2 = (-1 : ℂ) := by norm_num
  have hI4 : I ^ 4 = (1 : ℂ) := by norm_num
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [hI2, hI4]
  ring

private lemma fourier_spectralCCMLimitH :
    𝓕 spectralCCMLimitH = spectralCCMLimitH := by
  unfold spectralCCMLimitH
  calc
    𝓕 ((1 / (16 * (Real.pi : ℂ) ^ 2)) • fourierMoment4 +
        (3 / (8 * (Real.pi : ℂ))) • fourierMoment2) =
        (1 / (16 * (Real.pi : ℂ) ^ 2)) • 𝓕 fourierMoment4 +
          (3 / (8 * (Real.pi : ℂ))) • 𝓕 fourierMoment2 := by
      rw [fourier_add_integrable]
      · rw [fourier_const_smul, fourier_const_smul]
      · exact integrable_fourierMoment4.const_mul _
      · exact integrable_fourierMoment2.const_mul _
    _ = (1 / (16 * (Real.pi : ℂ) ^ 2)) •
          (fun x => gaussianP4 x * gaussianPi x) +
        (3 / (8 * (Real.pi : ℂ))) •
          (fun x => gaussianP2 x * gaussianPi x) := by
      rw [fourier_fourierMoment4, fourier_fourierMoment2]
    _ = (1 / (16 * (Real.pi : ℂ) ^ 2)) • fourierMoment4 +
        (3 / (8 * (Real.pi : ℂ))) • fourierMoment2 := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      unfold gaussianP4 gaussianP2 fourierMoment4 fourierMoment2
      have hI2 : I ^ 2 = (-1 : ℂ) := by norm_num
      have hI4 : I ^ 4 = (1 : ℂ) := by norm_num
      push_cast
      field_simp [Real.pi_ne_zero]
      ring_nf
      rw [hI2, hI4]
      simp only [smul_eq_mul]
      ring

/-- The literal CCM Eq. (7.1) packet is fixed by Mathlib's plus-phase Fourier
transform.  No Fourier eigenrelation is assumed. -/
theorem fourier_explicitCCMLimitH :
    𝓕 explicitCCMLimitH = explicitCCMLimitH := by
  rw [← spectralCCMLimitH_eq_explicitCCMLimitH]
  exact fourier_spectralCCMLimitH

private lemma explicitCCMLimitH_apply (x : ℝ) :
    explicitCCMLimitH x =
      ((Real.pi ^ 2 * x ^ 4 - (3 * Real.pi / 2) * x ^ 2 : ℝ) : ℂ) *
        gaussianPi x := by
  unfold explicitCCMLimitH gaussianPi
  push_cast
  ring

private lemma fourier_scale_pos (f : ℝ → ℂ) {u : ℝ} (hu : 0 < u) (y : ℝ) :
    𝓕 (fun x => f (u * x)) y = (u⁻¹ : ℝ) • 𝓕 f (y / u) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  let q : ℝ → ℂ := fun z =>
    Complex.exp (((-2 * Real.pi * (z / u) * y : ℝ) : ℂ) * I) • f z
  have hscale := Measure.integral_comp_mul_left q u
  rw [abs_of_pos (inv_pos.mpr hu)] at hscale
  calc
    _ = ∫ x : ℝ, q (u * x) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold q
      congr 2
      congr 2
      push_cast
      field_simp [hu.ne']
    _ = (u⁻¹ : ℝ) • ∫ z : ℝ, q z := hscale
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      unfold q
      congr 2
      congr 2
      push_cast
      field_simp [hu.ne']

open Filter Asymptotics in
private lemma explicitCCMLimitH_decay :
    explicitCCMLimitH =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  have hpoly :
      (fun x : ℝ =>
        (((Real.pi ^ 2 * x ^ 4 - (3 * Real.pi / 2) * x ^ 2 : ℝ) : ℂ)))
        =O[cocompact ℝ] (fun x : ℝ => |x| ^ 4) := by
    rw [isBigO_iff]
    refine ⟨1 + Real.pi ^ 2 + 3 * Real.pi / 2, ?_⟩
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hx1 : 1 ≤ |x| := by simpa using hx
    have hxpow : |x| ^ 2 ≤ |x| ^ 4 := by
      nlinarith [sq_nonneg (|x| ^ 2 - 1)]
    calc
      |Real.pi ^ 2 * x ^ 4 - (3 * Real.pi / 2) * x ^ 2| ≤
          Real.pi ^ 2 * |x| ^ 4 + (3 * Real.pi / 2) * |x| ^ 2 := by
        calc
          _ ≤ |Real.pi ^ 2 * x ^ 4| + |(3 * Real.pi / 2) * x ^ 2| :=
            abs_sub _ _
          _ = _ := by
            rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_sq]
            rw [abs_of_pos Real.pi_pos]
            rw [abs_of_nonneg (div_nonneg
              (mul_nonneg (by positivity) Real.pi_pos.le) (by norm_num))]
            rw [sq_abs]
      _ ≤ (1 + Real.pi ^ 2 + 3 * Real.pi / 2) * |x| ^ 4 := by
        have hp : 0 ≤ Real.pi := Real.pi_pos.le
        nlinarith [pow_nonneg (abs_nonneg x) 4]
      _ = (1 + Real.pi ^ 2 + 3 * Real.pi / 2) * |(|x| ^ 4)| := by
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg x) 4)]
  have hgauss :=
    (isLittleO_exp_neg_mul_sq_cocompact (a := (Real.pi : ℂ))
      (by simpa using Real.pi_pos) (-6 : ℝ)).isBigO
  have hmul :
      (fun x : ℝ =>
        ((((Real.pi ^ 2 * x ^ 4 - (3 * Real.pi / 2) * x ^ 2 : ℝ) : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2))
        =O[cocompact ℝ]
          (fun x : ℝ => |x| ^ 4 * |x| ^ (-6 : ℝ)) := by
    exact hpoly.mul hgauss
  have htarget :
      (fun x : ℝ => |x| ^ 4 * |x| ^ (-6 : ℝ))
        =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, one_mul]
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg x) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add (by simpa using hx)]
    norm_num
  refine (hmul.trans htarget).congr' ?_ EventuallyEq.rfl
  filter_upwards with x
  rw [explicitCCMLimitH_apply]
  rfl

open Filter Asymptotics in
private lemma rpow_decay_comp_mul_pos {f : ℝ → ℂ} {u : ℝ} (hu : 0 < u)
    (hf : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ))) :
    (fun x => f (u * x)) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  have hcomp := hf.comp_tendsto (Filter.tendsto_cocompact_mul_left₀ hu.ne')
  refine hcomp.trans ?_
  rw [isBigO_iff]
  refine ⟨|u| ^ (-2 : ℝ), ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hx
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  rw [abs_mul, Real.mul_rpow (abs_nonneg u) (abs_nonneg x)]

open Filter Asymptotics in
private lemma poisson_scaled_sum (u : ℝ) (hu : 0 < u) :
    (∑' n : ℤ, explicitCCMLimitH (u * n)) =
      ∑' n : ℤ, (u⁻¹ : ℝ) • explicitCCMLimitH ((n : ℝ) / u) := by
  let fu : ℝ → ℂ := fun x => explicitCCMLimitH (u * x)
  have hcont : Continuous fu := by
    unfold fu
    simp_rw [explicitCCMLimitH_apply]
    unfold gaussianPi
    apply Continuous.mul
    · fun_prop
    · apply Complex.continuous_exp.comp
      fun_prop
  have hfu : fu =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
    rpow_decay_comp_mul_pos hu explicitCCMLimitH_decay
  have hFfu :
      𝓕 fu =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    have hscaled :
        (fun y : ℝ => (u⁻¹ : ℝ) • explicitCCMLimitH (u⁻¹ * y))
          =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
      simpa only [Pi.smul_apply] using
        (rpow_decay_comp_mul_pos (inv_pos.mpr hu)
          explicitCCMLimitH_decay).const_smul_left (u⁻¹ : ℝ)
    refine hscaled.congr' ?_ EventuallyEq.rfl
    filter_upwards with y
    rw [fourier_scale_pos explicitCCMLimitH hu y,
      fourier_explicitCCMLimitH]
    congr 2
    field_simp [hu.ne']
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay
    hcont one_lt_two hfu hFfu 0
  calc
    _ = ∑' n : ℤ, fu (0 + n) := by simp [fu]
    _ = ∑' n : ℤ, 𝓕 fu n * fourier n (0 : UnitAddCircle) := hp
    _ = ∑' n : ℤ, 𝓕 fu n := by
      congr 1
      funext n
      simp
    _ = _ := by
      apply tsum_congr
      intro n
      rw [fourier_scale_pos explicitCCMLimitH hu n,
        fourier_explicitCCMLimitH]

private lemma explicitCCMLimitH_even (x : ℝ) :
    explicitCCMLimitH (-x) = explicitCCMLimitH x := by
  rw [explicitCCMLimitH_apply, explicitCCMLimitH_apply]
  unfold gaussianPi
  push_cast
  ring_nf

private lemma explicitCCMLimitH_zero : explicitCCMLimitH 0 = 0 := by
  rw [explicitCCMLimitH_apply]
  norm_num

open Filter Asymptotics in
private lemma summable_explicitCCMLimitH_int_mul (u : ℝ) (hu : 0 < u) :
    Summable (fun n : ℤ => explicitCCMLimitH (u * n)) := by
  have hcof := (rpow_decay_comp_mul_pos hu
    explicitCCMLimitH_decay).comp_tendsto Int.tendsto_coe_cofinite
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hcof

private lemma int_sum_eq_two_pnat_sum (u : ℝ) (hu : 0 < u) :
    (∑' n : ℤ, explicitCCMLimitH (u * n)) =
      2 * ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u) := by
  let fz : ℤ → ℂ := fun n => explicitCCMLimitH (u * (n : ℝ))
  have heven : ∀ n : ℤ, fz (-n) = fz n := by
    intro n
    unfold fz
    push_cast
    rw [show u * (-(n : ℝ)) = -(u * (n : ℝ)) by ring]
    exact explicitCCMLimitH_even _
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat heven
    (summable_explicitCCMLimitH_int_mul u hu)
  have hfz0 : fz 0 = 0 := by
    unfold fz
    norm_num [explicitCCMLimitH_zero]
  have hpn :
      (∑' n : ℕ+, fz (n : ℕ)) =
        ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u) := by
    apply tsum_congr
    intro n
    unfold fz
    congr 1
    push_cast
    ring
  rw [hfz0, zero_add, hpn, nsmul_eq_mul] at h
  exact h

private lemma positive_sum_scaling (u : ℝ) (hu : 0 < u) :
    (∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u)) =
      (u⁻¹ : ℝ) • ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u⁻¹) := by
  have hp := poisson_scaled_sum u hu
  rw [int_sum_eq_two_pnat_sum u hu] at hp
  have hinv : 0 < u⁻¹ := inv_pos.mpr hu
  rw [tsum_const_smul'' (u⁻¹ : ℝ)] at hp
  have harg :
      (fun n : ℤ => explicitCCMLimitH ((n : ℝ) / u)) =
        fun n : ℤ => explicitCCMLimitH (u⁻¹ * (n : ℝ)) := by
    funext n
    congr 1
    field_simp [hu.ne']
  rw [harg, int_sum_eq_two_pnat_sum u⁻¹ hinv] at hp
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  calc
    (2 : ℂ) * ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u) = _ := hp
    _ = 2 * ((u⁻¹ : ℝ) •
        ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u⁻¹)) := by
      rw [mul_comm (2 : ℂ), mul_comm (2 : ℂ)]
      exact (smul_mul_assoc (u⁻¹ : ℝ)
        (∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u⁻¹)) (2 : ℂ)).symm

/-- Poisson summation transports the exact Fourier invariance of the literal
CCM Eq. (7.1) packet to multiplicative inversion symmetry of `E_star` on the
positive half-line. -/
theorem E_star_explicitCCMLimitH_inv (u : ℝ) (hu : 0 < u) :
    E_star explicitCCMLimitH u⁻¹ = E_star explicitCCMLimitH u := by
  unfold E_star
  rw [Real.sqrt_inv, positive_sum_scaling u hu]
  have hs : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  simp only [Complex.real_smul]
  rw [show (u⁻¹ : ℝ) = (Real.sqrt u)⁻¹ * (Real.sqrt u)⁻¹ by
    rw [← mul_inv, hsq]]
  push_cast
  field_simp

end Q3.RouteB.D0Pstar
