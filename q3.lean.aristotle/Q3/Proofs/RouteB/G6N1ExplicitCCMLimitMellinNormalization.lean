import Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
import Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk
import Q3.Proofs.RouteB.CenteredXiZeroNonzero

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex MeasureTheory Asymptotics Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# L73.5 — the explicit CCM limit Mellin normalization

Floor `L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN` of verdict
`1dc92546`.

The exact Mellin identification of the limiting Gaussian target on the open
centered critical strip:

* `mellin (E_star explicitCCMLimitH) (-I*z) = (1/4) * centeredXi z`, and
* the factor-four corollary with coefficient exactly one.

Route: the private Gaussian-Mellin formula
`mellin explicitCCMLimitH p = p*(p-1)/8 * Gammaℝ p` is proved first, in the
absolute half-plane, by explicit `Gamma`-integral substitutions — the
coefficient `1/8` appears **before** any zeta multiplication.  The
`EStarMellinAbsolute` payload is then built (not assumed) by the same dilate
scaling argument as `MuntzV3/EStarMellinAbsolutePayload.lean`, the crosswalk
product formula gives the identity on the half-plane `1/2 < s.re`, and the
two-sided Big-O layer (`u^(-7/2)` at infinity by inverse-four decay,
`u^(7/2)` at zero by the exact public inversion
`E_star_explicitCCMLimitH_inv`) makes `mellin (E_star explicitCCMLimitH)`
differentiable on the connected strip `-3 < s.re < 3`.  The identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` extends the equality
across the strip, and the functional equation of the project `riemannXi`
(derived from `completedRiemannZeta₀_one_sub`) converts the substitution
`s = -I*z` into the production `centeredXi z`.

Deliberately NOT here: uniform outer Mellin tails on closed substrips
(L73.6), the substrip integration (L73.7), and the port inhabitant.

LEDGER:
  CLOSES: [EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI,
           FACTOR_FOUR_EXPLICIT_CCM_LIMIT_MELLIN_TO_CENTERED_XI]
  OPENS:  []
-/

/-! ## The plant -/

/-- **The plant.**  The quarter is load-bearing: at the nonzero central
anchor the quarter-scaled value differs from the unscaled one, so the
already-refuted coefficient-one Mellin identity cannot be restated. -/
private theorem quarter_centeredXi_ne_centeredXi_at_zero :
    (1 / 4 : ℂ) * centeredXi 0 ≠ centeredXi 0 := by
  have h0 := centeredXi_zero_ne_zero
  intro h
  have hmul : ((1 / 4 : ℂ) - 1) * centeredXi 0 = 0 := by
    calc
      ((1 / 4 : ℂ) - 1) * centeredXi 0 =
          (1 / 4 : ℂ) * centeredXi 0 - centeredXi 0 := by ring
      _ = 0 := sub_eq_zero.mpr h
  exact h0 ((mul_eq_zero.mp hmul).resolve_left (by norm_num))

/-! ## Local inverse-four decay of the target (private upstream, re-proved) -/

private theorem exp_linear_bound' (c s : ℝ) (hc : 0 < c) (_hs : 0 ≤ s) :
    s * Real.exp (-(s / c)) ≤ c := by
  have h1 : s / c + 1 ≤ Real.exp (s / c) := Real.add_one_le_exp _
  have h2 : s ≤ c * Real.exp (s / c) := by
    have h3 : c * (s / c + 1) = s + c := by
      rw [mul_add, mul_div_cancel₀ _ hc.ne', mul_one]
    have h4 := mul_le_mul_of_nonneg_left h1 hc.le
    rw [h3] at h4
    linarith
  rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
  linarith [h2]

private theorem s4_exp_bound (s : ℝ) (hs : 0 ≤ s) :
    s ^ 4 * Real.exp (-s) ≤ 256 := by
  have hq : s * Real.exp (-(s / 4)) ≤ 4 := exp_linear_bound' 4 s (by norm_num) hs
  have h0 : 0 ≤ s * Real.exp (-(s / 4)) := by positivity
  have hpow : (s * Real.exp (-(s / 4))) ^ 4 ≤ 4 ^ 4 :=
    pow_le_pow_left₀ h0 hq 4
  have hexp4 : Real.exp (-(s / 4)) ^ 4 = Real.exp (-s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc s ^ 4 * Real.exp (-s)
      = (s * Real.exp (-(s / 4))) ^ 4 := by
        rw [mul_pow, hexp4]
    _ ≤ 4 ^ 4 := hpow
    _ = 256 := by norm_num

private theorem s3_exp_bound (s : ℝ) (hs : 0 ≤ s) :
    s ^ 3 * Real.exp (-s) ≤ 27 := by
  have hq : s * Real.exp (-(s / 3)) ≤ 3 := exp_linear_bound' 3 s (by norm_num) hs
  have h0 : 0 ≤ s * Real.exp (-(s / 3)) := by positivity
  have hpow : (s * Real.exp (-(s / 3))) ^ 3 ≤ 3 ^ 3 :=
    pow_le_pow_left₀ h0 hq 3
  have hexp3 : Real.exp (-(s / 3)) ^ 3 = Real.exp (-s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc s ^ 3 * Real.exp (-s)
      = (s * Real.exp (-(s / 3))) ^ 3 := by
        rw [mul_pow, hexp3]
    _ ≤ 3 ^ 3 := hpow
    _ = 27 := by norm_num

/-- Local inverse-four decay of the target on the positive axis (the upstream
fact is private in its file and cannot be imported). -/
private theorem explicitCCMLimitH_inverse_four_decay (x : ℝ) (hx : 0 < x) :
    ‖explicitCCMLimitH x‖ ≤ 33 / x ^ 4 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  set s : ℝ := Real.pi * x ^ 2 with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hnorm : ‖explicitCCMLimitH x‖
      = |Real.pi / 2 * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)| * Real.exp (-s) := by
    rw [explicitCCMLimitH, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    have harg : -Real.pi * (x : ℂ) ^ 2 = ((-(Real.pi * x ^ 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.norm_exp, Complex.ofReal_re, hsdef]
  have habs2 : |Real.pi / 2 * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)|
      ≤ s ^ 2 + 3 / 2 * s := by
    have h2 : |2 * Real.pi * x ^ 2 - 3| ≤ 2 * Real.pi * x ^ 2 + 3 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg x, hpi]
    calc |Real.pi / 2 * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)|
        = (Real.pi / 2 * x ^ 2) * |2 * Real.pi * x ^ 2 - 3| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi / 2 * x ^ 2)]
      _ ≤ (Real.pi / 2 * x ^ 2) * (2 * Real.pi * x ^ 2 + 3) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = s ^ 2 + 3 / 2 * s := by rw [hsdef]; ring
  have hx4pi : x ^ 4 * Real.pi ^ 2 = s ^ 2 := by rw [hsdef]; ring
  have h4 := s4_exp_bound s hs0
  have h3 := s3_exp_bound s hs0
  have hstep : ‖explicitCCMLimitH x‖ * (x ^ 4 * Real.pi ^ 2) ≤ 297 := by
    rw [hnorm, hx4pi]
    have hchain : |Real.pi / 2 * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)| *
        Real.exp (-s) * s ^ 2
        ≤ (s ^ 2 + 3 / 2 * s) * Real.exp (-s) * s ^ 2 := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right habs2 (Real.exp_pos _).le
    have hexpand : (s ^ 2 + 3 / 2 * s) * Real.exp (-s) * s ^ 2
        = s ^ 4 * Real.exp (-s) + 3 / 2 * (s ^ 3 * Real.exp (-s)) := by
      ring
    have hval : s ^ 4 * Real.exp (-s) + 3 / 2 * (s ^ 3 * Real.exp (-s))
        ≤ 256 + 3 / 2 * 27 := by
      have := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 3/2)
      linarith
    calc |Real.pi / 2 * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)| *
        Real.exp (-s) * s ^ 2
        ≤ (s ^ 2 + 3 / 2 * s) * Real.exp (-s) * s ^ 2 := hchain
      _ = s ^ 4 * Real.exp (-s) + 3 / 2 * (s ^ 3 * Real.exp (-s)) := hexpand
      _ ≤ 256 + 3 / 2 * 27 := hval
      _ ≤ 297 := by norm_num
  have hpisq : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [hpi3]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < x ^ 4)]
  nlinarith [hstep, hpisq,
    mul_nonneg (norm_nonneg (explicitCCMLimitH x))
      (le_of_lt (pow_pos hx 4))]

/-! ## The Gaussian Mellin formula in the absolute half-plane -/

/-- The centered Gaussian factor of the target, as its own function. -/
private def gaussH (x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (x : ℂ) ^ 2)

/-- Mellin of `exp(-t)` is the Gamma function (the `Gamma` integral, with
the two factors commuted). -/
private lemma mellin_exp_neg {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  simp only [mellin, smul_eq_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _

/-- Mellin of `exp(-pi*t)`. -/
private lemma mellin_exp_neg_pi_mul {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-(Real.pi * t)) : ℝ) : ℂ)) s =
      (Real.pi : ℂ) ^ (-s) * Complex.Gamma s := by
  have h := mellin_comp_mul_left
    (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s Real.pi_pos
  rw [mellin_exp_neg hs] at h
  simpa [smul_eq_mul] using h

/-- The real-cast `rpow`-squared exponential form of the Gaussian. -/
private lemma gaussH_eq_rpow_form :
    (fun t : ℝ => ((Real.exp (-(Real.pi * t ^ (2:ℝ))) : ℝ) : ℂ)) = gaussH := by
  funext t
  have h2 : t ^ (2:ℝ) = t ^ (2:ℕ) := by
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [gaussH, h2,
    show -(Real.pi : ℂ) * (t:ℂ) ^ 2 = ((-(Real.pi * t ^ (2:ℕ)) : ℝ) : ℂ) by
      push_cast; ring,
    Complex.ofReal_exp]

private lemma re_div_two {s : ℂ} (hs : 0 < s.re) : 0 < (s / 2).re := by
  rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.div_ofReal_re]
  positivity

/-- **The Gaussian Mellin base**: `mellin gaussH s = (1/2) * Gammaℝ s`. -/
private lemma mellin_gaussH {s : ℂ} (hs : 0 < s.re) :
    mellin gaussH s = (1 / 2 : ℂ) * Gammaℝ s := by
  have hcomp := mellin_comp_rpow
    (fun t : ℝ => ((Real.exp (-(Real.pi * t)) : ℝ) : ℂ)) s (2:ℝ)
  rw [gaussH_eq_rpow_form,
    show s / ((2:ℝ):ℂ) = s / 2 by norm_num,
    mellin_exp_neg_pi_mul (re_div_two hs)] at hcomp
  rw [hcomp, Gammaℝ_def, Complex.real_smul]
  push_cast
  rw [show -s / 2 = -(s / 2) by ring]
  norm_num

/-- Convergence of the base exponential Mellin integral. -/
private lemma mellinConvergent_exp_neg {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s := by
  have h := Complex.GammaIntegral_convergent hs
  exact h.congr_fun
    (fun t _ => by simp [smul_eq_mul, mul_comm]) measurableSet_Ioi

/-- Convergence of the Gaussian Mellin integral for `0 < s.re`. -/
private lemma mellinConvergent_gaussH {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent gaussH s := by
  have hpi : MellinConvergent
      (fun t : ℝ => ((Real.exp (-(Real.pi * t)) : ℝ) : ℂ)) (s / 2) :=
    (MellinConvergent.comp_mul_left Real.pi_pos).mpr
      (mellinConvergent_exp_neg (re_div_two hs))
  have hsq := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => ((Real.exp (-(Real.pi * t)) : ℝ) : ℂ))
    (s := s) (by norm_num : (2:ℝ) ≠ 0)).mpr hpi
  rwa [gaussH_eq_rpow_form] at hsq

/-- The `k`-th real monomial against the Gaussian. -/
private def monoGaussH (k : ℕ) (x : ℝ) : ℂ :=
  ((x ^ k : ℝ) : ℂ) * gaussH x

/-- Two functions equal on `Ioi 0` have equal Mellin transforms. -/
private lemma mellin_congr_Ioi {f g : ℝ → ℂ}
    (h : Set.EqOn f g (Set.Ioi 0)) (s : ℂ) :
    mellin f s = mellin g s := by
  simp only [mellin]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [h ht])

/-- The monomial shift as a pointwise integrand identity on `Ioi 0`. -/
private lemma monomial_integrand_eqOn (k : ℕ) (s : ℂ) :
    Set.EqOn
      (fun t : ℝ => (t : ℂ) ^ (s + k - 1) • gaussH t)
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • monoGaussH k t)
      (Set.Ioi 0) := by
  intro t ht
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  simp only [smul_eq_mul, monoGaussH]
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast (t : ℂ) k,
    ← mul_assoc, ← Complex.cpow_add _ _ htne,
    show s - 1 + (k:ℂ) = s + k - 1 by ring]

/-- Convergence of the monomial-Gaussian Mellin integral. -/
private lemma mellinConvergent_monomial_gaussH (k : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    MellinConvergent (monoGaussH k) s := by
  have hsk : 0 < (s + k).re := by
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  have h := mellinConvergent_gaussH hsk
  exact h.congr_fun (monomial_integrand_eqOn k s) measurableSet_Ioi

/-- Value of the monomial-Gaussian Mellin integral. -/
private lemma mellin_monomial_gaussH (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mellin (monoGaussH k) s = (1 / 2 : ℂ) * Gammaℝ (s + k) := by
  have hsk : 0 < (s + k).re := by
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  have hcpow := mellin_cpow_smul gaussH s (k : ℂ)
  rw [mellin_gaussH hsk] at hcpow
  rw [← hcpow]
  apply mellin_congr_Ioi
  intro t ht
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  simp only [smul_eq_mul, monoGaussH]
  rw [Complex.ofReal_pow, Complex.cpow_natCast]

/-- The target decomposes into two monomial-Gaussian pieces. -/
private lemma explicitCCMLimitH_decomp :
    explicitCCMLimitH = fun x : ℝ =>
      ((Real.pi : ℂ) ^ 2) • monoGaussH 4 x -
        ((3 : ℂ) * Real.pi / 2) • monoGaussH 2 x := by
  funext x
  rw [explicitCCMLimitH]
  simp only [monoGaussH, gaussH, smul_eq_mul]
  push_cast
  ring

/-- Convergence of the target Mellin integral for `0 < s.re`. -/
private lemma mellinConvergent_explicitCCMLimitH {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent explicitCCMLimitH s := by
  rw [explicitCCMLimitH_decomp]
  exact (hasMellin_sub
    ((mellinConvergent_monomial_gaussH 4 hs).const_smul ((Real.pi : ℂ) ^ 2))
    ((mellinConvergent_monomial_gaussH 2 hs).const_smul
      ((3 : ℂ) * Real.pi / 2))).1

/-- **The exact packet formula in the absolute half-plane**:
`mellin explicitCCMLimitH s = s*(s-1)/8 * Gammaℝ s`.  The coefficient `1/8`
appears here, before any zeta multiplication. -/
private lemma mellin_explicitCCMLimitH {s : ℂ} (hs : 0 < s.re) :
    mellin explicitCCMLimitH s = s * (s - 1) / 8 * Gammaℝ s := by
  have hc4 := (mellinConvergent_monomial_gaussH 4 hs).const_smul
    ((Real.pi : ℂ) ^ 2)
  have hc2 := (mellinConvergent_monomial_gaussH 2 hs).const_smul
    ((3 : ℂ) * Real.pi / 2)
  rw [explicitCCMLimitH_decomp, (hasMellin_sub hc4 hc2).2,
    mellin_const_smul, mellin_const_smul,
    mellin_monomial_gaussH 4 hs, mellin_monomial_gaussH 2 hs]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs2ne : s + 2 ≠ 0 := by
    intro h
    have h2 : (s + 2).re = 0 := by rw [h]; simp
    rw [Complex.add_re] at h2
    norm_num at h2
    linarith
  have hG2 : Gammaℝ (s + 2) = Gammaℝ s * s / 2 / Real.pi :=
    Gammaℝ_add_two hs0
  have hG4 : Gammaℝ (s + 4) = Gammaℝ (s + 2) * (s + 2) / 2 / Real.pi := by
    have h := Gammaℝ_add_two hs2ne
    rwa [show s + 2 + 2 = s + 4 by ring] at h
  rw [show ((4:ℕ):ℂ) = (4:ℂ) by norm_num,
    show ((2:ℕ):ℂ) = (2:ℂ) by norm_num, hG4, hG2]
  have hpine : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [smul_eq_mul]
  field_simp
  ring

/-! ## The `EStarMellinAbsolute` payload (dilate scaling, not assumed) -/

/-- Dilate measurability, exactly as in the MuntzV3 payload but with the
Gaussian base convergence. -/
private lemma dilate_aestronglyMeasurable {p : ℂ} (hp : 0 < p.re) (n : ℕ+) :
    AEStronglyMeasurable
      (fun u : ℝ => (u : ℂ) ^ (p - 1) • explicitCCMLimitH (((n : ℕ) : ℝ) * u))
      (volume.restrict (Set.Ioi 0)) := by
  have hnpos : 0 < ((n : ℕ) : ℝ) := by positivity
  have hconv := (MellinConvergent.comp_mul_left hnpos).2
    (mellinConvergent_explicitCCMLimitH hp)
  change IntegrableOn
    (fun u : ℝ => (u : ℂ) ^ (p - 1) • explicitCCMLimitH (((n : ℕ) : ℝ) * u))
    (Set.Ioi 0) at hconv
  exact hconv.1

/-- Dilate `lintegral` scaling, exactly the MuntzV3 argument with the
Gaussian base convergence. -/
private lemma dilate_lintegral_eq {p : ℂ} (hp : 0 < p.re) (n : ℕ+) :
    (∫⁻ u : ℝ, ‖(u : ℂ) ^ (p - 1) • explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖ₑ
      ∂(volume.restrict (Set.Ioi 0))) =
      ENNReal.ofReal (((n : ℕ) : ℝ) ^ (-p.re)) *
        (∫⁻ v : ℝ, ‖(v : ℂ) ^ (p - 1) • explicitCCMLimitH v‖ₑ
          ∂(volume.restrict (Set.Ioi 0))) := by
  let a : ℝ := ((n : ℕ) : ℝ)
  have ha : 0 < a := by positivity
  have hbase := mellinConvergent_explicitCCMLimitH hp
  change IntegrableOn
    (fun v : ℝ => (v : ℂ) ^ (p - 1) • explicitCCMLimitH v) (Set.Ioi 0) at hbase
  have hscaled := (MellinConvergent.comp_mul_left ha).2
    (mellinConvergent_explicitCCMLimitH hp)
  change IntegrableOn
    (fun u : ℝ => (u : ℂ) ^ (p - 1) • explicitCCMLimitH (a * u))
    (Set.Ioi 0) at hscaled
  have hnorm :
      Set.EqOn
        (fun u : ℝ => ‖(u : ℂ) ^ (p - 1) • explicitCCMLimitH (a * u)‖)
        (fun u : ℝ => a ^ (1 - p.re) *
          ‖((a * u : ℝ) : ℂ) ^ (p - 1) • explicitCCMLimitH (a * u)‖)
        (Set.Ioi 0) := by
    intro u hu
    change ‖(u : ℂ) ^ (p - 1) • explicitCCMLimitH (a * u)‖ =
      a ^ (1 - p.re) * ‖((a * u : ℝ) : ℂ) ^ (p - 1) • explicitCCMLimitH (a * u)‖
    rw [norm_smul, norm_smul,
      Complex.norm_cpow_eq_rpow_re_of_pos hu,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha hu)]
    simp only [Complex.sub_re, Complex.one_re]
    rw [Real.mul_rpow ha.le hu.le]
    have hexp : (1 - p.re) + (p.re - 1) = 0 := by ring
    have hcancel : a ^ (1 - p.re) * a ^ (p.re - 1) = 1 := by
      rw [← Real.rpow_add ha, hexp]
      simp
    calc
      u ^ (p.re - 1) * ‖explicitCCMLimitH (a * u)‖ =
          (a ^ (1 - p.re) * a ^ (p.re - 1)) *
            (u ^ (p.re - 1) * ‖explicitCCMLimitH (a * u)‖) := by
        rw [hcancel, one_mul]
      _ = a ^ (1 - p.re) *
          (a ^ (p.re - 1) * u ^ (p.re - 1) * ‖explicitCCMLimitH (a * u)‖) := by
        ring
  have hreal :
      (∫ u in Set.Ioi (0 : ℝ),
          ‖(u : ℂ) ^ (p - 1) • explicitCCMLimitH (a * u)‖) =
        a ^ (-p.re) *
          ∫ v in Set.Ioi (0 : ℝ), ‖(v : ℂ) ^ (p - 1) • explicitCCMLimitH v‖ := by
    rw [setIntegral_congr_fun measurableSet_Ioi hnorm]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_comp_mul_left_Ioi
      (fun v : ℝ => ‖(v : ℂ) ^ (p - 1) • explicitCCMLimitH v‖) 0 ha]
    simp only [mul_zero, smul_eq_mul]
    rw [← mul_assoc]
    congr 1
    rw [← Real.rpow_neg_one a]
    have hexp : (1 - p.re) + (-1) = -p.re := by ring
    rw [← Real.rpow_add ha, hexp]
  rw [← ofReal_integral_norm_eq_lintegral_enorm hscaled]
  rw [← ofReal_integral_norm_eq_lintegral_enorm hbase]
  rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]

/-- The rpow-weighted `tsum` finiteness, exactly the MuntzV3 argument. -/
private lemma ennreal_pnat_rpow_mul_tsum_ne_top
    (a : ℝ) (ha : 1 < a) (C : ENNReal) (hC : C ≠ ⊤) :
    (∑' n : ℕ+, ENNReal.ofReal (((n : ℕ) : ℝ) ^ (-a)) * C) ≠ ⊤ := by
  by_cases hC0 : C = 0
  · simp [hC0]
  · have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-a)) :=
      Real.summable_nat_rpow.mpr (by linarith : -a < -1)
    have hsum' : Summable (fun n : ℕ+ => (n : ℝ) ^ (-a)) :=
      hsum.comp_injective Subtype.coe_injective
    have hsum'' :
        ∑' n : ℕ+, ENNReal.ofReal ((n : ℕ) ^ (-a)) =
          ENNReal.ofReal (∑' n : ℕ+, (n : ℝ) ^ (-a)) :=
      ((ENNReal.ofReal_tsum_of_nonneg
        fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum').symm
    have hfinite :
        ENNReal.ofReal (∑' n : ℕ+, (n : ℝ) ^ (-a)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    rw [show
      (∑' n : ℕ+, ENNReal.ofReal ((n : ℕ) ^ (-a)) * C) =
          (∑' n : ℕ+, ENNReal.ofReal ((n : ℕ) ^ (-a))) * C from
        ENNReal.tsum_mul_right]
    rw [hsum'']
    exact ENNReal.mul_ne_top hfinite hC

/-- **The payload**: absolute convergence of the positive-dilate Mellin comb
for the Gaussian target on `1 < p.re`. -/
private lemma eStarMellinAbsolute_explicitCCMLimitH {p : ℂ} (hp : 1 < p.re) :
    EStarMellinAbsolute explicitCCMLimitH p := by
  have hp0 : 0 < p.re := lt_trans one_pos hp
  refine ⟨fun n => dilate_aestronglyMeasurable hp0 n, ?_⟩
  rw [show
      (fun n : ℕ+ => ∫⁻ u : ℝ,
        ‖(u : ℂ) ^ (p - 1) • explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖ₑ
          ∂(volume.restrict (Set.Ioi 0))) =
      (fun n : ℕ+ => ENNReal.ofReal (((n : ℕ) : ℝ) ^ (-p.re)) *
        (∫⁻ v : ℝ, ‖(v : ℂ) ^ (p - 1) • explicitCCMLimitH v‖ₑ
          ∂(volume.restrict (Set.Ioi 0)))) from
    funext (fun n => dilate_lintegral_eq hp0 n)]
  refine ennreal_pnat_rpow_mul_tsum_ne_top p.re hp _ ?_
  have hbase := mellinConvergent_explicitCCMLimitH hp0
  change IntegrableOn
    (fun v : ℝ => (v : ℂ) ^ (p - 1) • explicitCCMLimitH v) (Set.Ioi 0) at hbase
  rw [← ofReal_integral_norm_eq_lintegral_enorm hbase]
  exact ENNReal.ofReal_ne_top

/-! ## Two-sided decay of `E_star explicitCCMLimitH` -/

private lemma summable_pnat_inv_four :
    Summable (fun n : ℕ+ => ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) := by
  have hnat : Summable (fun n : ℕ => (((n : ℝ)) ^ (4:ℕ))⁻¹) := by
    have h := Real.summable_nat_rpow.mpr (show (-4:ℝ) < -1 by norm_num)
    refine h.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      norm_num
    · have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      rw [show ((-4:ℝ)) = -((4:ℕ):ℝ) by norm_num,
        Real.rpow_neg hn'.le, Real.rpow_natCast]
  exact hnat.comp_injective Subtype.coe_injective

/-- The dilate-comb norm bound: `‖E_star h u‖ ≤ 33 * Z * sqrt u / u^4`. -/
private lemma E_star_norm_bound {u : ℝ} (hu : 0 < u) :
    ‖E_star explicitCCMLimitH u‖ ≤
      33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        (Real.sqrt u * ((u ^ (4:ℕ))⁻¹)) := by
  have hterm : ∀ n : ℕ+,
      ‖explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖ ≤
        33 * (u ^ (4:ℕ))⁻¹ * ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ := by
    intro n
    have hn : (0:ℝ) < ((n : ℕ) : ℝ) := by
      exact_mod_cast n.pos
    have hd := explicitCCMLimitH_inverse_four_decay
      (((n : ℕ) : ℝ) * u) (mul_pos hn hu)
    calc ‖explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖
        ≤ 33 / (((n : ℕ) : ℝ) * u) ^ 4 := hd
      _ = 33 * (u ^ (4:ℕ))⁻¹ * ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ := by
          rw [mul_pow]
          field_simp
  have hmaj : Summable (fun n : ℕ+ =>
      33 * (u ^ (4:ℕ))⁻¹ * ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) :=
    summable_pnat_inv_four.mul_left _
  have hsummable : Summable (fun n : ℕ+ =>
      ‖explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
  have htsum : ‖∑' n : ℕ+, explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖ ≤
      33 * (u ^ (4:ℕ))⁻¹ * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) := by
    calc ‖∑' n : ℕ+, explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖
        ≤ ∑' n : ℕ+, ‖explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖ :=
          norm_tsum_le_tsum_norm hsummable
      _ ≤ ∑' n : ℕ+, 33 * (u ^ (4:ℕ))⁻¹ * ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ :=
          hsummable.tsum_le_tsum hterm hmaj
      _ = 33 * (u ^ (4:ℕ))⁻¹ * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) :=
          tsum_mul_left
  unfold E_star
  rw [norm_mul,
    show ‖((Real.sqrt u : ℝ) : ℂ)‖ = Real.sqrt u by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg u)]]
  calc Real.sqrt u * ‖∑' n : ℕ+, explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖
      ≤ Real.sqrt u *
        (33 * (u ^ (4:ℕ))⁻¹ * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹)) :=
        mul_le_mul_of_nonneg_left htsum (Real.sqrt_nonneg u)
    _ = 33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        (Real.sqrt u * ((u ^ (4:ℕ))⁻¹)) := by ring

private lemma sqrt_mul_inv_pow_eq_rpow {u : ℝ} (hu : 0 < u) :
    Real.sqrt u * ((u ^ (4:ℕ))⁻¹) = u ^ (-(7/2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast u 4, ← Real.rpow_neg hu.le,
    ← Real.rpow_add hu]
  norm_num

/-- Decay at infinity: `E_star h = O(u^(-7/2))`. -/
private lemma E_star_isBigO_atTop :
    (E_star explicitCCMLimitH) =O[atTop]
      (fun u : ℝ => u ^ (-(7/2) : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹), ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
  calc ‖E_star explicitCCMLimitH u‖
      ≤ 33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        (Real.sqrt u * ((u ^ (4:ℕ))⁻¹)) := E_star_norm_bound hu0
    _ = 33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        u ^ (-(7/2) : ℝ) := by rw [sqrt_mul_inv_pow_eq_rpow hu0]

/-- Decay at zero via the exact public inversion: `E_star h = O(u^(7/2))`. -/
private lemma E_star_isBigO_zero :
    (E_star explicitCCMLimitH) =O[𝓝[>] (0:ℝ)]
      (fun u : ℝ => u ^ ((7:ℝ)/2)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹), ?_⟩
  have hmem : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, Set.mem_Ioi.mpr zero_lt_one, subset_rfl⟩
  filter_upwards [hmem] with u hu
  obtain ⟨hu0, hu1⟩ := hu
  have hinv0 : (0:ℝ) < u⁻¹ := inv_pos.mpr hu0
  have heq : E_star explicitCCMLimitH u = E_star explicitCCMLimitH u⁻¹ := by
    have h := E_star_explicitCCMLimitH_inv u⁻¹ hinv0
    rwa [inv_inv] at h
  have hrw : Real.sqrt u⁻¹ * (((u⁻¹) ^ (4:ℕ))⁻¹) = u ^ ((7:ℝ)/2) := by
    rw [sqrt_mul_inv_pow_eq_rpow hinv0,
      Real.inv_rpow hu0.le, Real.rpow_neg hu0.le, inv_inv]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _), heq]
  calc ‖E_star explicitCCMLimitH u⁻¹‖
      ≤ 33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        (Real.sqrt u⁻¹ * (((u⁻¹) ^ (4:ℕ))⁻¹)) := E_star_norm_bound hinv0
    _ = 33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        u ^ ((7:ℝ)/2) := by rw [hrw]

/-! ## Local integrability of `E_star explicitCCMLimitH` on `Ioi 0` -/

private lemma continuous_explicitCCMLimitH : Continuous explicitCCMLimitH := by
  unfold explicitCCMLimitH
  fun_prop

private lemma continuousOn_E_star :
    ContinuousOn (E_star explicitCCMLimitH) (Set.Ioi (0:ℝ)) := by
  intro u₀ hu₀
  apply ContinuousAt.continuousWithinAt
  have hu₀' : (0:ℝ) < u₀ := hu₀
  have hhalf : (0:ℝ) < u₀ / 2 := by linarith
  have hmem : u₀ ∈ Set.Ioi (u₀ / 2) := by
    simp only [Set.mem_Ioi]
    linarith
  have hnhds : Set.Ioi (u₀ / 2) ∈ 𝓝 u₀ := isOpen_Ioi.mem_nhds hmem
  have htsum : ContinuousOn
      (fun u : ℝ => ∑' n : ℕ+, explicitCCMLimitH (((n : ℕ) : ℝ) * u))
      (Set.Ioi (u₀ / 2)) := by
    apply continuousOn_tsum
      (u := fun n : ℕ+ =>
        33 * ((u₀ / 2) ^ (4:ℕ))⁻¹ * ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹)
    · intro n
      exact (continuous_explicitCCMLimitH.comp
        (continuous_const.mul continuous_id)).continuousOn
    · exact summable_pnat_inv_four.mul_left _
    · intro n u hu
      have hn : (0:ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
      have hu' : u₀ / 2 < u := hu
      have hu0 : (0:ℝ) < u := lt_trans hhalf hu'
      have hd := explicitCCMLimitH_inverse_four_decay
        (((n : ℕ) : ℝ) * u) (mul_pos hn hu0)
      have hmono : (((n : ℕ) : ℝ) * (u₀ / 2)) ^ 4 ≤ (((n : ℕ) : ℝ) * u) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_left hu'.le hn.le
      calc ‖explicitCCMLimitH (((n : ℕ) : ℝ) * u)‖
          ≤ 33 / (((n : ℕ) : ℝ) * u) ^ 4 := hd
        _ ≤ 33 / (((n : ℕ) : ℝ) * (u₀ / 2)) ^ 4 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hmono
        _ = 33 * ((u₀ / 2) ^ (4:ℕ))⁻¹ * ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ := by
            rw [mul_pow]
            field_simp
  have hsqrt : ContinuousAt (fun u : ℝ => ((Real.sqrt u : ℝ) : ℂ)) u₀ :=
    (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt
  have hAt : ContinuousAt
      (fun u : ℝ => ∑' n : ℕ+, explicitCCMLimitH (((n : ℕ) : ℝ) * u)) u₀ :=
    htsum.continuousAt hnhds
  exact hsqrt.mul hAt

private lemma locallyIntegrableOn_E_star :
    LocallyIntegrableOn (E_star explicitCCMLimitH) (Set.Ioi (0:ℝ)) :=
  continuousOn_E_star.locallyIntegrableOn measurableSet_Ioi

/-! ## The connected holomorphy strip -/

/-- The bounded connected strip `-3 < s.re < 3` containing both the product
half-plane seed and the image of the centered critical strip. -/
private def xiStrip : Set ℂ := {s : ℂ | -3 < s.re ∧ s.re < 3}

private lemma isOpen_xiStrip : IsOpen xiStrip := by
  have h : xiStrip = Complex.re ⁻¹' Set.Ioo (-3) 3 := by
    ext s
    simp [xiStrip, Set.mem_Ioo]
  rw [h]
  exact isOpen_Ioo.preimage Complex.continuous_re

private lemma preconnected_xiStrip : IsPreconnected xiStrip := by
  apply Convex.isPreconnected
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    simp [Complex.add_re]
  have hl2 : b * (-3) ≤ b * y.re := mul_le_mul_of_nonneg_left hy1.le hb
  have hl1 : a * (-3) ≤ a * x.re := mul_le_mul_of_nonneg_left hx1.le ha
  have hu1 : a * x.re ≤ a * 3 := mul_le_mul_of_nonneg_left hx2.le ha
  have hu2 : b * y.re ≤ b * 3 := mul_le_mul_of_nonneg_left hy2.le hb
  refine ⟨?_, ?_⟩ <;> rw [hre]
  · rcases lt_or_eq_of_le ha with ha' | ha0
    · have hstrict : a * (-3) < a * x.re := mul_lt_mul_of_pos_left hx1 ha'
      nlinarith
    · have hb' : 0 < b := by rw [← ha0] at hab; linarith
      have hstrict : b * (-3) < b * y.re := mul_lt_mul_of_pos_left hy1 hb'
      nlinarith
  · rcases lt_or_eq_of_le ha with ha' | ha0
    · have hstrict : a * x.re < a * 3 := mul_lt_mul_of_pos_left hx2 ha'
      nlinarith
    · have hb' : 0 < b := by rw [← ha0] at hab; linarith
      have hstrict : b * y.re < b * 3 := mul_lt_mul_of_pos_left hy2 hb'
      nlinarith

private lemma differentiableOn_mellin_E_star :
    DifferentiableOn ℂ (mellin (E_star explicitCCMLimitH)) xiStrip := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply mellin_differentiableAt_of_isBigO_rpow
    (a := 7/2) (b := -(7/2))
    locallyIntegrableOn_E_star E_star_isBigO_atTop
    (by linarith [hs.2] : s.re < 7/2)
    (by simpa using E_star_isBigO_zero)
    (by linarith [hs.1] : -(7/2) < s.re)

/-! ## The seed identity on the product half-plane -/

private lemma half_re_eq {s : ℂ} : (s + 1/2).re = s.re + 1/2 := by
  rw [show ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) by norm_num,
    Complex.add_re, Complex.ofReal_re]

/-- The half-plane identity: on `1/2 < s.re` the crosswalk product formula,
the exact Gaussian packet formula and the completed-zeta factorization give
`mellin (E_star h) s = (1/4) * riemannXi (s + 1/2)`. -/
private lemma seed_identity {s : ℂ} (hs : 1/2 < s.re) :
    mellin (E_star explicitCCMLimitH) s =
      (1/4 : ℂ) * riemannXi (s + 1/2) := by
  have hp1 : 1 < (s + 1/2).re := by
    rw [half_re_eq]
    linarith
  have hp0 : 0 < (s + 1/2).re := by linarith
  have hmain := mellin_E_star_eq_riemannZeta_mul hp1
    (eStarMellinAbsolute_explicitCCMLimitH hp1)
  rw [hmain, mellin_explicitCCMLimitH hp0]
  have hpne0 : s + 1/2 ≠ 0 := by
    intro h
    have h0 : (s + 1/2).re = 0 := by rw [h]; simp
    linarith [hp1, h0.symm.le]
  have hpne1 : s + 1/2 ≠ 1 := by
    intro h
    have h0 : (s + 1/2).re = 1 := by rw [h]; simp
    linarith [hp1]
  rw [riemannXi_eq_completedRiemannZeta hpne0 hpne1,
    completedRiemannZeta_eq_Gamma_mul_riemannZeta hp0]
  ring

/-! ## The identity across the strip -/

private lemma strip_identity :
    Set.EqOn (mellin (E_star explicitCCMLimitH))
      (fun s : ℂ => (1/4 : ℂ) * riemannXi (s + 1/2)) xiStrip := by
  have hUopen : IsOpen {s : ℂ | 1/2 < s.re} := by
    have h : {s : ℂ | 1/2 < s.re} = Complex.re ⁻¹' Set.Ioi (1/2) := rfl
    rw [h]
    exact isOpen_Ioi.preimage Complex.continuous_re
  have hone : (1:ℂ) ∈ {s : ℂ | 1/2 < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.one_re]
    norm_num
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (differentiableOn_mellin_E_star.analyticOnNhd isOpen_xiStrip)
    (((differentiable_riemannXi.comp
        (differentiable_id.add_const (1/2 : ℂ))).const_mul
      (1/4 : ℂ)).differentiableOn.analyticOnNhd isOpen_xiStrip)
    preconnected_xiStrip
    (show (1:ℂ) ∈ xiStrip by
      constructor <;> simp only [Complex.one_re] <;> norm_num)
    (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hone)
      (fun s hs => seed_identity hs))

/-! ## The functional equation of the project `riemannXi` -/

private lemma riemannXi_one_sub (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-! ## The public theorems -/

/-- **L73.5, unscaled.**  On the open centered critical strip, the Mellin
transform of the `E_star`-comb of the explicit CCM limit target equals
**one quarter** of the production `centeredXi`. -/
theorem mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi
    {z : ℂ} (hz : z ∈ centeredCriticalStrip) :
    mellin (E_star explicitCCMLimitH) (-Complex.I * z) =
      (1 / 4 : ℂ) * centeredXi z := by
  have him : |z.im| < 1/2 := hz
  obtain ⟨him1, him2⟩ := abs_lt.mp him
  have hre : (-Complex.I * z).re = z.im := by
    simp [Complex.mul_re]
  have hmem : (-Complex.I * z) ∈ xiStrip := by
    refine ⟨?_, ?_⟩ <;> rw [hre]
    · linarith
    · linarith
  have h := strip_identity hmem
  simp only at h
  rw [h]
  congr 1
  have harg : -Complex.I * z + 1/2 =
      (1:ℂ) - ((1/2 : ℂ) + Complex.I * z) := by ring
  rw [centeredXi, harg, riemannXi_one_sub]

/-- **L73.5, scaled.**  The exact factor-four corollary: after one factor of
four on the target, the Mellin transform equals `centeredXi` with
coefficient exactly one.  Pure linearity of `E_star`, `tsum` and `mellin` —
the scalar is not hidden in any definition. -/
theorem mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi
    {z : ℂ} (hz : z ∈ centeredCriticalStrip) :
    mellin (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
        (-Complex.I * z) =
      centeredXi z := by
  have hEfun : E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x) =
      fun u : ℝ => (4 : ℂ) * E_star explicitCCMLimitH u := by
    funext u
    unfold E_star
    rw [tsum_mul_left]
    ring
  rw [hEfun]
  have hlin : mellin (fun u : ℝ => (4:ℂ) * E_star explicitCCMLimitH u)
      (-Complex.I * z) =
      (4:ℂ) * mellin (E_star explicitCCMLimitH) (-Complex.I * z) := by
    simpa [smul_eq_mul] using
      mellin_const_smul (E_star explicitCCMLimitH) (-Complex.I * z)
        (c := (4:ℂ))
  rw [hlin, mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi hz]
  ring

#print axioms mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi
#print axioms mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi

end Q3.RouteB.D0Pstar

end
