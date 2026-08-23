import Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinNormalization
import Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex MeasureTheory Asymptotics Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# L73.6 — the explicit CCM limit outer Mellin tail, uniform on the strip

Floor `L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS`
of verdict `04b95c7e`, proved in the STRONGER whole-strip form the verdict
authorizes: the factor-four outer Mellin tail converges to zero uniformly on
the entire open `centeredCriticalStrip`, not only on closed substrips.

The public object carries the **factor-four** target `E_star (4*h)` — the
same function whose Mellin transform L73.5 identified with `centeredXi`.
An unscaled outer-tail theorem would estimate a different function and would
fail the C04/C10 object audit.

Quantitative content: the private common rate
`‖T_k(z)‖ ≤ 88 * Z4 / lambda_k^3` with `Z4 = ∑ n^(-4)`, derived from the
local inverse-four decay (`u^(-7/2)` at infinity, `u^(7/2)` at zero via the
exact public inversion) and the strip exponent guard `y - 9/2 < -4` and
`2 < y + 5/2` for `|y| < 1/2`.  The constant is source-derived, not fitted.
Since `lambda_k^2 = k + 2`, the rate vanishes along the schedule.

Deliberately NOT here: closed-substrip source convergence (L73.7) and the
port inhabitant (L73.8).

LEDGER:
  CLOSES: [EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS]
  OPENS:  []
-/

/-! ## The mandatory coordinate and exponent guards -/

/-- The exact coordinate: `(-I*z).re = z.im`.  A sign error here would swap
the two tail exponent ledgers. -/
private lemma neg_I_mul_re (z : ℂ) : (-Complex.I * z).re = z.im := by
  simp [Complex.mul_re]

/-- **The plant** (verbatim from the verdict): both tail exponents stay on
the decaying side simultaneously on the open centered strip. -/
private theorem centeredStrip_tail_exponent_guard_plant
    {y : ℝ} (hy : |y| < 1 / 2) :
    y - 9 / 2 < -4 ∧ 2 < y + 5 / 2 := by
  have h := abs_lt.mp hy
  constructor <;> linarith

/-! ## Local inverse-four decay and the comb bound (private upstream) -/

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

/-! ## Factor-four comb bounds on both sides -/

/-- The factor-four target comb is four times the unscaled comb. -/
private lemma E_star_four_mul_eq :
    E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x) =
      fun u : ℝ => (4 : ℂ) * E_star explicitCCMLimitH u := by
  funext u
  unfold E_star
  rw [tsum_mul_left]
  ring

/-- Decay of the factor-four comb at infinity, in `rpow` form, for all
positive `u`. -/
private lemma factorFour_norm_le_rpow_top {u : ℝ} (hu : 0 < u) :
    ‖E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x) u‖ ≤
      132 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) * u ^ (-(7/2) : ℝ) := by
  rw [E_star_four_mul_eq, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
  have h := E_star_norm_bound hu
  rw [sqrt_mul_inv_pow_eq_rpow hu] at h
  calc 4 * ‖E_star explicitCCMLimitH u‖
      ≤ 4 * (33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        u ^ (-(7/2) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 132 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        u ^ (-(7/2) : ℝ) := by ring

/-- Decay of the factor-four comb at zero, in `rpow` form, for all positive
`u`, via the exact public inversion. -/
private lemma factorFour_norm_le_rpow_bot {u : ℝ} (hu : 0 < u) :
    ‖E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x) u‖ ≤
      132 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) * u ^ ((7:ℝ)/2) := by
  rw [E_star_four_mul_eq, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
  have hinv0 : (0:ℝ) < u⁻¹ := inv_pos.mpr hu
  have heq : E_star explicitCCMLimitH u = E_star explicitCCMLimitH u⁻¹ := by
    have h := E_star_explicitCCMLimitH_inv u⁻¹ hinv0
    rwa [inv_inv] at h
  have h := E_star_norm_bound hinv0
  rw [sqrt_mul_inv_pow_eq_rpow hinv0,
    Real.inv_rpow hu.le, Real.rpow_neg hu.le, inv_inv] at h
  rw [heq]
  calc 4 * ‖E_star explicitCCMLimitH u⁻¹‖
      ≤ 4 * (33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        u ^ ((7:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 132 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        u ^ ((7:ℝ)/2) := by ring

/-! ## Schedule facts -/

private lemma lambda_ge_one (k : ℕ) : 1 ≤ selectedFerrersPaperLambda k := by
  rw [selectedFerrersPaperLambda,
    show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)

private lemma lambda_pos (k : ℕ) : 0 < selectedFerrersPaperLambda k :=
  lt_of_lt_of_le one_pos (lambda_ge_one k)

/-! ## The public outer tail -/

/-- **The factor-four outer Mellin tail** (verbatim shape from the verdict):
the two omitted Mellin pieces of the factor-four target at the exact
coordinate `s = -I*z`. -/
noncomputable def selectedFerrersFactorFourExplicitLimitMellinOuterTail
    (k : ℕ) (z : ℂ) : ℂ :=
  lowerMellinTail (selectedFerrersPaperLambda k)
      (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
      (-Complex.I * z) +
    upperMellinTail (selectedFerrersPaperLambda k)
      (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
      (-Complex.I * z)

/-! ## The two tail bounds -/

/-- The upper omitted tail is bounded by `44 * Z4 / lambda^3`. -/
private lemma upper_tail_bound (k : ℕ) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    ‖upperMellinTail (selectedFerrersPaperLambda k)
        (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
        (-Complex.I * z)‖ ≤
      44 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) /
        (selectedFerrersPaperLambda k) ^ 3 := by
  set lam : ℝ := selectedFerrersPaperLambda k with hlam
  set Z : ℝ := ∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ with hZ
  have hZnn : 0 ≤ Z := tsum_nonneg fun n => by positivity
  have hlam1 : 1 ≤ lam := lambda_ge_one k
  have hlam0 : 0 < lam := lambda_pos k
  have hguard := centeredStrip_tail_exponent_guard_plant
    (show |z.im| < 1/2 from hz)
  set F : ℝ → ℂ := E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x)
    with hF
  set g : ℝ → ℝ := (Set.Ioi lam).indicator
    (fun u : ℝ => 132 * Z * u ^ (-(4:ℝ))) with hg
  have hgint : Integrable g (volume.restrict (Set.Ioi 0)) := by
    apply MeasureTheory.Integrable.restrict
    rw [hg, integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-4:ℝ) < -1) hlam0).const_mul (132 * Z)
  have hdom : ∀ u ∈ Set.Ioi (0:ℝ),
      ‖(u : ℂ) ^ ((-Complex.I * z) - 1) •
        (Set.Ioi lam).indicator F u‖ ≤ g u := by
    intro u hu
    by_cases hmem : u ∈ Set.Ioi lam
    · have hulam : lam < u := hmem
      have hu1 : (1:ℝ) ≤ u := le_trans hlam1 hulam.le
      have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu1
      rw [Set.indicator_of_mem hmem, hg, Set.indicator_of_mem hmem,
        norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      have hre : ((-Complex.I * z) - 1).re = z.im - 1 := by
        rw [Complex.sub_re, neg_I_mul_re, Complex.one_re]
      rw [hre]
      have hFb := factorFour_norm_le_rpow_top hu0
      rw [← hZ] at hFb
      calc u ^ (z.im - 1) * ‖F u‖
          ≤ u ^ (z.im - 1) * (132 * Z * u ^ (-(7/2) : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hFb (Real.rpow_nonneg hu0.le _)
        _ = 132 * Z * u ^ (z.im - 1 + -(7/2)) := by
            rw [Real.rpow_add hu0]
            ring
        _ ≤ 132 * Z * u ^ (-(4:ℝ)) := by
            apply mul_le_mul_of_nonneg_left ?_ (by positivity)
            apply Real.rpow_le_rpow_of_exponent_le hu1
            linarith [hguard.1]
    · rw [Set.indicator_of_notMem hmem, hg, Set.indicator_of_notMem hmem]
      simp
  rw [upperMellinTail]
  have hle : ‖mellin ((Set.Ioi lam).indicator F) (-Complex.I * z)‖ ≤
      ∫ u in Set.Ioi (0:ℝ), g u := by
    simp only [mellin]
    apply norm_integral_le_of_norm_le hgint
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hdom)
  refine le_trans hle ?_
  have hIoi : Set.Ioi (0:ℝ) ∩ Set.Ioi lam = Set.Ioi lam :=
    Set.inter_eq_right.mpr (fun u hu => lt_trans hlam0 hu)
  rw [hg, setIntegral_indicator measurableSet_Ioi, hIoi,
    MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-4:ℝ) < -1) hlam0]
  have hpow : lam ^ ((-4:ℝ) + 1) = (lam ^ (3:ℕ))⁻¹ := by
    rw [show (-4:ℝ) + 1 = -((3:ℕ):ℝ) by norm_num,
      Real.rpow_neg hlam0.le, Real.rpow_natCast]
  rw [hpow]
  have hl3 : (0:ℝ) < lam ^ (3:ℕ) := pow_pos hlam0 3
  have hfinal : 132 * Z * (-(lam ^ (3:ℕ))⁻¹ / (-4 + 1)) = 44 * Z / lam ^ 3 := by
    have hne : (lam ^ (3:ℕ) : ℝ) ≠ 0 := hl3.ne'
    field_simp
    ring
  exact le_of_eq hfinal

/-- The lower omitted tail is bounded by `44 * Z4 / lambda^3`. -/
private lemma lower_tail_bound (k : ℕ) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    ‖lowerMellinTail (selectedFerrersPaperLambda k)
        (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
        (-Complex.I * z)‖ ≤
      44 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) /
        (selectedFerrersPaperLambda k) ^ 3 := by
  set lam : ℝ := selectedFerrersPaperLambda k with hlam
  set Z : ℝ := ∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ with hZ
  have hZnn : 0 ≤ Z := tsum_nonneg fun n => by positivity
  have hlam1 : 1 ≤ lam := lambda_ge_one k
  have hlam0 : 0 < lam := lambda_pos k
  have hinv1 : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam1
  have hinv0 : (0:ℝ) < lam⁻¹ := inv_pos.mpr hlam0
  have hguard := centeredStrip_tail_exponent_guard_plant
    (show |z.im| < 1/2 from hz)
  set F : ℝ → ℂ := E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x)
    with hF
  set g : ℝ → ℝ := (Set.Ioo (0:ℝ) lam⁻¹).indicator
    (fun u : ℝ => 132 * Z * u ^ (2:ℕ)) with hg
  have hgint : Integrable g (volume.restrict (Set.Ioi 0)) := by
    apply MeasureTheory.Integrable.restrict
    rw [hg, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono_set (t := Set.Ioc (0:ℝ) lam⁻¹)
    · exact (continuous_const.mul (continuous_pow 2)).integrableOn_Ioc
    · exact fun u hu => ⟨hu.1, hu.2.le⟩
  have hdom : ∀ u ∈ Set.Ioi (0:ℝ),
      ‖(u : ℂ) ^ ((-Complex.I * z) - 1) •
        (Set.Iio lam⁻¹).indicator F u‖ ≤ g u := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    by_cases hmem : u ∈ Set.Iio lam⁻¹
    · have hmem' : u ∈ Set.Ioo (0:ℝ) lam⁻¹ := ⟨hu0, hmem⟩
      have hu1 : u ≤ 1 := le_trans (le_of_lt hmem) hinv1
      rw [Set.indicator_of_mem hmem, hg, Set.indicator_of_mem hmem',
        norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      have hre : ((-Complex.I * z) - 1).re = z.im - 1 := by
        rw [Complex.sub_re, neg_I_mul_re, Complex.one_re]
      rw [hre]
      have hFb := factorFour_norm_le_rpow_bot hu0
      rw [← hZ] at hFb
      calc u ^ (z.im - 1) * ‖F u‖
          ≤ u ^ (z.im - 1) * (132 * Z * u ^ ((7:ℝ)/2)) := by
            apply mul_le_mul_of_nonneg_left hFb (Real.rpow_nonneg hu0.le _)
        _ = 132 * Z * u ^ (z.im - 1 + (7:ℝ)/2) := by
            rw [Real.rpow_add hu0]
            ring
        _ ≤ 132 * Z * u ^ (((2:ℕ):ℝ)) := by
            apply mul_le_mul_of_nonneg_left ?_ (by positivity)
            apply Real.rpow_le_rpow_of_exponent_ge hu0 hu1
            push_cast
            linarith [hguard.2]
        _ = 132 * Z * u ^ (2:ℕ) := by
            rw [Real.rpow_natCast]
    · have hmem' : u ∉ Set.Ioo (0:ℝ) lam⁻¹ := fun hc => hmem hc.2
      rw [Set.indicator_of_notMem hmem, hg, Set.indicator_of_notMem hmem']
      simp
  rw [lowerMellinTail]
  have hle : ‖mellin ((Set.Iio lam⁻¹).indicator F) (-Complex.I * z)‖ ≤
      ∫ u in Set.Ioi (0:ℝ), g u := by
    simp only [mellin]
    apply norm_integral_le_of_norm_le hgint
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hdom)
  refine le_trans hle ?_
  have hIoo : Set.Ioi (0:ℝ) ∩ Set.Ioo (0:ℝ) lam⁻¹ = Set.Ioo (0:ℝ) lam⁻¹ :=
    Set.inter_eq_right.mpr (fun u hu => hu.1)
  rw [hg, setIntegral_indicator measurableSet_Ioo, hIoo,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hinv0.le,
    intervalIntegral.integral_const_mul, integral_pow]
  have hval : (132 : ℝ) * Z * (((lam⁻¹) ^ (2 + 1) - 0 ^ (2 + 1)) / (((2:ℕ):ℝ) + 1)) =
      44 * Z * (lam ^ (3:ℕ))⁻¹ := by
    rw [← inv_pow]
    norm_num
    ring
  rw [hval]
  rw [div_eq_mul_inv]

/-! ## The required private rate -/

/-- **The common rate**: `88 * Z4 / lambda^3` on the whole open centered
strip, before any topology. -/
private lemma factorFour_outerTail_norm_le_inv_cube (k : ℕ) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    ‖selectedFerrersFactorFourExplicitLimitMellinOuterTail k z‖ ≤
      88 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) /
        (selectedFerrersPaperLambda k) ^ 3 := by
  rw [selectedFerrersFactorFourExplicitLimitMellinOuterTail]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := lower_tail_bound k hz
  have h2 := upper_tail_bound k hz
  have hsum := add_le_add h1 h2
  calc ‖lowerMellinTail (selectedFerrersPaperLambda k)
        (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
        (-Complex.I * z)‖ +
      ‖upperMellinTail (selectedFerrersPaperLambda k)
        (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
        (-Complex.I * z)‖
      ≤ 44 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) /
          (selectedFerrersPaperLambda k) ^ 3 +
        44 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) /
          (selectedFerrersPaperLambda k) ^ 3 := hsum
    _ = 88 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) /
          (selectedFerrersPaperLambda k) ^ 3 := by ring

/-! ## The public uniform-convergence theorem -/

/-- **L73.6.**  The factor-four outer Mellin tail tends to zero uniformly on
the entire open centered critical strip along the selected schedule.  This
is stronger than the catalog's closed-substrip requirement and closes it. -/
theorem selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn :
    TendstoUniformlyOn
      selectedFerrersFactorFourExplicitLimitMellinOuterTail
      (fun _ : ℂ => 0)
      Filter.atTop
      centeredCriticalStrip := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set Z : ℝ := ∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ with hZ
  have hZnn : 0 ≤ Z := tsum_nonneg fun n => by positivity
  have h0 : Tendsto (fun n : ℕ => 88 * Z / (n:ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hcomp : Tendsto (fun k : ℕ => 88 * Z / (((k + 2 : ℕ)):ℝ)) atTop
      (nhds 0) := h0.comp (tendsto_add_atTop_nat 2)
  have hev : ∀ᶠ k in (atTop : Filter ℕ),
      88 * Z / (((k + 2 : ℕ)):ℝ) < ε :=
    hcomp.eventually_lt_const hε
  filter_upwards [hev] with k hk z hz
  rw [dist_zero_left]
  have hb := factorFour_outerTail_norm_le_inv_cube k hz
  rw [← hZ] at hb
  have hlam1 := lambda_ge_one k
  have hlam0 := lambda_pos k
  have hsq : (selectedFerrersPaperLambda k) ^ (2:ℕ) = (((k + 2 : ℕ)):ℝ) :=
    selectedFerrersPaperLambda_sq k
  have hchain : 88 * Z / (selectedFerrersPaperLambda k) ^ 3 ≤
      88 * Z / (((k + 2 : ℕ)):ℝ) := by
    rw [← hsq]
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hlam0 2)
    exact pow_le_pow_right₀ hlam1 (by omega)
  exact lt_of_le_of_lt (le_trans hb hchain) hk

#print axioms selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn

end Q3.RouteB.D0Pstar

end
