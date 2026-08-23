import Q3.Proofs.RouteB.G6N1SelectedFerrersCommutatorResidualDefect

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Complex Matrix Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# H2a.4.1b.3c.0 — the selected Ferrers center-coefficient inverse-log floor

Floor `H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR`
of verdict `580e0a00`.

Pointwise nonvanishing of the center coefficient supplies legal division,
not an asymptotic lower envelope — the first plant records exactly this
kill.  This floor closes the center normalization before any ratio-rate
work:

* the **exact anchor identity**
  `L_k·|q₀|² = |s_k·Gwin_k(0)|² / ‖s_k·P(g_k)‖²` — the source scale stays
  inside the scaled projected vector, no fitted normalizer;
* the **source-derived inverse-log floor**: from the exact `hmode`/`hχ`
  inputs, eventually `c_center ≤ L_k·|q₀|²` — the numerator is floored by
  the selected-shell convergence at `z = 0` against `centeredXi(0) ≠ 0`,
  the denominator is capped by the L73 physical error plus the **global**
  `L²(d*u)` norm of the factor-four target obtained from its exact
  two-sided `u^{∓7/2}` decay (a `λ⁵`-window bound is NOT used — the
  second plant records that the global cap is load-bearing);
* the **denominator-free receiver**: `L_k·η_k·‖Γ_k‖² → 0` forces the
  ratified weighted-residual consumer `√η_k·√E_res,k → 0`, through the
  floor and the existing 3B ratio receiver — `R_k → 0` is never assumed
  separately.

The remaining analytic wall is the log-weighted commutator energy source
rate (`H2A_4_1B_3C_1`); it is NOT proved here.

Deliberately NOT here: any `Γ`-energy rate, beta-energy growth, sector
floors, simple ground, Theorem 5.10.

LEDGER:
  CLOSES: [SELECTED_FERRERS_CENTER_COEFFICIENT_ANCHOR_IDENTITY,
           SELECTED_FERRERS_CENTER_COEFFICIENT_INVERSE_LOG_FLOOR,
           SELECTED_FERRERS_RATIO_DENOMINATOR_REMOVAL,
           SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_TO_WEIGHTED_RESIDUAL_RECEIVER]
  OPENS:  [SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_ENERGY_SOURCE_RATE]
-/

/-! ## The two mandatory plants -/

/-- **Plant 1.**  Pointwise center nonvanishing does not give an
inverse-log floor: the unit rows `q_n = ((n+2)⁻¹, √(1−(n+2)⁻²))` have
nonzero center coefficient at every index, yet with the growing weight
`L_n = n+2` the product `L_n·|q₀,n|² = (n+2)⁻¹` tends to zero.  The
inference `q₀ ≠ 0 → inverse-log floor` is dead. -/
private theorem pointwise_center_nonzero_without_log_floor_plant :
    ∃ (L : ℕ → ℝ) (q : ℕ → Fin 2 → ℂ),
      (∀ n, 1 ≤ L n) ∧
      (∀ n, star (q n) ⬝ᵥ q n = 1) ∧
      (∀ n, q n 0 ≠ 0) ∧
      Filter.Tendsto (fun n => L n * Complex.normSq (q n 0))
        Filter.atTop (nhds 0) := by
  classical
  set c : ℕ → ℝ := fun n => ((n:ℝ) + 2)⁻¹ with hc
  set b : ℕ → ℝ := fun n => Real.sqrt (1 - c n ^ 2) with hb
  have hc0 : ∀ n, 0 < c n := by
    intro n
    have : (0:ℝ) < (n : ℝ) + 2 := by positivity
    exact inv_pos.mpr this
  have hcsq1 : ∀ n, c n ^ 2 ≤ 1 := by
    intro n
    have h2 : (1:ℝ) ≤ (n : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hle : c n ≤ 1 := by
      rw [hc]
      calc ((n:ℝ) + 2)⁻¹ ≤ (1:ℝ)⁻¹ :=
            (inv_le_inv₀ (by linarith) (by norm_num)).mpr h2
        _ = 1 := by norm_num
    nlinarith [hc0 n]
  have hbsq : ∀ n, b n ^ 2 = 1 - c n ^ 2 := by
    intro n
    rw [hb]
    exact Real.sq_sqrt (by nlinarith [hcsq1 n])
  refine ⟨fun n => (n:ℝ) + 2,
    fun n => ![((c n : ℝ) : ℂ), ((b n : ℝ) : ℂ)], ?_, ?_, ?_, ?_⟩
  · intro n
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · intro n
    have h : star (![((c n : ℝ) : ℂ), ((b n : ℝ) : ℂ)] : Fin 2 → ℂ) ⬝ᵥ
        ![((c n : ℝ) : ℂ), ((b n : ℝ) : ℂ)] =
        (((c n ^ 2 + b n ^ 2 : ℝ)) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_two, ← Complex.ofReal_mul]
      push_cast
      ring
    rw [h, hbsq n]
    norm_num
  · intro n
    show ((c n : ℝ) : ℂ) ≠ 0
    exact_mod_cast (hc0 n).ne'
  · have hval : ∀ n : ℕ, ((n:ℝ) + 2) *
        Complex.normSq (((c n : ℝ) : ℂ)) = c n := by
      intro n
      rw [Complex.normSq_ofReal, hc]
      field_simp
    have hclim : Filter.Tendsto c Filter.atTop (nhds 0) := by
      rw [hc]
      have h1 : Filter.Tendsto (fun n : ℕ => ((n:ℝ) + 2))
          Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact h1.inv_tendsto_atTop
    refine hclim.congr fun n => ?_
    show c n = ((n:ℝ) + 2) *
      Complex.normSq ((![((c n : ℝ) : ℂ), ((b n : ℝ) : ℂ)] : Fin 2 → ℂ) 0)
    rw [show (![((c n : ℝ) : ℂ), ((b n : ℝ) : ℂ)] : Fin 2 → ℂ) 0 =
      ((c n : ℝ) : ℂ) from rfl]
    rw [hval n]

/-- **Plant 2.**  The anchor alone does not force the center floor: with
`anchor_n = 1` and a diverging scaled projected norm `denom_n = (n+1)²`,
the anchor-identity ratio `anchor/denom` — the exact value of
`L·|q₀|²` — tends to zero.  The global upper bound on the scaled
projection is load-bearing. -/
private theorem anchor_without_scaled_projection_upper_bound_does_not_force_center_floor_plant :
    ∃ (anchor denom : ℕ → ℝ),
      (∀ n, anchor n = 1) ∧
      Filter.Tendsto denom Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n => anchor n / denom n)
        Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => ((n:ℝ) + 1) ^ 2)
      Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ⟨fun _ => 1, fun n => ((n:ℝ) + 1) ^ 2, fun _ => rfl, h1, ?_⟩
  have h2 := h1.inv_tendsto_atTop
  refine h2.congr fun n => ?_
  show ((fun n : ℕ => ((n:ℝ) + 1) ^ 2)⁻¹) n = 1 / (((n:ℝ) + 1) ^ 2)
  rw [Pi.inv_apply, one_div]
/-! ## Copied private groundwork (upstream copies are private) -/

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


/-- The factor-four target comb is four times the unscaled comb. -/
private lemma E_star_four_mul_eq :
    E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x) =
      fun u : ℝ => (4 : ℂ) * E_star explicitCCMLimitH u := by
  funext u
  unfold E_star
  rw [tsum_mul_left]
  ring

/-! ## Window and schedule facts -/

private lemma lambda_paper_eq_lambda_m (σ : ℕ) :
    lambda_m (selectedFerrersPreAnchorIndex σ) =
      selectedFerrersPaperLambda σ :=
  (selectedFerrersPreAnchorPair_lambda_eq σ).symm.trans
    (selectedFerrersPreAnchorPair_lambda_eq_paperLambda σ)

private lemma lambda_m_pre_ge_one (σ : ℕ) :
    1 ≤ lambda_m (selectedFerrersPreAnchorIndex σ) := by
  rw [lambda_paper_eq_lambda_m, selectedFerrersPaperLambda,
    show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)

private lemma lambda_m_pre_pos (σ : ℕ) :
    0 < lambda_m (selectedFerrersPreAnchorIndex σ) :=
  lt_of_lt_of_le one_pos (lambda_m_pre_ge_one σ)

/-! ## The window L² error integral -/

private lemma window_l2_integral_le (i : PairIndex)
    (hl : 1 ≤ lambda_m i)
    (err : ℝ → ℂ) (Cf : ℝ) (_hCf : 0 ≤ Cf)
    (herr : ∀ u ∈ I_m i, ‖err u‖ ≤ Cf / (lambda_m i * Real.sqrt u)) :
    ∫ u, Complex.normSq (err u) ∂(dStar.restrict (I_m i)) ≤
      Cf ^ 2 / lambda_m i := by
  classical
  set lam : ℝ := lambda_m i with hlam
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hl
  have hinv0 : 0 < lam⁻¹ := by positivity
  have hinvle : lam⁻¹ ≤ lam := le_trans (inv_le_one_of_one_le₀ hl) hl
  have hwmeas : Measurable (fun u : ℝ => ENNReal.ofReal u⁻¹) :=
    measurable_inv.ennreal_ofReal
  have hrestrict : dStar.restrict (I_m i) =
      (volume.restrict (I_m i)).withDensity
        (fun u : ℝ => ENNReal.ofReal u⁻¹) := by
    unfold dStar I_m
    exact restrict_withDensity measurableSet_Icc _
  rw [hrestrict,
    integral_withDensity_eq_integral_toReal_smul hwmeas
      (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top)
      (fun u => Complex.normSq (err u))]
  have hdom : ∀ u ∈ I_m i,
      (ENNReal.ofReal u⁻¹).toReal • Complex.normSq (err u) ≤
        Cf ^ 2 / lam ^ 2 * (u⁻¹ * u⁻¹) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hinv0 hu.1
    have hns : Complex.normSq (err u) = ‖err u‖ ^ 2 :=
      (Complex.normSq_eq_norm_sq (err u))
    have hbd : ‖err u‖ ^ 2 ≤ (Cf / (lam * Real.sqrt u)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (herr u hu) 2
    have hsq : (Cf / (lam * Real.sqrt u)) ^ 2 = Cf ^ 2 / (lam ^ 2 * u) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hu0.le]
    rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ u⁻¹)]
    calc u⁻¹ * Complex.normSq (err u)
        ≤ u⁻¹ * (Cf ^ 2 / (lam ^ 2 * u)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hns, ← hsq]
          exact hbd
      _ = Cf ^ 2 / lam ^ 2 * (u⁻¹ * u⁻¹) := by
          field_simp
  have hmaj : IntegrableOn
      (fun u : ℝ => Cf ^ 2 / lam ^ 2 * (u⁻¹ * u⁻¹)) (I_m i) := by
    apply Integrable.const_mul
    have hinv : ContinuousOn (fun u : ℝ => u⁻¹)
        (Set.Icc lam⁻¹ lam) := by
      apply ContinuousOn.inv₀ continuousOn_id
      intro u hu
      exact ne_of_gt (lt_of_lt_of_le hinv0 hu.1)
    exact (hinv.mul hinv).integrableOn_Icc
  have hle : (∫ u, (ENNReal.ofReal u⁻¹).toReal •
      Complex.normSq (err u) ∂(volume.restrict (I_m i))) ≤
      ∫ u, Cf ^ 2 / lam ^ 2 * (u⁻¹ * u⁻¹)
        ∂(volume.restrict (I_m i)) := by
    apply integral_mono_of_nonneg
    · apply ae_of_all
      intro u
      exact mul_nonneg ENNReal.toReal_nonneg (Complex.normSq_nonneg _)
    · exact hmaj
    · rw [Filter.EventuallyLE,
        show I_m i = Set.Icc (lambda_m i)⁻¹ (lambda_m i) from rfl,
        ae_restrict_iff' measurableSet_Icc]
      exact ae_of_all _ (by
        intro u hu
        exact hdom u hu)
  refine le_trans hle ?_
  rw [MeasureTheory.integral_const_mul]
  have hval_le : (∫ u in I_m i, u⁻¹ * u⁻¹ ∂volume) ≤ lam := by
    have hcongr : (∫ u in I_m i, u⁻¹ * u⁻¹ ∂volume) =
        ∫ u in Set.Ioo lam⁻¹ lam, u ^ (-2 : ℝ) ∂volume := by
      unfold I_m
      rw [← hlam, MeasureTheory.integral_Icc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      have hu0 : 0 < u := lt_trans hinv0 hu.1
      show u⁻¹ * u⁻¹ = u ^ (-2 : ℝ)
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg hu0.le,
        Real.rpow_natCast, sq, mul_inv]
    rw [hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hinvle]
    have hnmem : (0:ℝ) ∉ Set.uIcc lam⁻¹ lam := by
      intro hmem
      rw [Set.uIcc_of_le hinvle] at hmem
      exact absurd hmem.1 (not_le.mpr hinv0)
    rw [integral_rpow (Or.inr ⟨by norm_num, hnmem⟩)]
    have hev : (lam ^ ((-2:ℝ) + 1) - (lam⁻¹) ^ ((-2:ℝ) + 1)) /
        ((-2:ℝ) + 1) = lam - lam⁻¹ := by
      rw [show ((-2:ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one,
        Real.rpow_neg_one, inv_inv]
      ring
    rw [hev]
    linarith [hinv0.le]
  calc Cf ^ 2 / lam ^ 2 * ∫ u in I_m i, u⁻¹ * u⁻¹ ∂volume
      ≤ Cf ^ 2 / lam ^ 2 * lam :=
        mul_le_mul_of_nonneg_left hval_le (by positivity)
    _ = Cf ^ 2 / lam := by
        field_simp

/-! ## General window facts and the target membership -/

private lemma lambda_m_gen_pos (i : PairIndex) : 0 < lambda_m i := by
  have h := i.hm
  unfold lambda_m
  apply Real.sqrt_pos.mpr
  exact_mod_cast (by omega : 0 < i.m)

private lemma lambda_m_gen_ge_one (i : PairIndex) : 1 ≤ lambda_m i := by
  have h := i.hm
  unfold lambda_m
  rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  apply Real.sqrt_le_sqrt
  exact_mod_cast (by omega : 1 ≤ i.m)

private lemma Im_subset_Ioi (i : PairIndex) : I_m i ⊆ Set.Ioi (0:ℝ) := by
  intro u hu
  have h0 : (0:ℝ) < (lambda_m i)⁻¹ := by
    have := lambda_m_gen_pos i
    positivity
  exact lt_of_lt_of_le h0 hu.1

private lemma isFiniteMeasure_dStar_Im (i : PairIndex) :
    IsFiniteMeasure (dStar.restrict (I_m i)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  have hlam0 := lambda_m_gen_pos i
  have hinv0 : (0:ℝ) < (lambda_m i)⁻¹ := by positivity
  show dStar (I_m i) < ⊤
  unfold dStar I_m
  rw [withDensity_apply _ measurableSet_Icc]
  calc (∫⁻ u in Set.Icc (lambda_m i)⁻¹ (lambda_m i),
        ENNReal.ofReal u⁻¹ ∂volume)
      ≤ ∫⁻ _u in Set.Icc (lambda_m i)⁻¹ (lambda_m i),
          ENNReal.ofReal (lambda_m i) ∂volume := by
        apply setLIntegral_mono measurable_const
        intro u hu
        apply ENNReal.ofReal_le_ofReal
        calc u⁻¹ ≤ ((lambda_m i)⁻¹)⁻¹ := by
              exact (inv_le_inv₀ (lt_of_lt_of_le hinv0 hu.1) hinv0).mpr hu.1
          _ = lambda_m i := inv_inv _
      _ = ENNReal.ofReal (lambda_m i) *
          volume (Set.Icc (lambda_m i)⁻¹ (lambda_m i)) := by
          rw [setLIntegral_const]
      _ < ⊤ := by
          apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          rw [Real.volume_Icc]
          exact ENNReal.ofReal_lt_top

private lemma continuousOn_G_Im (i : PairIndex) :
    ContinuousOn (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
      (I_m i) := by
  rw [E_star_four_mul_eq]
  exact (continuousOn_const.mul continuousOn_E_star).mono (Im_subset_Ioi i)

private lemma memLp_G (i : PairIndex) :
    MemLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x)) 2
      (dStar.restrict (I_m i)) := by
  haveI := isFiniteMeasure_dStar_Im i
  have hlam0 := lambda_m_gen_pos i
  have hlam1 := lambda_m_gen_ge_one i
  have hinv0 : (0:ℝ) < (lambda_m i)⁻¹ := by positivity
  apply MemLp.of_bound
    ((continuousOn_G_Im i).aestronglyMeasurable measurableSet_Icc)
    (132 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) * lambda_m i ^ 5)
  have hIm : MeasurableSet (I_m i) := measurableSet_Icc
  rw [ae_restrict_iff' hIm]
  apply ae_of_all
  intro u hu
  have hu0 : 0 < u := Im_subset_Ioi i hu
  have hZnn : (0:ℝ) ≤ ∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ :=
    tsum_nonneg fun n => by positivity
  have hb : ‖E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u‖ ≤
      4 * (33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        (Real.sqrt u * ((u ^ (4:ℕ))⁻¹))) := by
    rw [E_star_four_mul_eq]
    rw [show (fun u : ℝ => (4:ℂ) * E_star explicitCCMLimitH u) u =
      (4:ℂ) * E_star explicitCCMLimitH u from rfl]
    rw [norm_mul, show ‖(4:ℂ)‖ = 4 by norm_num]
    exact mul_le_mul_of_nonneg_left (E_star_norm_bound hu0) (by norm_num)
  refine le_trans hb ?_
  have hsq : Real.sqrt u ≤ lambda_m i := by
    calc Real.sqrt u ≤ Real.sqrt (lambda_m i) := Real.sqrt_le_sqrt hu.2
      _ ≤ lambda_m i := by
          rw [Real.sqrt_le_left hlam0.le]
          nlinarith
  have hpow : ((u ^ (4:ℕ))⁻¹ : ℝ) ≤ lambda_m i ^ 4 := by
    have h1 : ((lambda_m i)⁻¹) ^ 4 ≤ u ^ 4 :=
      pow_le_pow_left₀ hinv0.le hu.1 4
    calc ((u ^ (4:ℕ))⁻¹ : ℝ) ≤ (((lambda_m i)⁻¹) ^ 4)⁻¹ := by
          exact (inv_le_inv₀ (by positivity) (by positivity)).mpr h1
      _ = lambda_m i ^ 4 := by
          rw [← inv_pow, inv_inv]
  calc 4 * (33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
      (Real.sqrt u * ((u ^ (4:ℕ))⁻¹)))
      ≤ 4 * (33 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        (lambda_m i * lambda_m i ^ 4)) := by
        apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hsq hpow (by positivity) hlam0.le
    _ = 132 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹) *
        lambda_m i ^ 5 := by ring


/-! ## Local projection and coefficient copies (upstream copies are private) -/

private lemma zero_mem_modeSet' (i : PairIndex) : (0:ℤ) ∈ modeSet i := by
  unfold modeSet
  rw [Finset.mem_Icc]
  omega

private lemma inner_V_P_eq' (i : PairIndex) (x : H_m i) {n : ℤ}
    (hn : n ∈ modeSet i) :
    inner ℂ (V_n_m i n) ((P_m_N i x : H_m i)) =
      inner ℂ (V_n_m i n) x := by
  classical
  rw [coe_P_m_N_apply_eq_sum_inner_V_n_m_smul, inner_sum]
  simp_rw [inner_smul_right,
    orthonormal_iff_ite.mp (V_n_m_orthonormal i), mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq (modeSet i) n
    (fun r => inner ℂ (V_n_m i r) x), if_pos hn]

private lemma c_n_eq_sT_inner' (i : PairIndex) (hT : ℝ → ℂ)
    (hE : MemLp (E_star hT) 2 (dStar.restrict (I_m i)))
    (hNz : TrialNonzero i hT hE) {n : ℤ} (hn : n ∈ modeSet i) :
    c_n i hT hE hNz n =
      ((sTrial_m_N i hT hE hNz : ℝ) : ℂ) *
        inner ℂ (V_n_m i n) (gTrial_m i hT hE) := by
  unfold c_n kTrial_m_N
  rw [Submodule.coe_smul, inner_smul_right]
  congr 1
  show inner ℂ (V_n_m i n) ((P_m_N i (gTrial_m i hT hE) : H_m i)) =
    inner ℂ (V_n_m i n) (gTrial_m i hT hE)
  exact inner_V_P_eq' i (gTrial_m i hT hE) hn

private lemma norm_P_m_N_apply_le (i : PairIndex) (x : H_m i) :
    ‖((P_m_N i x : E_m_N i) : H_m i)‖ ≤ ‖x‖ := by
  letI : FiniteDimensional ℂ (E_m_N i) :=
    FiniteDimensional.span_of_finite ℂ
      ((modeSet i).finite_toSet.image (V_n_m i))
  letI : CompleteSpace (E_m_N i) :=
    FiniteDimensional.complete ℂ (E_m_N i)
  show ‖(((E_m_N i).orthogonalProjection x : E_m_N i) : H_m i)‖ ≤ ‖x‖
  rw [Submodule.norm_coe]
  exact (E_m_N i).norm_orthogonalProjection_apply_le x

/-! ## The Lp norm as a window integral -/

private lemma lp_norm_sq_eq_integral (i : PairIndex) (f : ℝ → ℂ)
    (hf : MemLp f 2 (dStar.restrict (I_m i))) :
    ‖MemLp.toLp f hf‖ ^ 2 =
      ∫ u, Complex.normSq (f u) ∂(dStar.restrict (I_m i)) := by
  classical
  have hpt : (fun u => (inner ℂ ((MemLp.toLp f hf : ℝ → ℂ) u)
      ((MemLp.toLp f hf : ℝ → ℂ) u) : ℂ)) =ᵐ[dStar.restrict (I_m i)]
      fun u => ((Complex.normSq (f u) : ℝ) : ℂ) := by
    filter_upwards [MemLp.coeFn_toLp hf] with u hu
    rw [RCLike.inner_apply', ← Complex.normSq_eq_conj_mul_self, hu]
  have hinner : (inner ℂ (MemLp.toLp f hf) (MemLp.toLp f hf) : ℂ) =
      ((∫ u, Complex.normSq (f u) ∂(dStar.restrict (I_m i)) : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    rw [integral_congr_ae hpt]
    exact integral_complex_ofReal
  have hsq := inner_self_eq_norm_sq (𝕜 := ℂ) (MemLp.toLp f hf)
  rw [hinner] at hsq
  rw [← hsq]
  simp

/-! ## The global L²(d*u) bound for the factor-four target -/

/-- **The global target cap**: on EVERY selected window the squared
`L²(d*u)` norm of the factor-four target is at most the fixed constant
`2·(132·Z₄)²/7`, from the exact two-sided `u^{∓7/2}` decay.  This is a
`λ`-free bound — a `λ⁵` window estimate is deliberately NOT used. -/
private lemma target_norm_sq_le_global (i : PairIndex) :
    ‖MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
        (memLp_G i)‖ ^ 2 ≤
      2 * (132 * (∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹)) ^ 2 / 7 := by
  classical
  set Z : ℝ := ∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  set C : ℝ := 132 * Z with hCdef
  have hC0 : 0 ≤ C := by positivity
  set G : ℝ → ℂ := E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x)
    with hGdef
  have hlam0 := lambda_m_gen_pos i
  have hlam1 := lambda_m_gen_ge_one i
  have hinv0 : (0:ℝ) < (lambda_m i)⁻¹ := by positivity
  have hinvle1 : (lambda_m i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam1
  -- pointwise decay on both sides
  have hbig : ∀ u : ℝ, 1 ≤ u →
      Complex.normSq (G u) ≤ C ^ 2 * (u * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹)) := by
    intro u hu
    have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu
    have hb : ‖G u‖ ≤ C * (Real.sqrt u * ((u ^ (4:ℕ))⁻¹)) := by
      rw [hGdef, E_star_four_mul_eq]
      rw [show (fun v : ℝ => (4:ℂ) * E_star explicitCCMLimitH v) u =
        (4:ℂ) * E_star explicitCCMLimitH u from rfl]
      rw [norm_mul, show ‖(4:ℂ)‖ = 4 by norm_num]
      calc 4 * ‖E_star explicitCCMLimitH u‖
          ≤ 4 * (33 * Z * (Real.sqrt u * ((u ^ (4:ℕ))⁻¹))) := by
            apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
            simpa [hZdef] using E_star_norm_bound hu0
        _ = C * (Real.sqrt u * ((u ^ (4:ℕ))⁻¹)) := by
            rw [hCdef]; ring
    have hns : Complex.normSq (G u) = ‖G u‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    rw [hns]
    calc ‖G u‖ ^ 2 ≤ (C * (Real.sqrt u * ((u ^ (4:ℕ))⁻¹))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = C ^ 2 * (u * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹)) := by
          have hs : Real.sqrt u * Real.sqrt u = u :=
            Real.mul_self_sqrt hu0.le
          rw [mul_pow]
          rw [show (Real.sqrt u * ((u ^ (4:ℕ))⁻¹)) ^ 2 =
            (Real.sqrt u * Real.sqrt u) *
              ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹) by ring]
          rw [hs]
  have hsmall : ∀ u : ℝ, 0 < u → u ≤ 1 →
      Complex.normSq (G u) ≤ C ^ 2 * (u ^ (7:ℕ)) := by
    intro u hu0 hu1
    have hinv1 : (1:ℝ) ≤ u⁻¹ := (one_le_inv₀ hu0).mpr hu1
    have hGinv : G u = G u⁻¹ := by
      rw [hGdef, E_star_four_mul_eq]
      show (4:ℂ) * E_star explicitCCMLimitH u =
        (4:ℂ) * E_star explicitCCMLimitH u⁻¹
      congr 1
      exact (E_star_explicitCCMLimitH_inv u hu0).symm
    rw [hGinv]
    calc Complex.normSq (G u⁻¹)
        ≤ C ^ 2 * (u⁻¹ * (((u⁻¹) ^ (4:ℕ))⁻¹ * ((u⁻¹) ^ (4:ℕ))⁻¹)) :=
          hbig u⁻¹ hinv1
      _ = C ^ 2 * (u ^ (7:ℕ)) := by
          rw [inv_pow, inv_inv]
          field_simp
  -- the norm as a plain volume integral with the exact density
  rw [lp_norm_sq_eq_integral]
  have hrestrict : dStar.restrict (I_m i) =
      (volume.restrict (I_m i)).withDensity
        (fun u : ℝ => ENNReal.ofReal u⁻¹) := by
    unfold dStar I_m
    exact restrict_withDensity measurableSet_Icc _
  rw [hrestrict,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_inv.ennreal_ofReal)
      (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top)
      (fun u => Complex.normSq (G u))]
  set g : ℝ → ℝ := fun u => u⁻¹ * Complex.normSq (G u) with hgdef
  have hcongr : (∫ u, (ENNReal.ofReal u⁻¹).toReal •
      Complex.normSq (G u) ∂(volume.restrict (I_m i))) =
      ∫ u in I_m i, g u ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hinv0 hu.1
    show (ENNReal.ofReal u⁻¹).toReal • Complex.normSq (G u) = g u
    rw [smul_eq_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ u⁻¹)]
  rw [hcongr]
  -- continuity of the integrand on the positive axis
  have hGcont : ContinuousOn G (Set.Ioi (0:ℝ)) := by
    rw [hGdef, E_star_four_mul_eq]
    exact continuousOn_const.mul continuousOn_E_star
  have hgcont : ContinuousOn g (Set.Ioi (0:ℝ)) := by
    apply ContinuousOn.mul
    · exact ContinuousOn.inv₀ continuousOn_id fun u hu => ne_of_gt hu
    · exact Complex.continuous_normSq.comp_continuousOn hGcont
  have hIccL_sub : Set.Icc (lambda_m i)⁻¹ 1 ⊆ Set.Ioi (0:ℝ) := by
    intro u hu
    exact lt_of_lt_of_le hinv0 hu.1
  have hIccR_sub : Set.Icc (1:ℝ) (lambda_m i) ⊆ Set.Ioi (0:ℝ) := by
    intro u hu
    exact lt_of_lt_of_le one_pos hu.1
  have hintL : IntegrableOn g (Set.Icc (lambda_m i)⁻¹ 1) volume :=
    (hgcont.mono hIccL_sub).integrableOn_Icc
  have hintR : IntegrableOn g (Set.Ioc (1:ℝ) (lambda_m i)) volume :=
    ((hgcont.mono hIccR_sub).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  -- split the window at 1
  have hsplit : I_m i =
      Set.Icc (lambda_m i)⁻¹ 1 ∪ Set.Ioc (1:ℝ) (lambda_m i) := by
    show Set.Icc (lambda_m i)⁻¹ (lambda_m i) = _
    exact (Set.Icc_union_Ioc_eq_Icc hinvle1 hlam1).symm
  have hdisj : Disjoint (Set.Icc (lambda_m i)⁻¹ 1)
      (Set.Ioc (1:ℝ) (lambda_m i)) := by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    exact absurd hu1.2 (not_le.mpr hu2.1)
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hintL hintR]
  -- left piece: majorized by C²·u⁶
  have hleft : (∫ u in Set.Icc (lambda_m i)⁻¹ 1, g u ∂volume) ≤
      C ^ 2 / 7 := by
    have hmaj : ∀ u ∈ Set.Icc (lambda_m i)⁻¹ 1,
        g u ≤ C ^ 2 * u ^ (6:ℕ) := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hinv0 hu.1
      rw [hgdef]
      calc u⁻¹ * Complex.normSq (G u)
          ≤ u⁻¹ * (C ^ 2 * (u ^ (7:ℕ))) := by
            apply mul_le_mul_of_nonneg_left
              (hsmall u hu0 hu.2) (by positivity)
        _ = C ^ 2 * u ^ (6:ℕ) := by
            field_simp
    have hmaj_int : IntegrableOn (fun u : ℝ => C ^ 2 * u ^ (6:ℕ))
        (Set.Icc (lambda_m i)⁻¹ 1) volume := by
      apply Continuous.integrableOn_Icc
      fun_prop
    have hle : (∫ u in Set.Icc (lambda_m i)⁻¹ 1, g u ∂volume) ≤
        ∫ u in Set.Icc (lambda_m i)⁻¹ 1, C ^ 2 * u ^ (6:ℕ) ∂volume := by
      apply setIntegral_mono_on
        hintL hmaj_int measurableSet_Icc hmaj
    refine le_trans hle ?_
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hinvle1]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_pow]
    have hbound : ((1:ℝ) ^ (6+1) - ((lambda_m i)⁻¹) ^ (6+1)) / (6+1) ≤
        1 / 7 := by
      have h1 : (0:ℝ) ≤ ((lambda_m i)⁻¹) ^ 7 := by positivity
      have h2 : ((1:ℝ) ^ (6+1) - ((lambda_m i)⁻¹) ^ (6+1)) / ((6:ℝ)+1) =
          (1 - ((lambda_m i)⁻¹) ^ 7) / 7 := by norm_num
      rw [h2]
      linarith
    calc C ^ 2 * ((1 ^ (6+1) - ((lambda_m i)⁻¹) ^ (6+1)) / (6+1))
        ≤ C ^ 2 * (1 / 7) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = C ^ 2 / 7 := by ring
  -- right piece: majorized by C²·u⁻⁸
  have hright : (∫ u in Set.Ioc (1:ℝ) (lambda_m i), g u ∂volume) ≤
      C ^ 2 / 7 := by
    have hmaj : ∀ u ∈ Set.Ioc (1:ℝ) (lambda_m i),
        g u ≤ C ^ 2 * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹) := by
      intro u hu
      have hu1 : (1:ℝ) ≤ u := hu.1.le
      have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu1
      rw [hgdef]
      calc u⁻¹ * Complex.normSq (G u)
          ≤ u⁻¹ * (C ^ 2 *
              (u * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹))) := by
            apply mul_le_mul_of_nonneg_left (hbig u hu1) (by positivity)
        _ = C ^ 2 * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹) := by
            field_simp
    have hmaj_int : IntegrableOn
        (fun u : ℝ => C ^ 2 * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹))
        (Set.Ioc (1:ℝ) (lambda_m i)) volume := by
      apply IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.mul <;>
      · apply ContinuousOn.inv₀
        · fun_prop
        · intro u hu
          have : (0:ℝ) < u := lt_of_lt_of_le one_pos hu.1
          positivity
    have hg_nonneg : ∀ u ∈ Set.Ioc (1:ℝ) (lambda_m i), 0 ≤ g u := by
      intro u hu
      have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu.1.le
      rw [hgdef]
      exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
    have hle : (∫ u in Set.Ioc (1:ℝ) (lambda_m i), g u ∂volume) ≤
        ∫ u in Set.Ioc (1:ℝ) (lambda_m i),
          C ^ 2 * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹) ∂volume := by
      apply setIntegral_mono_on hintR hmaj_int measurableSet_Ioc hmaj
    refine le_trans hle ?_
    have hcongr8 : (∫ u in Set.Ioc (1:ℝ) (lambda_m i),
        C ^ 2 * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹) ∂volume) =
        ∫ u in Set.Ioc (1:ℝ) (lambda_m i),
          C ^ 2 * u ^ (-(8:ℝ)) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu.1.le
      show C ^ 2 * ((u ^ (4:ℕ))⁻¹ * (u ^ (4:ℕ))⁻¹) =
        C ^ 2 * u ^ (-(8:ℝ))
      congr 1
      rw [show (-(8:ℝ)) = -((8:ℕ):ℝ) by norm_num, Real.rpow_neg hu0.le,
        Real.rpow_natCast]
      rw [show ((u:ℝ) ^ (8:ℕ)) = u ^ (4:ℕ) * u ^ (4:ℕ) by ring]
      rw [mul_inv]
    rw [hcongr8]
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [show (∫ u in Set.Ioo (1:ℝ) (lambda_m i),
        C ^ 2 * u ^ (-(8:ℝ)) ∂volume) =
      C ^ 2 * ∫ u in Set.Ioo (1:ℝ) (lambda_m i),
        u ^ (-(8:ℝ)) ∂volume from by
        rw [MeasureTheory.integral_const_mul]]
    have hnmem : (0:ℝ) ∉ Set.uIcc 1 (lambda_m i) := by
      intro hmem
      rw [Set.uIcc_of_le hlam1] at hmem
      exact absurd hmem.1 (by norm_num)
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hlam1]
    rw [integral_rpow (Or.inr ⟨by norm_num, hnmem⟩)]
    have hval : ((lambda_m i) ^ ((-(8:ℝ)) + 1) -
        (1:ℝ) ^ ((-(8:ℝ)) + 1)) / ((-(8:ℝ)) + 1) ≤ 1 / 7 := by
      rw [show ((-(8:ℝ)) + 1) = -7 by norm_num]
      rw [Real.one_rpow]
      have hlpos : 0 < (lambda_m i) ^ (-(7:ℝ)) :=
        Real.rpow_pos_of_pos hlam0 _
      rw [show ((lambda_m i) ^ (-(7:ℝ)) - 1) / (-7 : ℝ) =
        (1 - (lambda_m i) ^ (-(7:ℝ))) / 7 by ring]
      have h1 : (lambda_m i) ^ (-(7:ℝ)) ≥ 0 := hlpos.le
      linarith
    calc C ^ 2 * (((lambda_m i) ^ ((-(8:ℝ)) + 1) -
        (1:ℝ) ^ ((-(8:ℝ)) + 1)) / ((-(8:ℝ)) + 1))
        ≤ C ^ 2 * (1 / 7) :=
          mul_le_mul_of_nonneg_left hval (by positivity)
      _ = C ^ 2 / 7 := by ring
  calc (∫ u in Set.Icc (lambda_m i)⁻¹ 1, g u ∂volume) +
      (∫ u in Set.Ioc (1:ℝ) (lambda_m i), g u ∂volume)
      ≤ C ^ 2 / 7 + C ^ 2 / 7 := add_le_add hleft hright
    _ = 2 * C ^ 2 / 7 := by ring
    _ = 2 * (132 * Z) ^ 2 / 7 := by rw [hCdef]

private lemma local_L_pos (i : PairIndex) : 0 < L_m i := by
  have h := i.hm
  show (0:ℝ) < Real.log i.m
  apply Real.log_pos
  exact_mod_cast (by omega : 1 < i.m)

/-! ## The exact anchor identity -/

/-- **The anchor identity**: `L_k·|q₀|² = |s_k·Gwin_k(0)|²/‖s_k·P(g_k)‖²`
— the source scale stays inside the scaled projected vector; no fitted
normalizer, no neighboring target. -/
theorem selectedFerrersFiniteCCM_log_mul_centerCoeff_normSq_eq_anchor_div_scaledProjectionNormSq
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    L_m ((selectedFerrersCofinalSourceData P).index k) *
      Complex.normSq (selectedFerrersFiniteCCMCenterCoefficient P k) =
      Complex.normSq
        ((selectedFerrersCofinalSourceData P).sourceScale k *
          preAnchorGwinTransformCoordinate
            ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            0) /
      ‖(selectedFerrersCofinalSourceData P).sourceScale k •
        ((gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
            E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
          H_m ((selectedFerrersCofinalSourceData P).index k))‖ ^ 2 := by
  classical
  have hs := (selectedFerrersCofinalSourceData P).sourceScale_ne k
  have hgN : 0 < ‖gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)‖ :=
    (selectedFerrersCofinalSourceData P).trialNonzero k
  have hL0 : 0 < L_m ((selectedFerrersCofinalSourceData P).index k) :=
    local_L_pos _
  -- the center coefficient through the zero-mode inner product
  have hq0 : selectedFerrersFiniteCCMCenterCoefficient P k =
      ((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)
        ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) *
        inner ℂ (V_n_m ((selectedFerrersCofinalSourceData P).index k) 0)
          (gTrial_m ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)) := by
    show selectedFerrersFiniteCCMRow P k
        (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N) = _
    show c_n ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)
        ((selectedFerrersCofinalSourceData P).trialNonzero k)
        (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N
          (ccmCenterFinite ((selectedFerrersCofinalSourceData P).index k).N)) = _
    rw [ccmModeFinite_center]
    exact c_n_eq_sT_inner' _ _ _ _ (zero_mem_modeSet' _)
  -- the numerator through the Gwin zero identity
  have hgwin := preAnchorGwin_zero_eq_sqrtL_mul_innerV0
    ((selectedFerrersCofinalSourceData P).index k)
    (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
    ((selectedFerrersCofinalSourceData P).eStar_memLp k)
  -- scalar bookkeeping
  set s : ℂ := (selectedFerrersCofinalSourceData P).sourceScale k with hsdef
  set L : ℝ := L_m ((selectedFerrersCofinalSourceData P).index k) with hLdef
  set w : ℂ := inner ℂ
    (V_n_m ((selectedFerrersCofinalSourceData P).index k) 0)
    (gTrial_m ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)) with hwdef
  set nG : ℝ := ‖gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)‖ with hnGdef
  have hnum : Complex.normSq (s *
      preAnchorGwinTransformCoordinate
        ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        0) = Complex.normSq s * (L * Complex.normSq w) := by
    rw [hgwin, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal]
    rw [Real.mul_self_sqrt hL0.le]
  have hden : ‖s • ((gTrial_m_N
      ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
        E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
      H_m ((selectedFerrersCofinalSourceData P).index k))‖ ^ 2 =
      Complex.normSq s * nG ^ 2 := by
    rw [norm_smul, mul_pow, Complex.normSq_eq_norm_sq, hnGdef]
    rw [Submodule.norm_coe]
  have hlhs : L * Complex.normSq
      (selectedFerrersFiniteCCMCenterCoefficient P k) =
      L * (nG⁻¹ ^ 2 * Complex.normSq w) := by
    rw [hq0, Complex.normSq_mul, Complex.normSq_ofReal]
    congr 2
    show (sTrial_m_N _ _ _ _) * (sTrial_m_N _ _ _ _) = nG⁻¹ ^ 2
    show ‖gTrial_m_N _ _ _‖⁻¹ * ‖gTrial_m_N _ _ _‖⁻¹ = nG⁻¹ ^ 2
    rw [hnGdef, sq]
  rw [hlhs, hnum, hden]
  have hs0 : Complex.normSq s ≠ 0 := by
    intro h
    exact hs (Complex.normSq_eq_zero.mp h)
  field_simp

/-! ## The window error bound (local copy of the H2A.3 chain) -/

private lemma local_err_norm_sq_le
    (i : PairIndex) (hT : ℝ → ℂ)
    (hE : MemLp (E_star hT) 2 (dStar.restrict (I_m i)))
    (s : ℂ) (Cf : ℝ)
    (hl : 1 ≤ lambda_m i) (hCf : 0 ≤ Cf)
    (herr : ∀ u ∈ I_m i,
      ‖s * E_star hT u -
        E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u‖ ≤
        Cf / (lambda_m i * Real.sqrt u)) :
    ‖s • (MemLp.toLp (E_star hT) hE) -
        MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
          (memLp_G i)‖ ^ 2 ≤ Cf ^ 2 / lambda_m i := by
  classical
  set e : H_m i := s • (MemLp.toLp (E_star hT) hE) -
    MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
      (memLp_G i) with hedef
  have hcoe : (e : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
      fun u => s * E_star hT u -
        E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u := by
    have h1 := MeasureTheory.Lp.coeFn_sub
      (s • (MemLp.toLp (E_star hT) hE))
      (MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
        (memLp_G i))
    have h2 := MeasureTheory.Lp.coeFn_smul s (MemLp.toLp (E_star hT) hE)
    have h3 := MemLp.coeFn_toLp hE
    have h4 := MemLp.coeFn_toLp (memLp_G i)
    have h5 : (⇑(s • (MemLp.toLp (E_star hT) hE)) : ℝ → ℂ)
        =ᵐ[dStar.restrict (I_m i)] fun u => s * E_star hT u := by
      filter_upwards [h2, h3] with u e2 e3
      rw [e2, Pi.smul_apply, e3, smul_eq_mul]
    filter_upwards [h1, h5, h4] with u e1 e5 e4
    rw [hedef]
    show (⇑((s • (MemLp.toLp (E_star hT) hE)) -
      MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
        (memLp_G i)) : ℝ → ℂ) u = _
    rw [e1, Pi.sub_apply, e5, e4]
  have hns : ‖e‖ ^ 2 =
      ∫ u, Complex.normSq
        (s * E_star hT u -
          E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u)
        ∂(dStar.restrict (I_m i)) := by
    have hpt : (fun u => (inner ℂ ((e : ℝ → ℂ) u) ((e : ℝ → ℂ) u) : ℂ))
        =ᵐ[dStar.restrict (I_m i)]
        fun u => ((Complex.normSq
          (s * E_star hT u -
            E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u) : ℝ) :
          ℂ) := by
      filter_upwards [hcoe] with u hu
      rw [RCLike.inner_apply', ← Complex.normSq_eq_conj_mul_self, hu]
    have hinner : (inner ℂ e e : ℂ) =
        ((∫ u, Complex.normSq
          (s * E_star hT u -
            E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u)
          ∂(dStar.restrict (I_m i)) : ℝ) : ℂ) := by
      rw [MeasureTheory.L2.inner_def]
      rw [integral_congr_ae hpt]
      exact integral_complex_ofReal
    have hsq := inner_self_eq_norm_sq (𝕜 := ℂ) e
    rw [hinner] at hsq
    rw [← hsq]
    simp
  rw [hns]
  exact window_l2_integral_le i hl _ Cf hCf herr

/-! ## The source-derived inverse-log floor -/

/-- **The inverse-log center floor**: from the exact mode/chi contracts,
eventually `c_center ≤ L_k·|q₀|²` for an explicit positive constant.  The
numerator is floored by the Müntz limit at `z = 0`; the denominator is
capped by the L73 physical error plus the global `L²(d*u)` target norm.
Pointwise nonvanishing is never used as a rate. -/
theorem selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates
    (C0 C4 Cχ : ℝ)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hCχ : 0 ≤ Cχ)
    (hmode :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 x -
            ((parabolicCylinderD 0
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    let P := selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
    ∃ cCenter : ℝ, 0 < cCenter ∧
      ∀ᶠ k in Filter.atTop,
        cCenter ≤
          L_m ((selectedFerrersCofinalSourceData P).index k) *
            Complex.normSq
              (selectedFerrersFiniteCCMCenterCoefficient P k) := by
  intro P
  classical
  obtain ⟨C1, hC1, hev1⟩ :=
    selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  obtain ⟨C2, hC2, hev2⟩ := selectedFerrersExplicitTargetTail_bound
  have hXi : (0:ℝ) < ‖centeredXi 0‖ :=
    norm_pos_iff.mpr centeredXi_zero_ne_zero
  set Z : ℝ := ∑' n : ℕ+, ((((n : ℕ) : ℝ)) ^ (4:ℕ))⁻¹ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  set Mt : ℝ := 2 * (132 * Z) ^ 2 / 7 with hMtdef
  have hMt0 : 0 ≤ Mt := by positivity
  refine ⟨(‖centeredXi 0‖ ^ 2 / 4) / (1 + Real.sqrt Mt) ^ 2,
    by positivity, ?_⟩
  -- eventual pointwise full error
  have hfull : ∀ᶠ σ in Filter.atTop,
      ∀ u ∈ sourceWindow (selectedFerrersPaperLambda σ),
        ‖selectedFerrersFullEStarError σ u‖ ≤
          (C1 + C2) / (selectedFerrersPaperLambda σ * Real.sqrt u) := by
    filter_upwards [hev1, hev2] with σ h1 h2
    intro u hu
    rw [selectedFerrersFullEStarError_eq_main_sub_targetTail σ hu]
    calc ‖selectedFerrersEStarWindowMainError σ u -
        selectedFerrersExplicitTargetTail σ u‖
        ≤ ‖selectedFerrersEStarWindowMainError σ u‖ +
          ‖selectedFerrersExplicitTargetTail σ u‖ := norm_sub_le _ _
      _ ≤ C1 / (selectedFerrersPaperLambda σ * Real.sqrt u) +
          C2 / (selectedFerrersPaperLambda σ * Real.sqrt u) :=
          add_le_add (h1 u hu) (h2 u hu)
      _ = (C1 + C2) / (selectedFerrersPaperLambda σ * Real.sqrt u) :=
          (add_div _ _ _).symm
  have hfullk := (selectedFerrersCofinalPreAnchorRank_tendsto P).eventually
    hfull
  -- eventual anchor at z = 0
  have hzero_mem : (0:ℂ) ∈ centeredCriticalStrip := by
    show |(0:ℂ).im| < 1 / 2
    norm_num
  have hpoint :=
    (selectedFerrersCofinalSourceData P).muntzLimit.tendsto_at hzero_mem
  have hanchor := hpoint.norm.eventually_const_le (half_lt_self hXi)
  -- eventual largeness of lambda
  have hlam_big : ∀ᶠ k in Filter.atTop,
      (C1 + C2) ^ 2 ≤
        lambda_m ((selectedFerrersCofinalSourceData P).index k) := by
    have hm := (selectedFerrersCofinalSourceData P).mCofinal
    have hev := hm.eventually
      (Filter.eventually_ge_atTop (Nat.ceil ((((C1+C2)^2)^2 : ℝ))))
    filter_upwards [hev] with k hk
    have hcast : ((((C1+C2)^2)^2 : ℝ)) ≤
        ((((selectedFerrersCofinalSourceData P).index k).m : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
    show (C1 + C2) ^ 2 ≤
      Real.sqrt (((selectedFerrersCofinalSourceData P).index k).m : ℝ)
    rw [show ((C1+C2)^2 : ℝ) =
      Real.sqrt ((((C1+C2)^2)^2 : ℝ)) from
        (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hcast
  filter_upwards [hfullk, hanchor, hlam_big] with k hkfull hkanch hklam
  -- rewrite through the exact anchor identity
  rw [selectedFerrersFiniteCCM_log_mul_centerCoeff_normSq_eq_anchor_div_scaledProjectionNormSq
    P k]
  -- window transfer (public crosswalks + local lambda lemma)
  have hlam_eq : lambda_m ((selectedFerrersCofinalSourceData P).index k) =
      selectedFerrersPaperLambda (selectedFerrersCofinalPreAnchorRank P k) := by
    rw [selectedFerrersCofinalSourceData_index_eq_preAnchorIndex P k]
    exact lambda_paper_eq_lambda_m _
  have hIm_eq : I_m ((selectedFerrersCofinalSourceData P).index k) =
      sourceWindow
        (selectedFerrersPaperLambda
          (selectedFerrersCofinalPreAnchorRank P k)) := by
    show Set.Icc (lambda_m ((selectedFerrersCofinalSourceData P).index k))⁻¹
      (lambda_m ((selectedFerrersCofinalSourceData P).index k)) = _
    rw [hlam_eq]
    rfl
  have herr : ∀ u ∈ I_m ((selectedFerrersCofinalSourceData P).index k),
      ‖(selectedFerrersCofinalSourceData P).sourceScale k *
          E_star (prolateCombination
            ((selectedFerrersCofinalSourceData P).pair k)) u -
        E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u‖ ≤
        (C1 + C2) /
          (lambda_m ((selectedFerrersCofinalSourceData P).index k) *
            Real.sqrt u) := by
    intro u hu
    have hfe : selectedFerrersFullEStarError
        (selectedFerrersCofinalPreAnchorRank P k) u =
        (selectedFerrersCofinalSourceData P).sourceScale k *
          E_star (prolateCombination
            ((selectedFerrersCofinalSourceData P).pair k)) u -
          E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u := by
      rw [selectedFerrersCofinalSourceData_sourceScale_eq_preAnchorScale P k,
        selectedFerrersCofinalSourceData_pair_eq_preAnchorPair P k,
        congrFun E_star_four_mul_eq u]
      rfl
    rw [← hfe, hlam_eq]
    exact hkfull u (by rwa [← hIm_eq])
  -- the physical error is eventually at most one
  have henorm := local_err_norm_sq_le
    ((selectedFerrersCofinalSourceData P).index k)
    (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
    ((selectedFerrersCofinalSourceData P).eStar_memLp k)
    ((selectedFerrersCofinalSourceData P).sourceScale k)
    (C1 + C2)
    (lambda_m_gen_ge_one _) (by positivity) herr
  have hlam0 := lambda_m_gen_pos
    ((selectedFerrersCofinalSourceData P).index k)
  set eVec : H_m ((selectedFerrersCofinalSourceData P).index k) :=
    (selectedFerrersCofinalSourceData P).sourceScale k •
      (MemLp.toLp (E_star (prolateCombination
        ((selectedFerrersCofinalSourceData P).pair k)))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)) -
      MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
        (memLp_G ((selectedFerrersCofinalSourceData P).index k))
    with heVec
  have herr1 : ‖eVec‖ ≤ 1 := by
    have hsq : ‖eVec‖ ^ 2 ≤ 1 := by
      refine le_trans henorm ?_
      rw [div_le_one hlam0]
      exact hklam
    nlinarith [norm_nonneg eVec, hsq]
  -- the global target cap
  have htarget : ‖MemLp.toLp
      (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
      (memLp_G ((selectedFerrersCofinalSourceData P).index k))‖ ≤
      Real.sqrt Mt := by
    have h := target_norm_sq_le_global
      ((selectedFerrersCofinalSourceData P).index k)
    rw [show ‖MemLp.toLp
        (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
        (memLp_G ((selectedFerrersCofinalSourceData P).index k))‖ =
      Real.sqrt (‖MemLp.toLp
        (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
        (memLp_G ((selectedFerrersCofinalSourceData P).index k))‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
    apply Real.sqrt_le_sqrt
    refine le_trans h ?_
    rw [hMtdef]
  -- the scaled trial is bounded
  have hgl : ‖(selectedFerrersCofinalSourceData P).sourceScale k •
      (MemLp.toLp (E_star (prolateCombination
        ((selectedFerrersCofinalSourceData P).pair k)))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k))‖ ≤
      1 + Real.sqrt Mt := by
    have hdecomp : (selectedFerrersCofinalSourceData P).sourceScale k •
        (MemLp.toLp (E_star (prolateCombination
          ((selectedFerrersCofinalSourceData P).pair k)))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)) =
        ((selectedFerrersCofinalSourceData P).sourceScale k •
          (MemLp.toLp (E_star (prolateCombination
            ((selectedFerrersCofinalSourceData P).pair k)))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)) -
          MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
            (memLp_G ((selectedFerrersCofinalSourceData P).index k))) +
        MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
          (memLp_G ((selectedFerrersCofinalSourceData P).index k)) := by
      rw [sub_add_cancel]
    rw [hdecomp]
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ 1 + Real.sqrt Mt := add_le_add herr1 htarget
  -- the denominator is capped
  have hdenmap : (selectedFerrersCofinalSourceData P).sourceScale k •
      ((gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
          E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
        H_m ((selectedFerrersCofinalSourceData P).index k)) =
      ((P_m_N ((selectedFerrersCofinalSourceData P).index k)
        ((selectedFerrersCofinalSourceData P).sourceScale k •
          gTrial_m ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination
              ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)) :
          E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
        H_m ((selectedFerrersCofinalSourceData P).index k)) := by
    rw [map_smul]
    rw [Submodule.coe_smul]
    rfl
  have hden_le : ‖(selectedFerrersCofinalSourceData P).sourceScale k •
      ((gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
          E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
        H_m ((selectedFerrersCofinalSourceData P).index k))‖ ≤
      1 + Real.sqrt Mt := by
    rw [hdenmap]
    refine le_trans (norm_P_m_N_apply_le _ _) ?_
    exact hgl
  -- the numerator is floored
  have hnum_ge : ‖centeredXi 0‖ ^ 2 / 4 ≤
      Complex.normSq
        ((selectedFerrersCofinalSourceData P).sourceScale k *
          preAnchorGwinTransformCoordinate
            ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination
              ((selectedFerrersCofinalSourceData P).pair k)) 0) := by
    rw [Complex.normSq_eq_norm_sq]
    have h := pow_le_pow_left₀ (by positivity) hkanch 2
    calc ‖centeredXi 0‖ ^ 2 / 4 = (‖centeredXi 0‖ / 2) ^ 2 := by ring
      _ ≤ _ := h
  -- assemble: the ratio dominates the constant
  have hdpos : (0:ℝ) < ‖(selectedFerrersCofinalSourceData P).sourceScale k •
      ((gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
          E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
        H_m ((selectedFerrersCofinalSourceData P).index k))‖ ^ 2 := by
    have hs := (selectedFerrersCofinalSourceData P).sourceScale_ne k
    have hgN := (selectedFerrersCofinalSourceData P).trialNonzero k
    have hne : (selectedFerrersCofinalSourceData P).sourceScale k •
        ((gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination
            ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
            E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
          H_m ((selectedFerrersCofinalSourceData P).index k)) ≠ 0 := by
      apply smul_ne_zero hs
      intro h0
      apply ne_of_gt hgN
      rw [show ‖gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)‖ =
        ‖((gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination
            ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
            E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
          H_m ((selectedFerrersCofinalSourceData P).index k))‖ from
          (Submodule.norm_coe _).symm]
      rw [h0, norm_zero]
    positivity
  calc ‖centeredXi 0‖ ^ 2 / 4 / (1 + Real.sqrt Mt) ^ 2
      ≤ ‖centeredXi 0‖ ^ 2 / 4 /
        ‖(selectedFerrersCofinalSourceData P).sourceScale k •
          ((gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination
              ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
              E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
            H_m ((selectedFerrersCofinalSourceData P).index k))‖ ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) hdpos
        exact pow_le_pow_left₀ (norm_nonneg _) hden_le 2
    _ ≤ Complex.normSq
          ((selectedFerrersCofinalSourceData P).sourceScale k *
            preAnchorGwinTransformCoordinate
              ((selectedFerrersCofinalSourceData P).index k)
              (prolateCombination
                ((selectedFerrersCofinalSourceData P).pair k)) 0) /
        ‖(selectedFerrersCofinalSourceData P).sourceScale k •
          ((gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination
              ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k) :
              E_m_N ((selectedFerrersCofinalSourceData P).index k)) :
            H_m ((selectedFerrersCofinalSourceData P).index k))‖ ^ 2 := by
        gcongr

private lemma local_oddMass_nonneg'
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    0 ≤ selectedFerrersFiniteCCMOddMass P k := by
  unfold selectedFerrersFiniteCCMOddMass
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-! ## The denominator-free receiver -/

/-- **The denominator-free receiver**: with the same exact mode/chi
inputs, `L_k·η_k·‖Γ_k‖² → 0` forces the ratified weighted-residual
consumer, through the inverse-log center floor and the existing 3B ratio
receiver.  `R_k → 0` is never assumed separately. -/
theorem selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_logWeightedCommutatorEnergy_of_modeAndChiRates
    (C0 C4 Cχ : ℝ)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hCχ : 0 ≤ Cχ)
    (hmode :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 x -
            ((parabolicCylinderD 0
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    let P := selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
    Filter.Tendsto
      (fun k =>
        L_m ((selectedFerrersCofinalSourceData P).index k) *
          selectedFerrersFiniteCCMOddMass P k *
          selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k)
      Filter.atTop (nhds 0) →
    Filter.Tendsto
      (fun k =>
        Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
          Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k))
      Filter.atTop (nhds 0) := by
  intro P hLηG
  classical
  obtain ⟨cCenter, hc0, hcev⟩ :=
    selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  -- the ratio tends to zero by squeeze
  have hratio : Filter.Tendsto
      (fun k => selectedFerrersFiniteCCMWeightedCommutatorRatio P k)
      Filter.atTop (nhds 0) := by
    have hub : ∀ᶠ k in Filter.atTop,
        selectedFerrersFiniteCCMWeightedCommutatorRatio P k ≤
          (L_m ((selectedFerrersCofinalSourceData P).index k) *
            selectedFerrersFiniteCCMOddMass P k *
            selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k) /
            cCenter := by
      filter_upwards [hcev] with k hck
      have hL0 : 0 < L_m ((selectedFerrersCofinalSourceData P).index k) :=
        local_L_pos _
      have hq0 : Complex.normSq
          (selectedFerrersFiniteCCMCenterCoefficient P k) ≠ 0 := by
        intro h
        exact selectedFerrersFiniteCCMCenterCoefficient_ne P k
          (Complex.normSq_eq_zero.mp h)
      have hq0pos : 0 < Complex.normSq
          (selectedFerrersFiniteCCMCenterCoefficient P k) :=
        lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hq0)
      have hη0 : 0 ≤ selectedFerrersFiniteCCMOddMass P k :=
        local_oddMass_nonneg' P k
      have hG0 : 0 ≤
          selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k := by
        unfold selectedFerrersFiniteCCMCommutatorResidualDefectEnergy
        exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
      unfold selectedFerrersFiniteCCMWeightedCommutatorRatio
      rw [div_le_div_iff₀ hq0pos hc0]
      calc selectedFerrersFiniteCCMOddMass P k *
          selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k *
          cCenter
          ≤ selectedFerrersFiniteCCMOddMass P k *
            selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k *
            (L_m ((selectedFerrersCofinalSourceData P).index k) *
              Complex.normSq
                (selectedFerrersFiniteCCMCenterCoefficient P k)) :=
            mul_le_mul_of_nonneg_left hck (mul_nonneg hη0 hG0)
        _ = L_m ((selectedFerrersCofinalSourceData P).index k) *
            selectedFerrersFiniteCCMOddMass P k *
            selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k *
            Complex.normSq
              (selectedFerrersFiniteCCMCenterCoefficient P k) := by
            ring
    have hlb : ∀ᶠ k in Filter.atTop,
        0 ≤ selectedFerrersFiniteCCMWeightedCommutatorRatio P k := by
      refine Filter.Eventually.of_forall fun k => ?_
      unfold selectedFerrersFiniteCCMWeightedCommutatorRatio
      apply div_nonneg
      · apply mul_nonneg (local_oddMass_nonneg' P k)
        unfold selectedFerrersFiniteCCMCommutatorResidualDefectEnergy
        exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
      · exact Complex.normSq_nonneg _
    have hub0 : Filter.Tendsto
        (fun k =>
          (L_m ((selectedFerrersCofinalSourceData P).index k) *
            selectedFerrersFiniteCCMOddMass P k *
            selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k) /
            cCenter)
        Filter.atTop (nhds 0) := by
      have h := hLηG.div_const cCenter
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hub0 hlb hub
  exact selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_commutatorRatio
    P hratio

#print axioms selectedFerrersFiniteCCM_log_mul_centerCoeff_normSq_eq_anchor_div_scaledProjectionNormSq
#print axioms selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates
#print axioms selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_logWeightedCommutatorEnergy_of_modeAndChiRates
#print axioms pointwise_center_nonzero_without_log_floor_plant
#print axioms anchor_without_scaled_projection_upper_bound_does_not_force_center_floor_plant

end Q3.RouteB.D0Pstar

end
