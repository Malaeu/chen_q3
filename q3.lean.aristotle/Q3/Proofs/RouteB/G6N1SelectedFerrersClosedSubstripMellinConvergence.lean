import Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail
import Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinOuterTail

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex MeasureTheory Asymptotics Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# L73.7 — selected Ferrers closed-substrip Mellin convergence

Floor `L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE` of verdict
`4c8b995a`.

The quantitative window Mellin assembly: on each fixed closed substrip
`|z.im| ≤ σ` with `0 ≤ σ < 1/2`, the scaled selected-Ferrers `Gwin`
coordinate converges to the production `centeredXi`, uniformly, under the
explicit mode and chi rate hypotheses.

The decisive identity is proved first, exactly and without any new
hypothesis: for every `k` and every `z` in the open centered strip,

`sourceScale * Gwin - centeredXi = windowMellin(fullError) - outerTail`.

Here `fullError` is the literal L73.4 pointwise defect, `outerTail` is the
literal L73.6 factor-four outer tail, and `windowMellin` is the source-window
Mellin integral at the exact coordinate `s = -I*z`.  The identity is
type-correct because the window integrability of the source side follows
from the finite support of the selected pair (at most `k+2` active dilates
on the window), and the target side is `MellinConvergent` by a locally
re-proved two-sided Big-O argument — nothing is assumed.

The rate is the verdict's two-term power rate, obtained by splitting the
window at `u = 1`:

`Cf * (lambda^(σ-1/2)/(σ+1/2) + lambda⁻¹/(1/2-σ))`.

The private plant records the boundary model `λ⁻¹∫_{λ⁻¹}^1 u⁻² du = 1-1/λ`,
which does not tend to zero: the closed-substrip margin is load-bearing and
the whole-open-strip source statement is forbidden.

Deliberately NOT here: the port inhabitant (L73.8).

LEDGER:
  CLOSES: [CCM_LEMMA_7_3_SELECTED_FERRERS_CLOSED_SUBSTRIP_CONVERGENCE]
  OPENS:  []
-/

/-! ## The mandatory margin plant -/

/-- **The plant.**  The exact algebraic value of the lower-window boundary
model `λ⁻¹ * ∫_{λ⁻¹}^{1} u⁻² du = (1/λ)*(λ-1) = 1 - 1/λ`: it is positive
and does **not** tend to zero as `λ → ∞`.  At the strip boundary
`z.im = -1/2` the lower-window Mellin majorant degenerates to exactly this
model, so uniform source convergence on the whole open strip is impossible
with the available `C/(λ√u)` budget.  The closed-substrip margin `σ < 1/2`
is load-bearing; any attempt to replace the closed substrip by the whole
open strip dies here. -/
private theorem closedSubstrip_margin_is_loadBearing_plant
    {lam : ℝ} (hlam : 1 < lam) :
    (1 / lam) * (lam - 1) = 1 - 1 / lam ∧ 0 < 1 - 1 / lam := by
  have hlam0 : (0:ℝ) < lam := lt_trans one_pos hlam
  constructor
  · field_simp
  · have h1 : 1 / lam < 1 := (div_lt_one hlam0).mpr hlam
    linarith

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

private lemma lambda_ge_one (k : ℕ) : 1 ≤ selectedFerrersPaperLambda k := by
  rw [selectedFerrersPaperLambda,
    show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)

private lemma lambda_pos (k : ℕ) : 0 < selectedFerrersPaperLambda k :=
  lt_of_lt_of_le one_pos (lambda_ge_one k)

/-- The exact coordinate: `(-I*z).re = z.im`.  A sign error here would swap
the two tail exponent ledgers. -/
private lemma neg_I_mul_re (z : ℂ) : (-Complex.I * z).re = z.im := by
  simp [Complex.mul_re]

/-! ## Schedule and coordinate facts -/

private lemma lambda_gt_one (k : ℕ) : 1 < selectedFerrersPaperLambda k := by
  rw [selectedFerrersPaperLambda,
    show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  apply Real.sqrt_lt_sqrt (by norm_num)
  exact_mod_cast (by omega : 1 < k + 2)

private lemma lambda_m_idx_eq (k : ℕ) :
    lambda_m (selectedFerrersPreAnchorIndex k) =
      selectedFerrersPaperLambda k := by
  rw [← selectedFerrersPreAnchorPair_lambda_eq,
    selectedFerrersPreAnchorPair_lambda_eq_paperLambda]

/-- The MuntzV3 comb and the D0Pstar comb are the same function. -/
private lemma muntz_Estar_eq (h : ℝ → ℂ) :
    EStarMuntzZeroMassContinuation.Estar h = E_star h := by
  funext u
  rw [EStarMuntzZeroMassContinuation.Estar, E_star]

/-- The selected `Gwin` coordinate as an explicit open-window integral with
the weight written first. -/
private lemma gwin_eq_window_integral (k : ℕ) (h : ℝ → ℂ) (z : ℂ) :
    preAnchorGwinTransformCoordinate (selectedFerrersPreAnchorIndex k) h z =
      ∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
          (selectedFerrersPaperLambda k),
        (u : ℂ) ^ (-Complex.I * z - 1) * E_star h u := by
  rw [preAnchorGwinTransformCoordinate, EStarMuntzZeroMassContinuation.Gwin,
    lambda_m_idx_eq, muntz_Estar_eq]
  exact setIntegral_congr_fun measurableSet_Ioo fun u _ => mul_comm _ _

/-! ## Mellin convergence of the factor-four target (re-proved locally) -/

private lemma continuousOn_E_star_four :
    ContinuousOn (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
      (Set.Ioi (0:ℝ)) := by
  rw [E_star_four_mul_eq]
  exact continuousOn_const.mul continuousOn_E_star

private lemma locallyIntegrableOn_E_star_four :
    LocallyIntegrableOn
      (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
      (Set.Ioi (0:ℝ)) :=
  continuousOn_E_star_four.locallyIntegrableOn measurableSet_Ioi

private lemma E_star_four_isBigO_atTop :
    (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x)) =O[atTop]
      (fun u : ℝ => u ^ (-(7/2) : ℝ)) := by
  rw [E_star_four_mul_eq]
  exact E_star_isBigO_atTop.const_mul_left (4 : ℂ)

private lemma E_star_four_isBigO_zero :
    (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x)) =O[𝓝[>] (0:ℝ)]
      (fun u : ℝ => u ^ ((7:ℝ)/2)) := by
  rw [E_star_four_mul_eq]
  exact E_star_isBigO_zero.const_mul_left (4 : ℂ)

/-- Local Mellin convergence of the factor-four target at the exact
coordinate, for every point of the open centered strip.  The upstream
convergence facts are private and cannot be imported; nothing is assumed. -/
private lemma mellinConvergent_E_star_four {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    MellinConvergent (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
      (-Complex.I * z) := by
  have him : |z.im| < 1/2 := hz
  obtain ⟨h1, h2⟩ := abs_lt.mp him
  apply mellinConvergent_of_isBigO_rpow (a := 7/2) (b := -(7/2))
    locallyIntegrableOn_E_star_four E_star_four_isBigO_atTop
  · rw [neg_I_mul_re]
    linarith
  · simpa using E_star_four_isBigO_zero
  · rw [neg_I_mul_re]
    linarith

/-- The three-piece split of `centeredXi` through the ratified L73.5 Mellin
identity and the public crosswalk decomposition. -/
private lemma centeredXi_eq_lower_add_window_add_upper (k : ℕ) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    centeredXi z =
      lowerMellinTail (selectedFerrersPaperLambda k)
          (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
          (-Complex.I * z) +
        windowedMellin (selectedFerrersPaperLambda k)
          (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
          (-Complex.I * z) +
        upperMellinTail (selectedFerrersPaperLambda k)
          (E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x))
          (-Complex.I * z) := by
  rw [← mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi hz]
  exact mellin_eq_lower_add_window_add_upper (lambda_ge_one k)
    (mellinConvergent_E_star_four hz)

/-- The windowed Mellin transform as an explicit open-window integral. -/
private lemma windowedMellin_eq_Ioo_integral (k : ℕ) (f : ℝ → ℂ) (s : ℂ) :
    windowedMellin (selectedFerrersPaperLambda k) f s =
      ∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
          (selectedFerrersPaperLambda k),
        (u : ℂ) ^ (s - 1) * f u := by
  have hlam0 : 0 < selectedFerrersPaperLambda k := lambda_pos k
  have hinv0 : (0:ℝ) < (selectedFerrersPaperLambda k)⁻¹ := by positivity
  rw [windowedMellin, sourceWindow]
  simp only [mellin]
  have hpt : ∀ t : ℝ, (t:ℂ) ^ (s - 1) •
      (Set.Icc (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)).indicator f t =
      (Set.Icc (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)).indicator
        (fun t : ℝ => (t:ℂ) ^ (s - 1) • f t) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t),
    setIntegral_indicator measurableSet_Icc]
  have hinter : Set.Ioi (0:ℝ) ∩
      Set.Icc (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k) =
      Set.Icc (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k) :=
    Set.inter_eq_right.mpr (fun u hu => lt_of_lt_of_le hinv0 hu.1)
  rw [hinter, MeasureTheory.integral_Icc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun u _ => by
    rw [smul_eq_mul]

/-! ## Finite window truncation of the source comb -/

/-- The source packet vanishes strictly beyond the window. -/
private lemma comb_zero_beyond_window (k : ℕ) {x : ℝ}
    (hx : selectedFerrersPaperLambda k < x) :
    prolateCombination (selectedFerrersPreAnchorPair k) x = 0 := by
  have hlameq := selectedFerrersPreAnchorPair_lambda_eq_paperLambda k
  have hnotmem : x ∉ Set.Icc
      (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda := by
    rw [hlameq]
    intro hmem
    linarith [hmem.2]
  have h0z : (selectedFerrersPreAnchorPair k).h0 x = 0 := by
    by_contra hne
    exact hnotmem ((selectedFerrersPreAnchorPair k).h0_support
      (Function.mem_support.mpr hne))
  have h4z : (selectedFerrersPreAnchorPair k).h4 x = 0 := by
    by_contra hne
    exact hnotmem ((selectedFerrersPreAnchorPair k).h4_support
      (Function.mem_support.mpr hne))
  rw [prolateCombination_apply, h0z, h4z]
  simp

/-- On the open source window the starred comb of the selected packet is the
finite sum over at most `k + 2` active dilates. -/
private lemma E_star_comb_eq_finite_on_window (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioo (selectedFerrersPaperLambda k)⁻¹
      (selectedFerrersPaperLambda k)) :
    E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u =
      ((Real.sqrt u : ℝ) : ℂ) *
        ∑ j ∈ Finset.range (k + 2),
          prolateCombination (selectedFerrersPreAnchorPair k)
            (((j + 1 : ℕ) : ℝ) * u) := by
  have hlam0 : 0 < selectedFerrersPaperLambda k := lambda_pos k
  have hinv0 : (0:ℝ) < (selectedFerrersPaperLambda k)⁻¹ := by positivity
  have hu0 : 0 < u := lt_trans hinv0 hu.1
  have hsq := selectedFerrersPaperLambda_sq k
  set emb : ℕ ↪ ℕ+ := ⟨Nat.succPNat, fun a b hab => by
    have := congrArg (fun p : ℕ+ => (p : ℕ)) hab
    simpa using this⟩ with hemb
  set S : Finset ℕ+ := (Finset.range (k + 2)).map emb with hS
  have hsourceZero : ∀ n : ℕ+, n ∉ S →
      prolateCombination (selectedFerrersPreAnchorPair k)
        (((n : ℕ) : ℝ) * u) = 0 := by
    intro n hn
    have hnK : k + 2 < (n : ℕ) := by
      by_contra hle
      push_neg at hle
      apply hn
      rw [hS, Finset.mem_map]
      refine ⟨(n : ℕ) - 1, ?_, ?_⟩
      · rw [Finset.mem_range]
        have := n.pos
        omega
      · have := n.pos
        have hcoe : ((emb ((n : ℕ) - 1) : ℕ+) : ℕ) = (n : ℕ) := by
          rw [hemb]
          simp [Nat.succPNat]
          omega
        exact PNat.coe_injective hcoe
    apply comb_zero_beyond_window
    have h3 : ((k + 3 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hnK
    have hstep : selectedFerrersPaperLambda k ≤
        ((k + 3 : ℕ) : ℝ) * (selectedFerrersPaperLambda k)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hlam0]
      calc selectedFerrersPaperLambda k * selectedFerrersPaperLambda k
          = (selectedFerrersPaperLambda k) ^ 2 := by ring
        _ = ((k + 2 : ℕ) : ℝ) := hsq
        _ ≤ ((k + 3 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : k + 2 ≤ k + 3)
    calc selectedFerrersPaperLambda k
        ≤ ((k + 3 : ℕ) : ℝ) * (selectedFerrersPaperLambda k)⁻¹ := hstep
      _ < ((k + 3 : ℕ) : ℝ) * u := by
          apply mul_lt_mul_of_pos_left hu.1
          positivity
      _ ≤ ((n : ℕ) : ℝ) * u := mul_le_mul_of_nonneg_right h3 hu0.le
  rw [E_star]
  congr 1
  rw [(hasSum_sum_of_ne_finset_zero hsourceZero).tsum_eq, hS, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-! ## Window integrability of both sides -/

/-- The selected source packet is Bochner integrable. -/
private lemma integrable_comb (k : ℕ) :
    Integrable (prolateCombination (selectedFerrersPreAnchorPair k)) := by
  have h0 := (selectedFerrersPreAnchorPair k).h0_integrable.const_mul
    (((selectedFerrersPreAnchorPair k).I4 : ℝ) : ℂ)
  have h4 := (selectedFerrersPreAnchorPair k).h4_integrable.const_mul
    (((selectedFerrersPreAnchorPair k).I0 : ℝ) : ℂ)
  have h := (h0.sub h4).div_const
    (((selectedFerrersPreAnchorPair k).normalizingDenominator : ℝ) : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [prolateCombination_apply]
  simp [Pi.sub_apply]

/-- Continuity of the combined window weight on the open window. -/
private lemma weight_continuousOn (s : ℂ) (k : ℕ) :
    ContinuousOn
      (fun u : ℝ => (u : ℂ) ^ (s - 1) * ((Real.sqrt u : ℝ) : ℂ))
      (Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)) := by
  have hlam0 : 0 < selectedFerrersPaperLambda k := lambda_pos k
  have hinv0 : (0:ℝ) < (selectedFerrersPaperLambda k)⁻¹ := by positivity
  apply ContinuousOn.mul
  · apply continuousOn_of_forall_continuousAt
    intro u hu
    have hu0 : 0 < u := lt_trans hinv0 hu.1
    exact (continuousAt_cpow_const
      (Complex.ofReal_mem_slitPlane.2 hu0)).comp
      Complex.continuous_ofReal.continuousAt
  · exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn

/-- Window integrability of the weighted source comb: on the window the comb
is a finite sum of scaled copies of the Bochner-integrable packet, each
multiplied by a bounded continuous weight. -/
private lemma integrableOn_window_source (k : ℕ) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z - 1) *
        E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u)
      (Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)) := by
  have him : |z.im| < 1/2 := hz
  obtain ⟨him1, him2⟩ := abs_lt.mp him
  have hlam0 : 0 < selectedFerrersPaperLambda k := lambda_pos k
  have hinv0 : (0:ℝ) < (selectedFerrersPaperLambda k)⁻¹ := by positivity
  have hterm : ∀ j : ℕ, IntegrableOn
      (fun u : ℝ => ((u : ℂ) ^ (-Complex.I * z - 1) *
          ((Real.sqrt u : ℝ) : ℂ)) *
        prolateCombination (selectedFerrersPreAnchorPair k)
          (((j + 1 : ℕ) : ℝ) * u))
      (Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)) := by
    intro j
    have hcpos : (0:ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hcomp : Integrable (fun u : ℝ =>
        prolateCombination (selectedFerrersPreAnchorPair k)
          (((j + 1 : ℕ) : ℝ) * u)) :=
      (integrable_comp_mul_left_iff
        (prolateCombination (selectedFerrersPreAnchorPair k))
        hcpos.ne').mpr (integrable_comb k)
    apply MeasureTheory.Integrable.bdd_mul
      (hcomp.integrableOn)
      (((weight_continuousOn (-Complex.I * z) k).aestronglyMeasurable
        measurableSet_Ioo))
      (c := Real.sqrt (selectedFerrersPaperLambda k) *
        ((selectedFerrersPaperLambda k)⁻¹ ^ (z.im - 1)))
    rw [ae_restrict_iff' measurableSet_Ioo]
    apply ae_of_all
    intro u hu
    have hu0 : 0 < u := lt_trans hinv0 hu.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg u),
      show ((-Complex.I * z) - 1).re = z.im - 1 by
        rw [Complex.sub_re, neg_I_mul_re, Complex.one_re],
      mul_comm (u ^ (z.im - 1)) (Real.sqrt u)]
    apply mul_le_mul
    · exact Real.sqrt_le_sqrt hu.2.le
    · exact Real.rpow_le_rpow_of_nonpos hinv0 hu.1.le (by linarith)
    · exact Real.rpow_nonneg hu0.le _
    · exact Real.sqrt_nonneg _
  have hsum : IntegrableOn
      (fun u : ℝ => ∑ j ∈ Finset.range (k + 2),
        ((u : ℂ) ^ (-Complex.I * z - 1) * ((Real.sqrt u : ℝ) : ℂ)) *
          prolateCombination (selectedFerrersPreAnchorPair k)
            (((j + 1 : ℕ) : ℝ) * u))
      (Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)) :=
    MeasureTheory.integrable_finset_sum _ (fun j _ => hterm j)
  apply hsum.congr_fun ?_ measurableSet_Ioo
  intro u hu
  dsimp only
  rw [E_star_comb_eq_finite_on_window k hu]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Window integrability of the weighted factor-four target. -/
private lemma integrableOn_window_target (k : ℕ) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z - 1) *
        E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x) u)
      (Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)) := by
  have hlam0 : 0 < selectedFerrersPaperLambda k := lambda_pos k
  have hinv0 : (0:ℝ) < (selectedFerrersPaperLambda k)⁻¹ := by positivity
  have hconv := mellinConvergent_E_star_four hz
  rw [MellinConvergent] at hconv
  have hmono := hconv.mono_set
    (show Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k) ⊆ Set.Ioi (0:ℝ) from
      fun u hu => lt_trans hinv0 hu.1)
  exact hmono.congr_fun (fun u _ => by rw [smul_eq_mul]) measurableSet_Ioo

/-! ## The decisive exact split -/

/-- Window integrability of the weighted full error. -/
private lemma integrableOn_window_error (k : ℕ) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z - 1) *
        selectedFerrersFullEStarError k u)
      (Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k)) := by
  have h := ((integrableOn_window_source k hz).const_mul
    (selectedFerrersLemma73SourceScale k)).sub
    (integrableOn_window_target k hz)
  refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioo
  intro u _
  simp only [Pi.sub_apply]
  rw [selectedFerrersFullEStarError, E_star_four_mul_eq]
  ring

/-- **The decisive identity.**  For every `k` and every `z` in the open
centered strip, exactly and with no new hypothesis:

`sourceScale * Gwin - centeredXi = windowMellin(fullError) - outerTail`. -/
private lemma source_minus_target_split (k : ℕ) {z : ℂ}
    (hz : z ∈ centeredCriticalStrip) :
    selectedFerrersLemma73SourceScale k *
        preAnchorGwinTransformCoordinate (selectedFerrersPreAnchorIndex k)
          (prolateCombination (selectedFerrersPreAnchorPair k)) z -
      centeredXi z =
    (∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k),
      (u : ℂ) ^ (-Complex.I * z - 1) * selectedFerrersFullEStarError k u) -
      selectedFerrersFactorFourExplicitLimitMellinOuterTail k z := by
  have hsrc := integrableOn_window_source k hz
  have htgt := integrableOn_window_target k hz
  have hpoint : (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z - 1) *
      selectedFerrersFullEStarError k u) =
      fun u : ℝ =>
        selectedFerrersLemma73SourceScale k *
          ((u : ℂ) ^ (-Complex.I * z - 1) *
            E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u) -
        (u : ℂ) ^ (-Complex.I * z - 1) *
          E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x) u := by
    funext u
    rw [selectedFerrersFullEStarError, E_star_four_mul_eq]
    ring
  have hint : (∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
      (selectedFerrersPaperLambda k),
      (u : ℂ) ^ (-Complex.I * z - 1) * selectedFerrersFullEStarError k u) =
      selectedFerrersLemma73SourceScale k *
        (∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
            (selectedFerrersPaperLambda k),
          (u : ℂ) ^ (-Complex.I * z - 1) *
            E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u) -
      (∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
          (selectedFerrersPaperLambda k),
        (u : ℂ) ^ (-Complex.I * z - 1) *
          E_star (fun x : ℝ => (4 : ℂ) * explicitCCMLimitH x) u) := by
    rw [hpoint, integral_sub (hsrc.const_mul _) htgt,
      MeasureTheory.integral_const_mul]
  rw [hint, ← gwin_eq_window_integral,
    ← windowedMellin_eq_Ioo_integral,
    centeredXi_eq_lower_add_window_add_upper k hz,
    selectedFerrersFactorFourExplicitLimitMellinOuterTail]
  ring

/-! ## The closed-substrip two-term rate -/

/-- The window Mellin error obeys the exact two-term power rate on each
fixed closed substrip. -/
private lemma window_error_norm_le (k : ℕ) {z : ℂ} {σ Cf : ℝ}
    (hσ0 : 0 ≤ σ) (hσ : σ < 1/2) (hzim : |z.im| ≤ σ) (hCf : 0 ≤ Cf)
    (herr : ∀ u ∈ sourceWindow (selectedFerrersPaperLambda k),
        ‖selectedFerrersFullEStarError k u‖ ≤
          Cf / (selectedFerrersPaperLambda k * Real.sqrt u)) :
    ‖∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k),
      (u : ℂ) ^ (-Complex.I * z - 1) *
        selectedFerrersFullEStarError k u‖ ≤
      Cf * ((selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) / (σ + 1/2) +
        (selectedFerrersPaperLambda k)⁻¹ / (1/2 - σ)) := by
  obtain ⟨hy1, hy2⟩ := abs_le.mp hzim
  have hzs : z ∈ centeredCriticalStrip := by
    exact lt_of_le_of_lt hzim hσ
  have hlam0 : 0 < selectedFerrersPaperLambda k := lambda_pos k
  have hlam1 : 1 < selectedFerrersPaperLambda k := lambda_gt_one k
  have hinv0 : (0:ℝ) < (selectedFerrersPaperLambda k)⁻¹ := by positivity
  have hinv1 : (selectedFerrersPaperLambda k)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hlam1
  set lam : ℝ := selectedFerrersPaperLambda k with hlamdef
  have hint := integrableOn_window_error k hzs
  -- the exact norm of the integrand on the window
  have hnorm : ∀ u ∈ Set.Ioo lam⁻¹ lam,
      ‖(u : ℂ) ^ (-Complex.I * z - 1) *
        selectedFerrersFullEStarError k u‖ ≤
      (Cf / lam) * u ^ (z.im - 3/2 : ℝ) := by
    intro u hu
    have hu0 : 0 < u := lt_trans hinv0 hu.1
    have huw : u ∈ sourceWindow lam := ⟨hu.1.le, hu.2.le⟩
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
      show ((-Complex.I * z) - 1).re = z.im - 1 by
        rw [Complex.sub_re, neg_I_mul_re, Complex.one_re]]
    calc u ^ (z.im - 1) * ‖selectedFerrersFullEStarError k u‖
        ≤ u ^ (z.im - 1) * (Cf / (lam * Real.sqrt u)) := by
          apply mul_le_mul_of_nonneg_left (herr u huw)
            (Real.rpow_nonneg hu0.le _)
      _ = (Cf / lam) * u ^ (z.im - 3/2 : ℝ) := by
          rw [Real.sqrt_eq_rpow,
            show (z.im - 3/2 : ℝ) = (z.im - 1) + (-(1/2)) by ring,
            Real.rpow_add hu0, Real.rpow_neg hu0.le]
          field_simp
  -- split the window at u = 1
  have hunion : Set.Ioo lam⁻¹ lam =
      Set.Ioo lam⁻¹ 1 ∪ Set.Ico 1 lam :=
    (Set.Ioo_union_Ico_eq_Ioo hinv1 hlam1.le).symm
  have hdisj : Disjoint (Set.Ioo lam⁻¹ (1:ℝ)) (Set.Ico (1:ℝ) lam) :=
    Set.disjoint_left.mpr fun u hu1 hu2 => absurd hu1.2 (not_lt.mpr hu2.1)
  have hsub1 : Set.Ioo lam⁻¹ (1:ℝ) ⊆ Set.Ioo lam⁻¹ lam :=
    Set.Ioo_subset_Ioo_right hlam1.le
  have hsub2 : Set.Ico (1:ℝ) lam ⊆ Set.Ioo lam⁻¹ lam :=
    fun u hu => ⟨lt_of_lt_of_le hinv1 hu.1, hu.2⟩
  rw [hunion, setIntegral_union hdisj measurableSet_Ico
    (hint.mono_set hsub1) (hint.mono_set hsub2)]
  refine le_trans (norm_add_le _ _) ?_
  -- lower piece
  have hmaj1cont : ContinuousOn
      (fun u : ℝ => (Cf / lam) * u ^ (-σ - 3/2 : ℝ))
      (Set.Icc lam⁻¹ 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply continuousOn_of_forall_continuousAt
    intro u hu
    exact Real.continuousAt_rpow_const u _
      (Or.inl (ne_of_gt (lt_of_lt_of_le hinv0 hu.1)))
  have hmaj1int : IntegrableOn
      (fun u : ℝ => (Cf / lam) * u ^ (-σ - 3/2 : ℝ))
      (Set.Ioo lam⁻¹ 1) :=
    (hmaj1cont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hbound1 : ‖∫ u in Set.Ioo lam⁻¹ 1,
      (u : ℂ) ^ (-Complex.I * z - 1) *
        selectedFerrersFullEStarError k u‖ ≤
      (Cf / lam) * (lam ^ (σ + 1/2 : ℝ) / (σ + 1/2)) := by
    have hle : ‖∫ u in Set.Ioo lam⁻¹ 1,
        (u : ℂ) ^ (-Complex.I * z - 1) *
          selectedFerrersFullEStarError k u‖ ≤
        ∫ u in Set.Ioo lam⁻¹ 1, (Cf / lam) * u ^ (-σ - 3/2 : ℝ) := by
      apply norm_integral_le_of_norm_le hmaj1int
      rw [ae_restrict_iff' measurableSet_Ioo]
      apply ae_of_all
      intro u hu
      have hu0 : 0 < u := lt_trans hinv0 hu.1
      refine le_trans (hnorm u (hsub1 hu)) ?_
      apply mul_le_mul_of_nonneg_left ?_ (div_nonneg hCf hlam0.le)
      apply Real.rpow_le_rpow_of_exponent_ge hu0 hu.2.le
      linarith
    refine le_trans hle ?_
    rw [MeasureTheory.integral_const_mul]
    apply mul_le_mul_of_nonneg_left ?_ (div_nonneg hCf hlam0.le)
    have hne1 : (-σ - 3/2 : ℝ) ≠ -1 := by
      intro h
      linarith
    have hnmem : (0:ℝ) ∉ Set.uIcc lam⁻¹ (1:ℝ) := by
      intro hmem
      rw [Set.uIcc_of_le hinv1.le] at hmem
      exact absurd hmem.1 (not_le.mpr hinv0)
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hinv1.le,
      integral_rpow (Or.inr ⟨hne1, hnmem⟩), Real.one_rpow,
      show (-σ - 3/2 : ℝ) + 1 = -(σ + 1/2) by ring,
      Real.inv_rpow hlam0.le, Real.rpow_neg hlam0.le, inv_inv]
    have hden1 : (0:ℝ) < σ + 1/2 := by linarith
    have heq : (1 - lam ^ (σ + 1/2 : ℝ)) / (-(σ + 1/2)) =
        (lam ^ (σ + 1/2 : ℝ) - 1) / (σ + 1/2) := by
      field_simp
      ring
    rw [heq]
    gcongr
    linarith [Real.rpow_pos_of_pos hlam0 (σ + 1/2 : ℝ)]
  -- upper piece
  have hmaj2int : IntegrableOn
      (fun u : ℝ => (Cf / lam) * u ^ (σ - 3/2 : ℝ)) (Set.Ici (1:ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have hbound2 : ‖∫ u in Set.Ico 1 lam,
      (u : ℂ) ^ (-Complex.I * z - 1) *
        selectedFerrersFullEStarError k u‖ ≤
      (Cf / lam) * (1 / (1/2 - σ)) := by
    have hle : ‖∫ u in Set.Ico 1 lam,
        (u : ℂ) ^ (-Complex.I * z - 1) *
          selectedFerrersFullEStarError k u‖ ≤
        ∫ u in Set.Ico 1 lam, (Cf / lam) * u ^ (σ - 3/2 : ℝ) := by
      apply norm_integral_le_of_norm_le
        (hmaj2int.mono_set (fun u hu => hu.1))
      rw [ae_restrict_iff' measurableSet_Ico]
      apply ae_of_all
      intro u hu
      have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu.1
      refine le_trans (hnorm u (hsub2 hu)) ?_
      apply mul_le_mul_of_nonneg_left ?_ (div_nonneg hCf hlam0.le)
      apply Real.rpow_le_rpow_of_exponent_le hu.1
      linarith
    refine le_trans hle ?_
    have hmono : (∫ u in Set.Ico 1 lam,
        (Cf / lam) * u ^ (σ - 3/2 : ℝ)) ≤
        ∫ u in Set.Ici 1, (Cf / lam) * u ^ (σ - 3/2 : ℝ) := by
      apply setIntegral_mono_set hmaj2int
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
        have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu
        exact mul_nonneg (div_nonneg hCf hlam0.le)
          (Real.rpow_nonneg hu0.le _)
      · exact HasSubset.Subset.eventuallyLE (fun u hu => hu.1)
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi,
      MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) one_pos,
      show (σ - 3/2 : ℝ) + 1 = σ - 1/2 by ring, Real.one_rpow]
    apply mul_le_mul_of_nonneg_left ?_ (div_nonneg hCf hlam0.le)
    apply le_of_eq
    rw [div_eq_div_iff (ne_of_lt (by linarith : (σ - 1/2 : ℝ) < 0))
      (ne_of_gt (by linarith : (0:ℝ) < 1/2 - σ))]
    ring
  -- combine
  calc ‖∫ u in Set.Ioo lam⁻¹ 1, _‖ + ‖∫ u in Set.Ico 1 lam, _‖
      ≤ (Cf / lam) * (lam ^ (σ + 1/2 : ℝ) / (σ + 1/2)) +
        (Cf / lam) * (1 / (1/2 - σ)) := add_le_add hbound1 hbound2
    _ = Cf * (lam ^ (σ - 1/2 : ℝ) / (σ + 1/2) + lam⁻¹ / (1/2 - σ)) := by
        have hsplit : lam ^ (σ + 1/2 : ℝ) = lam ^ (σ - 1/2 : ℝ) * lam := by
          rw [show (σ + 1/2 : ℝ) = (σ - 1/2 : ℝ) + 1 by ring,
            Real.rpow_add hlam0, Real.rpow_one]
        rw [hsplit]
        have hd1 : (σ + 1/2 : ℝ) ≠ 0 := by
          intro h
          linarith
        have hd2 : (1/2 - σ : ℝ) ≠ 0 := by
          intro h
          linarith
        field_simp

/-! ## The public theorem -/

/-- **L73.7.**  On each fixed closed substrip `|z.im| ≤ σ` with
`0 ≤ σ < 1/2`, the scaled selected-Ferrers `Gwin` coordinate converges to
the production `centeredXi`, uniformly, under the explicit mode and chi
rate hypotheses.  The exact selected pair, the precommitted index schedule,
the exact factor-four source scale, the exact `Gwin` coordinate and the
production target are all literal. -/
theorem selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates
    (σ C0 C4 Cχ : ℝ)
    (hσ0 : 0 ≤ σ)
    (hσ : σ < 1 / 2)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hCχ : 0 ≤ Cχ)
    (hmode :
      ∀ᶠ k in Filter.atTop,
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
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    TendstoUniformlyOn
      (fun k z =>
        selectedFerrersLemma73SourceScale k *
          preAnchorGwinTransformCoordinate
            (selectedFerrersPreAnchorIndex k)
            (prolateCombination (selectedFerrersPreAnchorPair k)) z)
      centeredXi
      Filter.atTop
      {z : ℂ | |z.im| ≤ σ} := by
  obtain ⟨C1, hC1nn, hev1⟩ :=
    selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  obtain ⟨C2, hC2nn, hev2⟩ := selectedFerrersExplicitTargetTail_bound
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have houter :=
    selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff] at houter
  have houter2 := houter (ε/2) (by linarith)
  set Cf : ℝ := C1 + C2 with hCfdef
  have hCfnn : 0 ≤ Cf := add_nonneg hC1nn hC2nn
  have hden1 : (0:ℝ) < σ + 1/2 := by linarith
  have hden2 : (0:ℝ) < 1/2 - σ := by linarith
  set Crate : ℝ := Cf * (1/(σ + 1/2) + 1/(1/2 - σ)) with hCratedef
  have hCratenn : 0 ≤ Crate := by positivity
  have hlim : Tendsto (fun k : ℕ =>
      (selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ)) atTop (nhds 0) := by
    have heq : ∀ k : ℕ, (selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) =
        (((k + 2 : ℕ) : ℝ)) ^ (-((1/2 - σ)/2)) := by
      intro k
      rw [selectedFerrersPaperLambda, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((k + 2 : ℕ) : ℝ))]
      congr 1
      ring
    have hneg : Tendsto (fun x : ℝ => x ^ (-((1/2 - σ)/2))) atTop
        (nhds 0) := tendsto_rpow_neg_atTop (by linarith)
    have hnat : Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    exact (hneg.comp hnat).congr fun k => (heq k).symm
  have hrtend : Tendsto (fun k : ℕ =>
      Crate * (selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ)) atTop
      (nhds 0) := by
    simpa using hlim.const_mul Crate
  have hev3 := hrtend.eventually_lt_const (show (0:ℝ) < ε/2 by linarith)
  filter_upwards [hev1, hev2, houter2, hev3] with k hk1 hk2 hkO hkR
  intro z hzσ
  have hzim : |z.im| ≤ σ := hzσ
  have hzs : z ∈ centeredCriticalStrip := lt_of_le_of_lt hzim hσ
  have herr : ∀ u ∈ sourceWindow (selectedFerrersPaperLambda k),
      ‖selectedFerrersFullEStarError k u‖ ≤
        Cf / (selectedFerrersPaperLambda k * Real.sqrt u) := by
    intro u hu
    rw [selectedFerrersFullEStarError_eq_main_sub_targetTail k hu]
    calc ‖selectedFerrersEStarWindowMainError k u -
        selectedFerrersExplicitTargetTail k u‖
        ≤ ‖selectedFerrersEStarWindowMainError k u‖ +
          ‖selectedFerrersExplicitTargetTail k u‖ := norm_sub_le _ _
      _ ≤ C1 / (selectedFerrersPaperLambda k * Real.sqrt u) +
          C2 / (selectedFerrersPaperLambda k * Real.sqrt u) :=
          add_le_add (hk1 u hu) (hk2 u hu)
      _ = Cf / (selectedFerrersPaperLambda k * Real.sqrt u) := by
          rw [hCfdef, add_div]
  have hW := window_error_norm_le k hσ0 hσ hzim hCfnn herr
  have hchain : Cf * ((selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) /
      (σ + 1/2) + (selectedFerrersPaperLambda k)⁻¹ / (1/2 - σ)) ≤
      Crate * (selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) := by
    have hbase : (selectedFerrersPaperLambda k)⁻¹ ≤
        (selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (lambda_ge_one k)
        (by linarith)
    have hpownn : (0:ℝ) ≤
        (selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) :=
      Real.rpow_nonneg (lambda_pos k).le _
    rw [hCratedef,
      show Cf * (1/(σ + 1/2) + 1/(1/2 - σ)) *
          (selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) =
        Cf * ((selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) / (σ + 1/2) +
          (selectedFerrersPaperLambda k) ^ (σ - 1/2 : ℝ) / (1/2 - σ)) by
        ring]
    gcongr
  rw [dist_eq_norm, norm_sub_rev, source_minus_target_split k hzs]
  have hT : ‖selectedFerrersFactorFourExplicitLimitMellinOuterTail k z‖ <
      ε/2 := by
    have h := hkO z hzs
    rwa [dist_zero_left] at h
  calc ‖(∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
        (selectedFerrersPaperLambda k),
        (u : ℂ) ^ (-Complex.I * z - 1) *
          selectedFerrersFullEStarError k u) -
      selectedFerrersFactorFourExplicitLimitMellinOuterTail k z‖
      ≤ ‖∫ u in Set.Ioo (selectedFerrersPaperLambda k)⁻¹
          (selectedFerrersPaperLambda k),
          (u : ℂ) ^ (-Complex.I * z - 1) *
            selectedFerrersFullEStarError k u‖ +
        ‖selectedFerrersFactorFourExplicitLimitMellinOuterTail k z‖ :=
        norm_sub_le _ _
    _ < ε/2 + ε/2 :=
        add_lt_add_of_le_of_lt (lt_of_le_of_lt (le_trans hW hchain) hkR).le hT
    _ = ε := by ring

#print axioms selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates

end Q3.RouteB.D0Pstar

end
