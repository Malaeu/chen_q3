import Q3.Proofs.RouteB.G6N1SelectedFerrersEStarWindowMainError
import Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter Complex

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# L73.4 — the explicit target tail beyond the source window

Floor `L73_4_EXPLICIT_TARGET_SUPPORT_TAIL` of verdict `405777bc`.

A C04 support-category repair: the selected packet is literally
zero-extended outside `[-lambda_k, lambda_k]`, while the target
`explicitCCMLimitH` is a noncompact polynomial-Gaussian.  The full starred
difference is therefore NOT the L73.3 main error — the target comb keeps
running past the dynamic source cutoff, and the omitted terms must be named
and bounded, not dismissed as negligible.  This file proves the exact split

`full error = main error − target tail`,

with the tail indexed by `mainCount + n + 1`, and bounds the tail by
`C / (lambda * sqrt u)` using only a local inverse-four polynomial-Gaussian
decay (proved here from scratch — the upstream inverse-square fact is
private and not importable) and ordinary inverse-square summability.  No
exponential-tail machinery and no numerical constants.

LEDGER:
  CLOSES: [EXPLICIT_CCM_LIMIT_ESTAR_BEYOND_PROLATE_WINDOW_TAIL,
           SELECTED_FERRERS_FULL_ESTAR_POINTWISE_ERROR_DECOMPOSITION]
  OPENS:  []
-/

/-- **The plant.**  A target term strictly beyond the dynamic source count is
invisible to the main sum: the count is a support fact about the source, not
about the target. -/
private theorem dynamicMainCount_does_not_cover_noncompact_target_plant :
    ((∑ n ∈ Finset.range 1,
        (if n + 1 = 2 then (1 : ℂ) else 0)) = 0) ∧
      ((∑ n ∈ Finset.range 2,
        (if n + 1 = 2 then (1 : ℂ) else 0)) = 1) := by
  constructor
  · rw [Finset.sum_range_one]
    norm_num
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num

/-! ## Local inverse-four polynomial-Gaussian decay -/

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

/-- Fourth-power exponential moment: `s^4 * e^(-s) ≤ 256`. -/
private theorem s4_exp_bound (s : ℝ) (hs : 0 ≤ s) :
    s ^ 4 * Real.exp (-s) ≤ 256 := by
  have hq : s * Real.exp (-(s / 4)) ≤ 4 := exp_linear_bound' 4 s (by norm_num) hs
  have h0 : 0 ≤ s * Real.exp (-(s / 4)) := by positivity
  have hpow : (s * Real.exp (-(s / 4))) ^ 4 ≤ 4 ^ 4 := by
    exact pow_le_pow_left₀ h0 hq 4
  have hexp4 : Real.exp (-(s / 4)) ^ 4 = Real.exp (-s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc s ^ 4 * Real.exp (-s)
      = (s * Real.exp (-(s / 4))) ^ 4 := by
        rw [mul_pow, hexp4]
    _ ≤ 4 ^ 4 := hpow
    _ = 256 := by norm_num

/-- Third-power exponential moment: `s^3 * e^(-s) ≤ 27`. -/
private theorem s3_exp_bound (s : ℝ) (hs : 0 ≤ s) :
    s ^ 3 * Real.exp (-s) ≤ 27 := by
  have hq : s * Real.exp (-(s / 3)) ≤ 3 := exp_linear_bound' 3 s (by norm_num) hs
  have h0 : 0 ≤ s * Real.exp (-(s / 3)) := by positivity
  have hpow : (s * Real.exp (-(s / 3))) ^ 3 ≤ 3 ^ 3 := by
    exact pow_le_pow_left₀ h0 hq 3
  have hexp3 : Real.exp (-(s / 3)) ^ 3 = Real.exp (-s) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc s ^ 3 * Real.exp (-s)
      = (s * Real.exp (-(s / 3))) ^ 3 := by
        rw [mul_pow, hexp3]
    _ ≤ 3 ^ 3 := hpow
    _ = 27 := by norm_num

/-- **Local inverse-four decay** of the target on the positive axis:
`‖explicitCCMLimitH x‖ * x^4 ≤ 33` for all `x`, hence
`‖explicitCCMLimitH x‖ ≤ 33 / x^4` for `x > 0`.  The substitution
`s = pi * x^2` is exact — no large-`x` restriction is needed. -/
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

/-! ## The shifted target tail and the full error -/

/-- **The explicit target tail**: the `sqrt u`-weighted target comb beyond
the dynamic source count, indexed by `mainCount + n + 1`. -/
noncomputable def selectedFerrersExplicitTargetTail
    (k : ℕ) (u : ℝ) : ℂ :=
  ((Real.sqrt u : ℝ) : ℂ) *
    ∑' n : ℕ,
      (4 : ℂ) * explicitCCMLimitH
        ((((selectedFerrersEStarMainCount k u + n + 1 : ℕ) : ℝ) * u))

/-- **The full E-star error** of the ported packet against the target. -/
noncomputable def selectedFerrersFullEStarError
    (k : ℕ) (u : ℝ) : ℂ :=
  selectedFerrersLemma73SourceScale k *
      E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u -
    (4 : ℂ) * E_star explicitCCMLimitH u

/-! ## Summability of the shifted target comb -/

private theorem target_comb_norm_bound (k : ℕ) {u : ℝ} (hu0 : 0 < u)
    (hlam : 0 < selectedFerrersPaperLambda k)
    (hMgt : selectedFerrersPaperLambda k <
      ((selectedFerrersEStarMainCount k u + 1 : ℕ) : ℝ) * u) :
    ∀ n : ℕ,
      ‖(4 : ℂ) * explicitCCMLimitH
          ((((selectedFerrersEStarMainCount k u + n + 1 : ℕ) : ℝ) * u))‖
        ≤ 132 / ((selectedFerrersPaperLambda k) ^ 2 * u ^ 2) *
            (1 / ((n : ℝ) + 1) ^ 2) := by
  intro n
  set M : ℕ := selectedFerrersEStarMainCount k u with hM
  set r : ℝ := ((M + n + 1 : ℕ) : ℝ) * u with hr
  have hrpos : 0 < r := by
    rw [hr]
    positivity
  have hrgtlam : selectedFerrersPaperLambda k < r := by
    rw [hr]
    have h1 : ((M + 1 : ℕ) : ℝ) ≤ ((M + n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    calc selectedFerrersPaperLambda k
        < ((M + 1 : ℕ) : ℝ) * u := hMgt
      _ ≤ ((M + n + 1 : ℕ) : ℝ) * u := mul_le_mul_of_nonneg_right h1 hu0.le
  have hrge : ((n : ℝ) + 1) * u ≤ r := by
    rw [hr]
    have h1 : ((n : ℝ) + 1) ≤ ((M + n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) M]
    exact mul_le_mul_of_nonneg_right h1 hu0.le
  have hdecay := explicitCCMLimitH_inverse_four_decay r hrpos
  have hnorm4 : ‖(4 : ℂ)‖ = 4 := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  have hr4 : (selectedFerrersPaperLambda k) ^ 2 * (((n : ℝ) + 1) * u) ^ 2
      ≤ r ^ 4 := by
    have h1 : (selectedFerrersPaperLambda k) ^ 2 ≤ r ^ 2 := by
      nlinarith [hlam, hrgtlam]
    have h2 : (((n : ℝ) + 1) * u) ^ 2 ≤ r ^ 2 := by
      have hnn : 0 ≤ ((n : ℝ) + 1) * u := by positivity
      nlinarith [hrge, hnn]
    calc (selectedFerrersPaperLambda k) ^ 2 * (((n : ℝ) + 1) * u) ^ 2
        ≤ r ^ 2 * r ^ 2 := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = r ^ 4 := by ring
  have hchain : 33 / r ^ 4
      ≤ 33 / ((selectedFerrersPaperLambda k) ^ 2 * (((n : ℝ) + 1) * u) ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) ?_ hr4
    positivity
  rw [norm_mul, hnorm4]
  calc 4 * ‖explicitCCMLimitH r‖
      ≤ 4 * (33 / r ^ 4) := mul_le_mul_of_nonneg_left hdecay (by norm_num)
    _ ≤ 4 * (33 / ((selectedFerrersPaperLambda k) ^ 2 * (((n : ℝ) + 1) * u) ^ 2)) :=
        mul_le_mul_of_nonneg_left hchain (by norm_num)
    _ = 132 / ((selectedFerrersPaperLambda k) ^ 2 * u ^ 2) *
          (1 / ((n : ℝ) + 1) ^ 2) := by
        field_simp
        ring

private theorem inverse_square_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h := Real.summable_one_div_nat_pow.mpr (le_refl 2)
  have h2 := (summable_nat_add_iff 1).mpr h
  refine h2.congr fun n => ?_
  push_cast
  ring_nf

/-! ## The theorems -/

/-- **L73.4, the exact split.**  On the source window, the full E-star error
is the main error minus the explicit target tail. -/
theorem selectedFerrersFullEStarError_eq_main_sub_targetTail
    (k : ℕ) {u : ℝ}
    (hu : u ∈ sourceWindow (selectedFerrersPaperLambda k)) :
    selectedFerrersFullEStarError k u =
      selectedFerrersEStarWindowMainError k u -
        selectedFerrersExplicitTargetTail k u := by
  have hlam : 0 < selectedFerrersPaperLambda k := by
    rw [selectedFerrersPaperLambda]
    apply Real.sqrt_pos.mpr
    positivity
  have hu0 : 0 < u := by
    have h1 : (selectedFerrersPaperLambda k)⁻¹ ≤ u := hu.1
    have h2 : 0 < (selectedFerrersPaperLambda k)⁻¹ := by positivity
    linarith
  set M : ℕ := selectedFerrersEStarMainCount k u with hM
  have hMgt : selectedFerrersPaperLambda k < ((M + 1 : ℕ) : ℝ) * u := by
    have hfl : selectedFerrersPaperLambda k / u < ((M + 1 : ℕ) : ℝ) := by
      rw [hM, selectedFerrersEStarMainCount]
      push_cast
      exact Nat.lt_floor_add_one _
    calc selectedFerrersPaperLambda k
        = (selectedFerrersPaperLambda k / u) * u := by field_simp
      _ < ((M + 1 : ℕ) : ℝ) * u := mul_lt_mul_of_pos_right hfl hu0
  -- the source packet vanishes strictly beyond the window
  have hcombzero : ∀ x : ℝ, selectedFerrersPaperLambda k < x →
      prolateCombination (selectedFerrersPreAnchorPair k) x = 0 := by
    intro x hx
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
  -- the finite source support set
  set emb : ℕ ↪ ℕ+ := ⟨Nat.succPNat, fun a b hab => by
    have := congrArg (fun p : ℕ+ => (p : ℕ)) hab
    simpa using this⟩ with hemb
  set S : Finset ℕ+ := (Finset.range M).map emb with hS
  have hsourceZero : ∀ n : ℕ+, n ∉ S →
      prolateCombination (selectedFerrersPreAnchorPair k)
        (((n : ℕ) : ℝ) * u) = 0 := by
    intro n hn
    have hnM : M < (n : ℕ) := by
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
    apply hcombzero
    have h1 : ((M + 1 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hnM
    calc selectedFerrersPaperLambda k
        < ((M + 1 : ℕ) : ℝ) * u := hMgt
      _ ≤ ((n : ℕ) : ℝ) * u := mul_le_mul_of_nonneg_right h1 hu0.le
  -- source side: E_star equals the finite main comb
  have hsourceEq : E_star
      (prolateCombination (selectedFerrersPreAnchorPair k)) u
      = ((Real.sqrt u : ℝ) : ℂ) *
        ∑ j ∈ Finset.range M,
          prolateCombination (selectedFerrersPreAnchorPair k)
            (((j + 1 : ℕ) : ℝ) * u) := by
    rw [E_star]
    congr 1
    rw [(hasSum_sum_of_ne_finset_zero hsourceZero).tsum_eq, hS, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  -- target side: reindex to ℕ and split at M
  have htargetSummable : Summable (fun j : ℕ =>
      (4 : ℂ) * explicitCCMLimitH (((j + 1 : ℕ) : ℝ) * u)) := by
    apply Summable.of_norm
    have hbound : ∀ j : ℕ,
        ‖(4 : ℂ) * explicitCCMLimitH (((j + 1 : ℕ) : ℝ) * u)‖
          ≤ 132 / u ^ 4 * (1 / ((j : ℝ) + 1) ^ 4) := by
      intro j
      have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) * u := by positivity
      have hdecay := explicitCCMLimitH_inverse_four_decay _ hjpos
      have hnorm4 : ‖(4 : ℂ)‖ = 4 := by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs]
        norm_num
      rw [norm_mul, hnorm4]
      calc 4 * ‖explicitCCMLimitH (((j + 1 : ℕ) : ℝ) * u)‖
          ≤ 4 * (33 / (((j + 1 : ℕ) : ℝ) * u) ^ 4) :=
            mul_le_mul_of_nonneg_left hdecay (by norm_num)
        _ = 132 / u ^ 4 * (1 / ((j : ℝ) + 1) ^ 4) := by
            push_cast
            field_simp
            ring
    apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound
    apply Summable.mul_left
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 2 ≤ 4)
    have h2 := (summable_nat_add_iff 1).mpr h
    refine h2.congr fun n => ?_
    push_cast
    ring_nf
  have htargetEq : E_star explicitCCMLimitH u
      = ((Real.sqrt u : ℝ) : ℂ) *
        ∑' j : ℕ, explicitCCMLimitH (((j + 1 : ℕ) : ℝ) * u) := by
    rw [E_star]
    congr 1
    rw [← Equiv.tsum_eq (Equiv.pnatEquivNat).symm
      (fun n : ℕ+ => explicitCCMLimitH (((n : ℕ) : ℝ) * u))]
    apply tsum_congr
    intro j
    congr 2
  have htargetSummable' : Summable (fun j : ℕ =>
      explicitCCMLimitH (((j + 1 : ℕ) : ℝ) * u)) := by
    have := htargetSummable.div_const 4
    refine this.congr fun j => ?_
    rw [mul_comm, mul_div_assoc]
    norm_num
  have hsplit := htargetSummable'.sum_add_tsum_nat_add M
  -- the tail with argument alignment `(i + M) + 1 = M + i + 1`
  have hsplitEq : (∑' j : ℕ, explicitCCMLimitH (((j + 1 : ℕ) : ℝ) * u))
      = (∑ j ∈ Finset.range M, explicitCCMLimitH (((j + 1 : ℕ) : ℝ) * u))
        + ∑' n : ℕ, explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u)) := by
    rw [← hsplit]
    congr 1
    apply tsum_congr
    intro n
    have hidx : (n + M + 1 : ℕ) = (M + n + 1 : ℕ) := by omega
    rw [hidx]
  have htail4 : (∑' n : ℕ,
      (4 : ℂ) * explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u)))
      = (4 : ℂ) * ∑' n : ℕ,
        explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u)) := tsum_mul_left
  -- assemble
  rw [selectedFerrersFullEStarError, selectedFerrersEStarWindowMainError,
    selectedFerrersExplicitTargetTail, ← hM,
    hsourceEq, htargetEq, hsplitEq, htail4]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  generalize (∑ j ∈ Finset.range M,
    prolateCombination (selectedFerrersPreAnchorPair k)
      (((j + 1 : ℕ) : ℝ) * u)) = SQ
  generalize (∑ j ∈ Finset.range M,
    explicitCCMLimitH (((j + 1 : ℕ) : ℝ) * u)) = SH
  generalize (∑' n : ℕ,
    explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u))) = T
  ring

/-- **L73.4, the tail bound.**  The explicit target tail is
`O(1 / (lambda * sqrt u))`, uniformly over the source window. -/
theorem selectedFerrersExplicitTargetTail_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in Filter.atTop,
        ∀ u ∈ sourceWindow (selectedFerrersPaperLambda k),
          ‖selectedFerrersExplicitTargetTail k u‖ ≤
            C / (selectedFerrersPaperLambda k * Real.sqrt u) := by
  set Z : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  refine ⟨132 * Z, by positivity, ?_⟩
  filter_upwards with k
  intro u hu
  have hlam : 0 < selectedFerrersPaperLambda k := by
    rw [selectedFerrersPaperLambda]
    apply Real.sqrt_pos.mpr
    positivity
  have hu0 : 0 < u := by
    have h1 : (selectedFerrersPaperLambda k)⁻¹ ≤ u := hu.1
    have h2 : 0 < (selectedFerrersPaperLambda k)⁻¹ := by positivity
    linarith
  have hlu : 1 ≤ selectedFerrersPaperLambda k * u := by
    have h1 : (selectedFerrersPaperLambda k)⁻¹ ≤ u := hu.1
    calc (1 : ℝ) = selectedFerrersPaperLambda k *
        (selectedFerrersPaperLambda k)⁻¹ := by field_simp
      _ ≤ selectedFerrersPaperLambda k * u :=
          mul_le_mul_of_nonneg_left h1 hlam.le
  set M : ℕ := selectedFerrersEStarMainCount k u with hM
  have hMgt : selectedFerrersPaperLambda k < ((M + 1 : ℕ) : ℝ) * u := by
    have hfl : selectedFerrersPaperLambda k / u < ((M + 1 : ℕ) : ℝ) := by
      rw [hM, selectedFerrersEStarMainCount]
      push_cast
      exact Nat.lt_floor_add_one _
    calc selectedFerrersPaperLambda k
        = (selectedFerrersPaperLambda k / u) * u := by field_simp
      _ < ((M + 1 : ℕ) : ℝ) * u := mul_lt_mul_of_pos_right hfl hu0
  have hbound := target_comb_norm_bound k hu0 hlam hMgt
  have hdomSummable : Summable (fun n : ℕ =>
      132 / ((selectedFerrersPaperLambda k) ^ 2 * u ^ 2) *
        (1 / ((n : ℝ) + 1) ^ 2)) :=
    inverse_square_summable.mul_left _
  have hnormSummable : Summable (fun n : ℕ =>
      ‖(4 : ℂ) * explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hdomSummable
  have htsumBound : ‖∑' n : ℕ,
      (4 : ℂ) * explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u))‖
      ≤ 132 / ((selectedFerrersPaperLambda k) ^ 2 * u ^ 2) * Z := by
    calc ‖∑' n : ℕ, (4 : ℂ) * explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u))‖
        ≤ ∑' n : ℕ,
          ‖(4 : ℂ) * explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u))‖ :=
          norm_tsum_le_tsum_norm hnormSummable
      _ ≤ ∑' n : ℕ, 132 / ((selectedFerrersPaperLambda k) ^ 2 * u ^ 2) *
            (1 / ((n : ℝ) + 1) ^ 2) :=
          hnormSummable.tsum_le_tsum hbound hdomSummable
      _ = 132 / ((selectedFerrersPaperLambda k) ^ 2 * u ^ 2) * Z := by
          rw [hZ, tsum_mul_left]
  rw [selectedFerrersExplicitTargetTail]
  rw [norm_mul]
  have hsnorm : ‖((Real.sqrt u : ℝ) : ℂ)‖ = Real.sqrt u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg u)]
  rw [hsnorm]
  set s : ℝ := Real.sqrt u with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu0
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hchain : s * (132 / ((selectedFerrersPaperLambda k) ^ 2 * u ^ 2) * Z)
      ≤ 132 * Z / (selectedFerrersPaperLambda k * s) := by
    rw [← hs2]
    have hineq : s * (132 / ((selectedFerrersPaperLambda k) ^ 2 * (s ^ 2) ^ 2) * Z)
        = 132 * Z / (selectedFerrersPaperLambda k * s) *
          (1 / (selectedFerrersPaperLambda k * s ^ 2)) := by
      field_simp
    rw [hineq]
    have hls : 1 ≤ selectedFerrersPaperLambda k * s ^ 2 := by
      rw [hs2]
      exact hlu
    have hfrac : 1 / (selectedFerrersPaperLambda k * s ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hls
    calc 132 * Z / (selectedFerrersPaperLambda k * s) *
        (1 / (selectedFerrersPaperLambda k * s ^ 2))
        ≤ 132 * Z / (selectedFerrersPaperLambda k * s) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 132 * Z / (selectedFerrersPaperLambda k * s) := mul_one _
  calc s * ‖∑' n : ℕ,
      (4 : ℂ) * explicitCCMLimitH ((((M + n + 1 : ℕ) : ℝ) * u))‖
      ≤ s * (132 / ((selectedFerrersPaperLambda k) ^ 2 * u ^ 2) * Z) :=
        mul_le_mul_of_nonneg_left htsumBound hs0.le
    _ ≤ 132 * Z / (selectedFerrersPaperLambda k * s) := hchain
    _ = 132 * Z / (selectedFerrersPaperLambda k * Real.sqrt u) := by rw [hsdef]

#print axioms selectedFerrersFullEStarError_eq_main_sub_targetTail
#print axioms selectedFerrersExplicitTargetTail_bound

end Q3.RouteB.D0Pstar

end
