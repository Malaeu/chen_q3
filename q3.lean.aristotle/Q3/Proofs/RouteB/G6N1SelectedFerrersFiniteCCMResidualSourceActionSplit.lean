import Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance
import Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail

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
# H2a.4.1a — the selected Ferrers finite Riesz source-action split

Floor `H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT` of
verdict `e0c47c3b`.

The exact source-action split behind any future residual rate: the
factor-four target and the scaled physical L73 error become window-Hilbert
vectors, both are projected into the same selected `E_m_N`, and the
shifted finite Riesz defect of the selected `kTrial` splits **exactly**
into the shifted action on the projected error plus the shifted defect of
the projected target:

`s_k • (R x_k − a_k x_k) = t_k • ((R eE_k − a_k eE_k) + (R gE_k − a_k gE_k))`,

with the norm budget
`‖s_k‖·‖R x_k − a_k x_k‖ ≤ t_k·(‖R eE_k − a_k eE_k‖ + ‖R gE_k − a_k gE_k‖)`.

**This transaction proves no rate.**  It exposes the two load-bearing
action terms which a real H2A.4.1 proof must estimate.  The two plants
record the decisive kills: a vanishing Hilbert error without a uniform
Riesz action bound does not control the residual, and an exact target
match without a target action theorem does not control it either.

Deliberately NOT here: any decay of the action terms, sector floors, an
ambient associated Weil operator or a compression claim, simple ground,
Theorem 5.10.

LEDGER:
  CLOSES: [SELECTED_FERRERS_FACTOR_FOUR_TARGET_HILBERT_OBJECT_LOCK,
           SELECTED_FERRERS_SCALED_PHYSICAL_ERROR_PROJECTION_LOCK,
           SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_EXACT_SPLIT,
           SELECTED_FERRERS_RESIDUAL_SOURCE_ACTION_BUDGET]
  OPENS:  []
-/

/-! ## The two mandatory plants -/

/-- **Plant 1.**  A vanishing Hilbert error without a uniform Riesz action
bound does not control the residual: on `Fin 2` take
`K n = diag(0, n+2)`, the exact zero-eigenvector `y = e₀`, and the unit
rows `q n = (√(1−(n+2)⁻²), (n+2)⁻¹)`.  The Hilbert error
`‖q n − y‖² → 0`, yet the Rayleigh residual energy is `1 − (n+2)⁻² ≥ 3/4`
for every `n`.  `L²` tracking without a uniform action or form-dual bound
is not residual control. -/
private theorem vanishing_Hilbert_error_without_uniform_Riesz_action_does_not_control_residual_plant :
    ∃ (K : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ → Fin 2 → ℂ)
      (y : Fin 2 → ℂ),
      (∀ n, (K n).IsHermitian) ∧
      (∀ n, K n *ᵥ y = 0) ∧
      (∀ n, star (q n) ⬝ᵥ q n = 1) ∧
      Filter.Tendsto (fun n => (star (q n - y) ⬝ᵥ (q n - y)).re)
        Filter.atTop (nhds 0) ∧
      (∀ n, 3/4 ≤
        (star (K n *ᵥ q n -
            (((star (q n) ⬝ᵥ (K n *ᵥ q n)).re : ℝ) : ℂ) • q n) ⬝ᵥ
          (K n *ᵥ q n -
            (((star (q n) ⬝ᵥ (K n *ᵥ q n)).re : ℝ) : ℂ) • q n)).re) := by
  classical
  set c : ℕ → ℝ := fun n => ((n : ℝ) + 2)⁻¹ with hc
  set b : ℕ → ℝ := fun n => Real.sqrt (1 - c n ^ 2) with hb
  have hc0 : ∀ n, 0 < c n := by
    intro n
    have : (0:ℝ) < (n : ℝ) + 2 := by positivity
    exact inv_pos.mpr this
  have hchalf : ∀ n, c n ≤ 1/2 := by
    intro n
    rw [hc]
    have h2 : (2:ℝ) ≤ (n : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    calc ((n : ℝ) + 2)⁻¹ ≤ (2:ℝ)⁻¹ :=
          (inv_le_inv₀ (by linarith) (by norm_num)).mpr h2
      _ = 1/2 := by norm_num
  have hcsq : ∀ n, c n ^ 2 ≤ 1/4 := by
    intro n
    have h1 := hchalf n
    have h0 := (hc0 n).le
    nlinarith
  have hbsq : ∀ n, b n ^ 2 = 1 - c n ^ 2 := by
    intro n
    rw [hb]
    exact Real.sq_sqrt (by nlinarith [hcsq n])
  have hb0 : ∀ n, 0 ≤ b n := fun n => Real.sqrt_nonneg _
  have hb1 : ∀ n, b n ≤ 1 := by
    intro n
    show Real.sqrt (1 - c n ^ 2) ≤ 1
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg (c n)]
  have hblow : ∀ n, 1 - c n ^ 2 ≤ b n := by
    intro n
    nlinarith [hb0 n, hb1 n, hbsq n,
      mul_nonneg (hb0 n) (sub_nonneg.mpr (hb1 n))]
  refine ⟨fun n => !![0, 0; 0, ((n : ℝ) + 2 : ℝ)],
    fun n => ![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)], ![1, 0],
    ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply]
  · intro n
    funext l
    fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro n
    have h : star (![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)] : Fin 2 → ℂ) ⬝ᵥ
        ![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)] =
        (((b n ^ 2 + c n ^ 2 : ℝ)) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_two, ← Complex.ofReal_mul]
      push_cast
      ring
    rw [h, hbsq n]
    norm_num
  · have herr : ∀ n,
        (star ((![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)] : Fin 2 → ℂ) -
            ![1, 0]) ⬝ᵥ
          ((![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)] : Fin 2 → ℂ) -
            ![1, 0])).re = (b n - 1) ^ 2 + c n ^ 2 := by
      intro n
      have h : (![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)] : Fin 2 → ℂ) -
          ![1, 0] = ![(((b n - 1 : ℝ)) : ℂ), ((c n : ℝ) : ℂ)] := by
        funext l
        fin_cases l <;> simp [Complex.ofReal_sub]
      rw [h]
      have h2 : star (![(((b n - 1 : ℝ)) : ℂ), ((c n : ℝ) : ℂ)] :
          Fin 2 → ℂ) ⬝ᵥ ![(((b n - 1 : ℝ)) : ℂ), ((c n : ℝ) : ℂ)] =
          ((((b n - 1) ^ 2 + c n ^ 2 : ℝ)) : ℂ) := by
        simp [dotProduct, Fin.sum_univ_two, ← Complex.ofReal_mul]
        push_cast
        ring
      rw [h2, Complex.ofReal_re]
    have hbound : ∀ n, (b n - 1) ^ 2 + c n ^ 2 ≤ 3 * c n ^ 2 := by
      intro n
      have h3 : 1 - b n ≤ c n ^ 2 := by nlinarith [hblow n]
      have h4 : (0:ℝ) ≤ 1 - b n := by nlinarith [hb1 n]
      nlinarith [mul_le_mul_of_nonneg_right h3 h4, hb0 n, hcsq n,
        sq_nonneg (c n)]
    have hclim : Filter.Tendsto (fun n : ℕ => c n ^ 2)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2))
          Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have h2 : Filter.Tendsto c Filter.atTop (nhds 0) := by
        rw [hc]
        exact h1.inv_tendsto_atTop
      have := h2.mul h2
      simpa [sq] using this
    have h3 : Filter.Tendsto (fun n : ℕ => 3 * c n ^ 2)
        Filter.atTop (nhds 0) := by
      have := hclim.const_mul (3:ℝ)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds h3 ?_ ?_
    · exact Filter.Eventually.of_forall fun n => by
        rw [herr n]
        positivity
    · exact Filter.Eventually.of_forall fun n => by
        rw [herr n]
        exact hbound n
  · intro n
    have hKq : (!![0, 0; 0, ((n : ℝ) + 2 : ℝ)] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        (![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)] : Fin 2 → ℂ) =
        ![0, 1] := by
      funext l
      have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
      fin_cases l <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc]
      · rw [mul_inv_cancel₀]
        exact_mod_cast hne
    have hRay : (star (![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)] : Fin 2 → ℂ) ⬝ᵥ
        (![0, 1] : Fin 2 → ℂ)).re = c n := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [hKq, hRay]
    have hres : (![0, 1] : Fin 2 → ℂ) -
        ((c n : ℝ) : ℂ) • ![((b n : ℝ) : ℂ), ((c n : ℝ) : ℂ)] =
        ![(((-(c n * b n) : ℝ)) : ℂ), (((1 - c n ^ 2 : ℝ)) : ℂ)] := by
      funext l
      fin_cases l
      · show (0:ℂ) - ((c n : ℝ) : ℂ) * ((b n : ℝ) : ℂ) =
          (((-(c n * b n) : ℝ)) : ℂ)
        push_cast
        ring
      · show (1:ℂ) - ((c n : ℝ) : ℂ) * ((c n : ℝ) : ℂ) =
          (((1 - c n ^ 2 : ℝ)) : ℂ)
        push_cast
        ring
    rw [hres]
    have hdot : (star (![(((-(c n * b n) : ℝ)) : ℂ),
        (((1 - c n ^ 2 : ℝ)) : ℂ)] : Fin 2 → ℂ) ⬝ᵥ
        ![(((-(c n * b n) : ℝ)) : ℂ), (((1 - c n ^ 2 : ℝ)) : ℂ)]).re =
        (c n * b n) ^ 2 + (1 - c n ^ 2) ^ 2 := by
      have h : star (![(((-(c n * b n) : ℝ)) : ℂ),
          (((1 - c n ^ 2 : ℝ)) : ℂ)] : Fin 2 → ℂ) ⬝ᵥ
          ![(((-(c n * b n) : ℝ)) : ℂ), (((1 - c n ^ 2 : ℝ)) : ℂ)] =
          ((((c n * b n) ^ 2 + (1 - c n ^ 2) ^ 2 : ℝ)) : ℂ) := by
        simp [dotProduct, Fin.sum_univ_two, ← Complex.ofReal_mul]
        push_cast
        ring
      rw [h, Complex.ofReal_re]
    rw [hdot]
    have hb2 := hbsq n
    have hc2 := hcsq n
    nlinarith [sq_nonneg (c n), sq_nonneg (b n)]

/-- **Plant 2.**  An exact target match without a target action theorem
does not control the residual: with `K = [[0,1,0],[1,0,1],[0,1,0]]` and
`q = y = (0,1,0)` the Hilbert error is exactly zero, yet the Rayleigh
residual energy is `2`.  Even a perfect physical approximation says
nothing about the target's own shifted finite-form defect. -/
private theorem exact_target_match_without_target_action_theorem_does_not_control_residual_plant :
    ∃ (K : Matrix (Fin 3) (Fin 3) ℂ) (q y : Fin 3 → ℂ),
      K.IsHermitian ∧ q = y ∧
      star (q - y) ⬝ᵥ (q - y) = 0 ∧
      star q ⬝ᵥ q = 1 ∧
      (star (K *ᵥ q - (((star q ⬝ᵥ (K *ᵥ q)).re : ℝ) : ℂ) • q) ⬝ᵥ
        (K *ᵥ q - (((star q ⬝ᵥ (K *ᵥ q)).re : ℝ) : ℂ) • q)).re = 2 := by
  classical
  refine ⟨!![0, 1, 0; 1, 0, 1; 0, 1, 0], ![0, 1, 0], ![0, 1, 0],
    ?_, rfl, ?_, ?_, ?_⟩
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · simp
  · simp [dotProduct, Fin.sum_univ_three]
  · have hKq : (!![0, 1, 0; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ
        (![0, 1, 0] : Fin 3 → ℂ) = ![1, 0, 1] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hRay : (star (![0, 1, 0] : Fin 3 → ℂ) ⬝ᵥ
        (![(1:ℂ), 0, 1] : Fin 3 → ℂ)).re = 0 := by
      simp [dotProduct, Fin.sum_univ_three]
    rw [hKq, hRay]
    have hvec : (![(1:ℂ), 0, 1] : Fin 3 → ℂ) -
        (((0:ℝ) : ℂ)) • (![0, 1, 0] : Fin 3 → ℂ) = ![1, 0, 1] := by
      funext l
      fin_cases l <;> simp
    rw [hvec]
    have h : star (![1, 0, 1] : Fin 3 → ℂ) ⬝ᵥ
        (![1, 0, 1] : Fin 3 → ℂ) = (((2:ℝ)) : ℂ) := by
      simp [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      norm_num
    rw [h, Complex.ofReal_re]
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


/-! ## The public window-Hilbert objects -/

/-- **The factor-four target vector**: the exact inversion-even production
target `E⋆(4·explicitCCMLimitH)` as an element of the selected window
Hilbert space. -/
noncomputable def selectedFerrersFactorFourTargetVector
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : H_m ((selectedFerrersCofinalSourceData P).index k) :=
  MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x))
    (memLp_G ((selectedFerrersCofinalSourceData P).index k))

/-- **The scaled physical error vector**: the exact L73 full E-star error
`s_k · gTrial_k − G_k` as an element of the selected window Hilbert
space. -/
noncomputable def selectedFerrersScaledPhysicalErrorVector
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : H_m ((selectedFerrersCofinalSourceData P).index k) :=
  (selectedFerrersCofinalSourceData P).sourceScale k •
      gTrial_m ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k) -
    selectedFerrersFactorFourTargetVector P k

/-- The projection of the factor-four target into the selected finite
source subspace. -/
noncomputable def selectedFerrersFactorFourTargetProjection
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : E_m_N ((selectedFerrersCofinalSourceData P).index k) :=
  P_m_N ((selectedFerrersCofinalSourceData P).index k)
    (selectedFerrersFactorFourTargetVector P k)

/-- The projection of the scaled physical error into the selected finite
source subspace. -/
noncomputable def selectedFerrersScaledPhysicalErrorProjection
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : E_m_N ((selectedFerrersCofinalSourceData P).index k) :=
  P_m_N ((selectedFerrersCofinalSourceData P).index k)
    (selectedFerrersScaledPhysicalErrorVector P k)

/-! ## The exact vector identity -/

/-- **The exact vector identity**: the scaled selected `kTrial` is the
normalizer times the sum of the projected error and the projected target,
`s_k • x_k = t_k • (eE_k + gE_k)`.  Pure projection linearity — nothing is
estimated. -/
theorem selectedFerrers_sourceScale_smul_kTrial_eq_normalizer_smul_error_add_target
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    (selectedFerrersCofinalSourceData P).sourceScale k •
      kTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)
        ((selectedFerrersCofinalSourceData P).trialNonzero k) =
      ((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) •
        (selectedFerrersScaledPhysicalErrorProjection P k +
          selectedFerrersFactorFourTargetProjection P k) := by
  classical
  have hsum : selectedFerrersScaledPhysicalErrorProjection P k +
      selectedFerrersFactorFourTargetProjection P k =
      (selectedFerrersCofinalSourceData P).sourceScale k •
        gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k) := by
    unfold selectedFerrersScaledPhysicalErrorProjection
      selectedFerrersFactorFourTargetProjection
    rw [← map_add]
    unfold selectedFerrersScaledPhysicalErrorVector
    rw [sub_add_cancel, map_smul]
    rfl
  rw [hsum]
  show (selectedFerrersCofinalSourceData P).sourceScale k •
      (((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) •
        gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)) = _
  rw [smul_comm]

/-! ## The exact shifted-action split -/

/-- **The exact source-action split**: the scaled shifted finite Riesz
defect of the selected `kTrial` is the normalizer times the sum of the
shifted action on the projected physical error and the shifted defect of
the projected factor-four target.  Pure linearity of the finite Riesz
operator — no term is estimated, no rate is claimed. -/
theorem selectedFerrersFiniteRieszDefect_sourceScale_split
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    (selectedFerrersCofinalSourceData P).sourceScale k •
      (sourceCCMFiniteRieszOperator
          ((selectedFerrersCofinalSourceData P).index k)
          (kTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).trialNonzero k)) -
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
          kTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).trialNonzero k)) =
      ((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) •
        ((sourceCCMFiniteRieszOperator
            ((selectedFerrersCofinalSourceData P).index k)
            (selectedFerrersScaledPhysicalErrorProjection P k) -
          ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
            selectedFerrersScaledPhysicalErrorProjection P k) +
          (sourceCCMFiniteRieszOperator
              ((selectedFerrersCofinalSourceData P).index k)
              (selectedFerrersFactorFourTargetProjection P k) -
            ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
              selectedFerrersFactorFourTargetProjection P k)) := by
  classical
  have hvec :=
    selectedFerrers_sourceScale_smul_kTrial_eq_normalizer_smul_error_add_target
      P k
  have hR : (selectedFerrersCofinalSourceData P).sourceScale k •
      sourceCCMFiniteRieszOperator
        ((selectedFerrersCofinalSourceData P).index k)
        (kTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k)) =
      ((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) •
        (sourceCCMFiniteRieszOperator
            ((selectedFerrersCofinalSourceData P).index k)
            (selectedFerrersScaledPhysicalErrorProjection P k) +
          sourceCCMFiniteRieszOperator
            ((selectedFerrersCofinalSourceData P).index k)
            (selectedFerrersFactorFourTargetProjection P k)) := by
    rw [← map_smul, hvec, map_smul, map_add]
  have ha : (selectedFerrersCofinalSourceData P).sourceScale k •
      (((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
        kTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k)) =
      ((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) •
        (((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
            selectedFerrersScaledPhysicalErrorProjection P k +
          ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
            selectedFerrersFactorFourTargetProjection P k) := by
    rw [smul_comm, hvec, smul_comm, smul_add]
  rw [smul_sub, hR, ha, ← smul_sub]
  congr 1
  abel

/-! ## The exact norm budget -/

/-- **The action budget**: the scaled shifted defect norm is at most the
normalizer times the sum of the two action-term norms.  This is the exact
consumer shape for H2A.4.1B; both displayed terms remain to be estimated
and neither is claimed to decay here. -/
theorem norm_sourceScale_mul_selectedFerrersFiniteRieszDefect_le_action_budget
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    ‖(selectedFerrersCofinalSourceData P).sourceScale k‖ *
      ‖(sourceCCMFiniteRieszOperator
          ((selectedFerrersCofinalSourceData P).index k)
          (kTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).trialNonzero k)) -
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
          kTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).trialNonzero k) :
          E_m_N ((selectedFerrersCofinalSourceData P).index k))‖ ≤
      sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
        (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
        ((selectedFerrersCofinalSourceData P).eStar_memLp k)
        ((selectedFerrersCofinalSourceData P).trialNonzero k) *
        (‖(sourceCCMFiniteRieszOperator
            ((selectedFerrersCofinalSourceData P).index k)
            (selectedFerrersScaledPhysicalErrorProjection P k) -
          ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
            selectedFerrersScaledPhysicalErrorProjection P k :
            E_m_N ((selectedFerrersCofinalSourceData P).index k))‖ +
          ‖(sourceCCMFiniteRieszOperator
              ((selectedFerrersCofinalSourceData P).index k)
              (selectedFerrersFactorFourTargetProjection P k) -
            ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
              selectedFerrersFactorFourTargetProjection P k :
              E_m_N ((selectedFerrersCofinalSourceData P).index k))‖) := by
  classical
  have hsplit := selectedFerrersFiniteRieszDefect_sourceScale_split P k
  have hT0 : (0:ℝ) ≤ sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)
      ((selectedFerrersCofinalSourceData P).trialNonzero k) := by
    show (0:ℝ) ≤ ‖gTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
      (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)‖⁻¹
    positivity
  rw [← norm_smul, hsplit, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hT0]
  apply mul_le_mul_of_nonneg_left (norm_add_le _ _) hT0

#print axioms selectedFerrers_sourceScale_smul_kTrial_eq_normalizer_smul_error_add_target
#print axioms selectedFerrersFiniteRieszDefect_sourceScale_split
#print axioms norm_sourceScale_mul_selectedFerrersFiniteRieszDefect_le_action_budget
#print axioms vanishing_Hilbert_error_without_uniform_Riesz_action_does_not_control_residual_plant
#print axioms exact_target_match_without_target_action_theorem_does_not_control_residual_plant

end Q3.RouteB.D0Pstar

end
