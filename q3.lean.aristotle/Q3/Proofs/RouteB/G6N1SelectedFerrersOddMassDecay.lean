import Q3.Proofs.RouteB.G6N1SelectedFerrersH2aSourceQuantities
import Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail
import Q3.Proofs.RouteB.D0PstarInversionCoefficientCrosswalk

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
# H2a.3 — the selected Ferrers odd-mass decay

Floor `H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY` of verdict `89f10e98`.

The first substantive cofinal quantitative input for the H2A.1 receiver:
the exact selected-shell odd mass obeys

`η_k ≤ C · log(m_k) / sqrt(m_k) → 0`,

derived from the already-ratified L73 mode/chi inputs — no free odd-mass
hypothesis anywhere.  The route: the public final-shell/pre-anchor rank
crosswalk; the full pointwise `E⋆` error `C/(λ√u)` from L73.3 + L73.4;
its square integrated in the exact `dStar = du/u` unit over the source
window (`O(1/λ)`, not `O(log λ/λ)`); the exactly inversion-even factor-four
target through `E_star_explicitCCMLimitH_inv`, giving reflected retained
coefficients via `inner_V_neg_eq_inner_V_of_inversion_even` without
symmetrizing the selected row; the projected-norm floor `Ω(1/L)` from the
central zero-mode anchor `preAnchorGwin_zero_eq_sqrtL_mul_innerV0`, the
selected-shell `muntzLimit` at `z = 0` and `centeredXi_zero_ne_zero`
(pointwise `sourceScale_ne` alone is insufficient — the plant records the
failure); and finite Bessel over the exact orthonormal modes.

The scale cancels between the physical approximation error and the
projected norm: the final bound is scale-invariant.

Deliberately NOT here: residual rate, sector floors, cofinal effective
floor, simple ground, Theorem 5.10, real zeros.

LEDGER:
  CLOSES: [SELECTED_FERRERS_FINAL_SHELL_TO_PREANCHOR_RANK_CROSSWALK,
           SELECTED_FERRERS_ODD_MASS_LOG_OVER_SQRT_RATE,
           SELECTED_FERRERS_ODD_MASS_DECAY]
  OPENS:  []
-/

/-! ## The public final-shell / pre-anchor rank crosswalk -/

/-- The recovered pre-anchor rank of the theorem-generated final shell:
the selected schedule stores `m = rank + 2`. -/
noncomputable def selectedFerrersCofinalPreAnchorRank
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) : ℕ :=
  ((selectedFerrersCofinalSourceData P).index k).m - 2

/-- The final-shell index is the precommitted pre-anchor index at the
recovered rank. -/
theorem selectedFerrersCofinalSourceData_index_eq_preAnchorIndex
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    (selectedFerrersCofinalSourceData P).index k =
      selectedFerrersPreAnchorIndex
        (selectedFerrersCofinalPreAnchorRank P k) := rfl

/-- The final-shell pair is the precommitted pre-anchor pair at the
recovered rank. -/
theorem selectedFerrersCofinalSourceData_pair_eq_preAnchorPair
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    (selectedFerrersCofinalSourceData P).pair k =
      selectedFerrersPreAnchorPair
        (selectedFerrersCofinalPreAnchorRank P k) := rfl

/-- The final-shell source scale is the port scale at the recovered rank. -/
theorem selectedFerrersCofinalSourceData_sourceScale_eq_preAnchorScale
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ) :
    (selectedFerrersCofinalSourceData P).sourceScale k =
      P.sourceScale (selectedFerrersCofinalPreAnchorRank P k) := rfl

/-- The recovered rank is cofinal. -/
theorem selectedFerrersCofinalPreAnchorRank_tendsto
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData) :
    Tendsto (selectedFerrersCofinalPreAnchorRank P) atTop atTop := by
  have hm := (selectedFerrersCofinalSourceData P).mCofinal
  rw [tendsto_atTop_atTop] at hm ⊢
  intro b
  obtain ⟨N0, hN0⟩ := hm (b + 2)
  refine ⟨N0, fun a ha => ?_⟩
  have := hN0 a ha
  unfold selectedFerrersCofinalPreAnchorRank
  omega

/-! ## The mandatory plant -/

/-- **The plant.**  A vanishing unnormalized error without an anchor floor
does not control the normalized odd mass: on `Fin 2` with the reflection
`diag(1, -1)`, the raw vectors `p_n = (0, 1/(n+1))` have squared norm
tending to zero (hence vanishing error to the zero even target), yet the
normalization `(n+1) • p_n` is always the pure odd unit vector `(0, 1)`
with odd mass one.  Any proof dividing by a merely pointwise nonzero
projected norm dies here; the central-anchor lower bound is
load-bearing. -/
private theorem vanishing_unnormalized_error_without_anchor_does_not_control_normalized_oddMass_plant :
    ∃ (J : Matrix (Fin 2) (Fin 2) ℂ) (p : ℕ → Fin 2 → ℂ),
      J.IsHermitian ∧ J * J = 1 ∧
      Tendsto (fun n => (star (p n) ⬝ᵥ p n).re) atTop (nhds 0) ∧
      (∀ n : ℕ, ((n : ℂ) + 1) • p n = ![0, 1]) ∧
      star (![0, 1] : Fin 2 → ℂ) ⬝ᵥ (![0, 1] : Fin 2 → ℂ) = 1 ∧
      (star ((2⁻¹ : ℂ) • ((![0, 1] : Fin 2 → ℂ) -
          (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![0, 1])) ⬝ᵥ
        ((2⁻¹ : ℂ) • ((![0, 1] : Fin 2 → ℂ) -
          (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![0, 1]))).re
        = 1 := by
  classical
  refine ⟨!![1, 0; 0, -1], fun n => ![0, ((n : ℂ) + 1)⁻¹],
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show _ᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have hval : ∀ n : ℕ,
        (star (![0, ((n : ℂ) + 1)⁻¹] : Fin 2 → ℂ) ⬝ᵥ
          ![0, ((n : ℂ) + 1)⁻¹]).re = (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
      intro n
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      have h : star (![0, ((n : ℂ) + 1)⁻¹] : Fin 2 → ℂ) ⬝ᵥ
          ![0, ((n : ℂ) + 1)⁻¹] =
          (((1 : ℝ) / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
        simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          RCLike.star_def, map_zero, map_inv₀]
        rw [show (starRingEnd ℂ) ((n : ℂ) + 1) = ((n : ℂ) + 1) by
          rw [map_add, map_one]
          congr 1
          exact Complex.conj_natCast n]
        push_cast
        field_simp
        norm_num
      rw [h, Complex.ofReal_re]
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop := by
      apply (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
        atTop (nhds 0) := by
      simpa [one_div] using h1.inv_tendsto_atTop
    exact hlim.congr fun n => (hval n).symm
  · intro n
    funext j
    have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    fin_cases j <;> simp [hne]
  · simp [dotProduct, Fin.sum_univ_two]
  · have hJv : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        (![0, 1] : Fin 2 → ℂ) = ![0, -1] := by
      funext l
      fin_cases l <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hJv]
    have hvec : (2⁻¹ : ℂ) • ((![0, 1] : Fin 2 → ℂ) -
        (![0, -1] : Fin 2 → ℂ)) = ![0, 1] := by
      funext l
      fin_cases l <;> simp <;> norm_num
    rw [hvec]
    simp [dotProduct, Fin.sum_univ_two]


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

private lemma G_inversion_even (i : PairIndex) :
    ∀ u ∈ I_m i,
      (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x)) u⁻¹ =
        (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x)) u := by
  intro u hu
  have hu0 : 0 < u := Im_subset_Ioi i hu
  rw [E_star_four_mul_eq]
  show (4:ℂ) * E_star explicitCCMLimitH u⁻¹ =
    (4:ℂ) * E_star explicitCCMLimitH u
  congr 1
  have h := E_star_explicitCCMLimitH_inv u⁻¹ (by positivity)
  rw [inv_inv] at h
  exact h.symm

/-! ## Projection and coefficient identities -/

private lemma inner_V_P_eq (i : PairIndex) (x : H_m i) {n : ℤ}
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

private lemma c_n_eq_sT_inner (i : PairIndex) (hT : ℝ → ℂ)
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
  exact inner_V_P_eq i (gTrial_m i hT hE) hn

private lemma label_mem_modeSet (i : PairIndex) (j : CCMModeFinite i.N) :
    ccmModeFinite i.N j ∈ modeSet i := by
  have h := ccmModeFinite_range i.N j
  unfold modeSet
  exact Finset.mem_Icc.mpr h

private lemma neg_label_mem_modeSet (i : PairIndex) (j : CCMModeFinite i.N) :
    -(ccmModeFinite i.N j) ∈ modeSet i := by
  have h := ccmModeFinite_range i.N j
  unfold modeSet
  rw [Finset.mem_Icc]
  omega

private lemma zero_mem_modeSet (i : PairIndex) : (0:ℤ) ∈ modeSet i := by
  unfold modeSet
  rw [Finset.mem_Icc]
  omega

private lemma L_m_pos (i : PairIndex) : 0 < L_m i := by
  have h := i.hm
  show (0:ℝ) < Real.log i.m
  apply Real.log_pos
  exact_mod_cast (by omega : 1 < i.m)

/-! ## The scale-cancelling coefficient difference -/

/-- The exactly inversion-even factor-four target as an element of the
window Hilbert space. -/
private noncomputable def targetG (i : PairIndex) : H_m i :=
  MemLp.toLp (E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x)) (memLp_G i)

/-- The scaled physical approximation error inside the window Hilbert
space: the ported source packet minus the inversion-even target. -/
private noncomputable def errVec (i : PairIndex) (hT : ℝ → ℂ)
    (hE : MemLp (E_star hT) 2 (dStar.restrict (I_m i)))
    (s : ℂ) : H_m i :=
  s • gTrial_m i hT hE - targetG i

/-- The decisive coefficient identity: the source scale times the retained
coefficient difference is the trial normalizer times the difference of the
error inner products.  The even target cancels exactly through the
inversion crosswalk — the selected row is never symmetrized. -/
private lemma sourceScale_mul_coeff_diff
    (i : PairIndex) (hT : ℝ → ℂ)
    (hE : MemLp (E_star hT) 2 (dStar.restrict (I_m i)))
    (hNz : TrialNonzero i hT hE)
    (s : ℂ) (j : CCMModeFinite i.N) :
    s * (c_n i hT hE hNz (ccmModeFinite i.N j) -
        c_n i hT hE hNz (ccmModeFinite i.N (ccmNegFinite i.N j))) =
      ((sTrial_m_N i hT hE hNz : ℝ) : ℂ) *
        (inner ℂ (V_n_m i (ccmModeFinite i.N j)) (errVec i hT hE s) -
          inner ℂ (V_n_m i (-(ccmModeFinite i.N j))) (errVec i hT hE s)) := by
  rw [ccmModeFinite_neg i.N j]
  rw [c_n_eq_sT_inner i hT hE hNz (label_mem_modeSet i j),
    c_n_eq_sT_inner i hT hE hNz (neg_label_mem_modeSet i j)]
  unfold errVec
  rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right]
  have heq : inner ℂ (V_n_m i (-(ccmModeFinite i.N j))) (targetG i) =
      inner ℂ (V_n_m i (ccmModeFinite i.N j)) (targetG i) :=
    inner_V_neg_eq_inner_V_of_inversion_even i (ccmModeFinite i.N j) _
      (memLp_G i) (G_inversion_even i)
  rw [heq]
  ring

/-! ## Finite Bessel over the exact orthonormal modes -/

private lemma normSq_sub_le (x y : ℂ) :
    Complex.normSq (x - y) ≤ 2 * Complex.normSq x + 2 * Complex.normSq y := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  have h := norm_sub_le x y
  have h2 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private lemma sum_labels_inner_sq_le (i : PairIndex) (x : H_m i)
    (lab : CCMModeFinite i.N → ℤ) (hinj : Function.Injective lab) :
    ∑ j : CCMModeFinite i.N, ‖inner ℂ (V_n_m i (lab j)) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  have himg : ∑ n ∈ Finset.univ.image lab, ‖inner ℂ (V_n_m i n) x‖ ^ 2 =
      ∑ j : CCMModeFinite i.N, ‖inner ℂ (V_n_m i (lab j)) x‖ ^ 2 :=
    Finset.sum_image (fun a _ b _ hab => hinj hab)
  rw [← himg]
  exact (V_n_m_orthonormal i).sum_inner_products_le x

/-! ## The odd-mass core bound -/

/-- The scale-invariant odd-mass core bound: the selected odd-mass sum is at
most the squared normalizer over the squared scale times the squared error
norm.  Bessel is applied twice, once per label family; the selected row is
kept exact throughout. -/
private lemma oddMass_core_le
    (i : PairIndex) (hT : ℝ → ℂ)
    (hE : MemLp (E_star hT) 2 (dStar.restrict (I_m i)))
    (hNz : TrialNonzero i hT hE)
    (s : ℂ) (hs : s ≠ 0) :
    ∑ j : CCMModeFinite i.N,
      Complex.normSq
        ((c_n i hT hE hNz (ccmModeFinite i.N j) -
          c_n i hT hE hNz (ccmModeFinite i.N (ccmNegFinite i.N j))) / 2) ≤
      (sTrial_m_N i hT hE hNz) ^ 2 / Complex.normSq s *
        ‖errVec i hT hE s‖ ^ 2 := by
  classical
  have hns0 : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs
  have hsT0 : (0:ℝ) ≤ sTrial_m_N i hT hE hNz := by
    show (0:ℝ) ≤ ‖gTrial_m_N i hT hE‖⁻¹
    positivity
  have h2 : Complex.normSq ((2:ℂ)) = 4 := by
    norm_num [Complex.normSq_apply]
  have hterm : ∀ j : CCMModeFinite i.N,
      Complex.normSq
        ((c_n i hT hE hNz (ccmModeFinite i.N j) -
          c_n i hT hE hNz (ccmModeFinite i.N (ccmNegFinite i.N j))) / 2) =
      (sTrial_m_N i hT hE hNz) ^ 2 / (4 * Complex.normSq s) *
        Complex.normSq
          (inner ℂ (V_n_m i (ccmModeFinite i.N j)) (errVec i hT hE s) -
            inner ℂ (V_n_m i (-(ccmModeFinite i.N j))) (errVec i hT hE s)) := by
    intro j
    have hA := congrArg Complex.normSq (sourceScale_mul_coeff_diff i hT hE hNz s j)
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal] at hA
    have hkey : Complex.normSq
        (c_n i hT hE hNz (ccmModeFinite i.N j) -
          c_n i hT hE hNz (ccmModeFinite i.N (ccmNegFinite i.N j))) =
        (sTrial_m_N i hT hE hNz) ^ 2 *
          Complex.normSq
            (inner ℂ (V_n_m i (ccmModeFinite i.N j)) (errVec i hT hE s) -
              inner ℂ (V_n_m i (-(ccmModeFinite i.N j))) (errVec i hT hE s)) /
          Complex.normSq s := by
      rw [eq_div_iff hns0.ne', sq]
      linarith [hA]
    rw [Complex.normSq_div, h2, hkey]
    field_simp
  calc ∑ j : CCMModeFinite i.N,
      Complex.normSq
        ((c_n i hT hE hNz (ccmModeFinite i.N j) -
          c_n i hT hE hNz (ccmModeFinite i.N (ccmNegFinite i.N j))) / 2)
      = ∑ j : CCMModeFinite i.N,
          (sTrial_m_N i hT hE hNz) ^ 2 / (4 * Complex.normSq s) *
            Complex.normSq
              (inner ℂ (V_n_m i (ccmModeFinite i.N j)) (errVec i hT hE s) -
                inner ℂ (V_n_m i (-(ccmModeFinite i.N j)))
                  (errVec i hT hE s)) :=
        Finset.sum_congr rfl fun j _ => hterm j
    _ = (sTrial_m_N i hT hE hNz) ^ 2 / (4 * Complex.normSq s) *
        ∑ j : CCMModeFinite i.N,
          Complex.normSq
            (inner ℂ (V_n_m i (ccmModeFinite i.N j)) (errVec i hT hE s) -
              inner ℂ (V_n_m i (-(ccmModeFinite i.N j)))
                (errVec i hT hE s)) := by
        rw [Finset.mul_sum]
    _ ≤ (sTrial_m_N i hT hE hNz) ^ 2 / (4 * Complex.normSq s) *
        (4 * ‖errVec i hT hE s‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hplus : ∑ j : CCMModeFinite i.N,
            Complex.normSq
              (inner ℂ (V_n_m i (ccmModeFinite i.N j))
                (errVec i hT hE s)) ≤ ‖errVec i hT hE s‖ ^ 2 := by
          have := sum_labels_inner_sq_le i (errVec i hT hE s)
            (ccmModeFinite i.N) (ccmModeFinite_injective i.N)
          simpa [Complex.normSq_eq_norm_sq] using this
        have hminus : ∑ j : CCMModeFinite i.N,
            Complex.normSq
              (inner ℂ (V_n_m i (-(ccmModeFinite i.N j)))
                (errVec i hT hE s)) ≤ ‖errVec i hT hE s‖ ^ 2 := by
          have := sum_labels_inner_sq_le i (errVec i hT hE s)
            (fun j => -(ccmModeFinite i.N j))
            (fun a b hab => ccmModeFinite_injective i.N (neg_injective hab))
          simpa [Complex.normSq_eq_norm_sq] using this
        calc ∑ j : CCMModeFinite i.N,
            Complex.normSq
              (inner ℂ (V_n_m i (ccmModeFinite i.N j)) (errVec i hT hE s) -
                inner ℂ (V_n_m i (-(ccmModeFinite i.N j)))
                  (errVec i hT hE s))
            ≤ ∑ j : CCMModeFinite i.N,
              (2 * Complex.normSq
                  (inner ℂ (V_n_m i (ccmModeFinite i.N j))
                    (errVec i hT hE s)) +
                2 * Complex.normSq
                  (inner ℂ (V_n_m i (-(ccmModeFinite i.N j)))
                    (errVec i hT hE s))) :=
              Finset.sum_le_sum fun j _ => normSq_sub_le _ _
          _ = 2 * ∑ j : CCMModeFinite i.N,
                Complex.normSq
                  (inner ℂ (V_n_m i (ccmModeFinite i.N j))
                    (errVec i hT hE s)) +
              2 * ∑ j : CCMModeFinite i.N,
                Complex.normSq
                  (inner ℂ (V_n_m i (-(ccmModeFinite i.N j)))
                    (errVec i hT hE s)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ ≤ 4 * ‖errVec i hT hE s‖ ^ 2 := by
              linarith [hplus, hminus]
    _ = (sTrial_m_N i hT hE hNz) ^ 2 / Complex.normSq s *
        ‖errVec i hT hE s‖ ^ 2 := by
        field_simp

/-! ## The window L² bound for the error vector -/

/-- The squared Hilbert norm of the scaled error vector is controlled by the
exact window integral: `‖e‖² ≤ Cf²/λ` from the pointwise full E-star error
`Cf/(λ√u)` in the exact `dStar = du/u` unit. -/
private lemma errVec_norm_sq_le
    (i : PairIndex) (hT : ℝ → ℂ)
    (hE : MemLp (E_star hT) 2 (dStar.restrict (I_m i)))
    (s : ℂ) (Cf : ℝ)
    (hl : 1 ≤ lambda_m i) (hCf : 0 ≤ Cf)
    (herr : ∀ u ∈ I_m i,
      ‖s * E_star hT u -
        E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u‖ ≤
        Cf / (lambda_m i * Real.sqrt u)) :
    ‖errVec i hT hE s‖ ^ 2 ≤ Cf ^ 2 / lambda_m i := by
  classical
  have hcoe : (errVec i hT hE s : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
      fun u => s * E_star hT u -
        E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u := by
    have h1 := MeasureTheory.Lp.coeFn_sub
      (s • gTrial_m i hT hE) (targetG i)
    have h2 := MeasureTheory.Lp.coeFn_smul s (gTrial_m i hT hE)
    have h3 : (gTrial_m i hT hE : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        E_star hT := MemLp.coeFn_toLp hE
    have h4 : (targetG i : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) :=
      MemLp.coeFn_toLp (memLp_G i)
    have h5 : (⇑(s • gTrial_m i hT hE) : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        fun u => s * E_star hT u := by
      filter_upwards [h2, h3] with u e2 e3
      rw [e2, Pi.smul_apply, e3, smul_eq_mul]
    filter_upwards [h1, h5, h4] with u e1 e5 e4
    show ((s • gTrial_m i hT hE - targetG i : H_m i) : ℝ → ℂ) u = _
    rw [e1, Pi.sub_apply, e5, e4]
  have hns : ‖errVec i hT hE s‖ ^ 2 =
      ∫ u, Complex.normSq
        (s * E_star hT u -
          E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u)
        ∂(dStar.restrict (I_m i)) := by
    have hpt : (fun u => (inner ℂ ((errVec i hT hE s : ℝ → ℂ) u)
        ((errVec i hT hE s : ℝ → ℂ) u) : ℂ)) =ᵐ[dStar.restrict (I_m i)]
        fun u => ((Complex.normSq
          (s * E_star hT u -
            E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u) : ℝ) : ℂ) := by
      filter_upwards [hcoe] with u hu
      rw [RCLike.inner_apply', ← Complex.normSq_eq_conj_mul_self, hu]
    have hinner : (inner ℂ (errVec i hT hE s) (errVec i hT hE s) : ℂ) =
        ((∫ u, Complex.normSq
          (s * E_star hT u -
            E_star (fun x : ℝ => (4:ℂ) * explicitCCMLimitH x) u)
          ∂(dStar.restrict (I_m i)) : ℝ) : ℂ) := by
      rw [MeasureTheory.L2.inner_def]
      rw [integral_congr_ae hpt]
      exact integral_complex_ofReal
    have hsq := inner_self_eq_norm_sq (𝕜 := ℂ) (errVec i hT hE s)
    rw [hinner] at hsq
    rw [← hsq]
    simp
  rw [hns]
  exact window_l2_integral_le i hl _ Cf hCf herr

/-! ## The central-anchor normalizer floor -/

/-- The anchor floor: an eventual lower bound `b` on the scaled central
`Gwin` value bounds the squared-normalizer-over-squared-scale ratio by
`L_m/b²`.  This is exactly where a merely pointwise nonzero projected norm
is insufficient — the plant records the failure mode. -/
private lemma normalizer_ratio_le_of_anchor
    (i : PairIndex) (hT : ℝ → ℂ)
    (hE : MemLp (E_star hT) 2 (dStar.restrict (I_m i)))
    (hNz : TrialNonzero i hT hE)
    (s : ℂ) (b : ℝ) (hb : 0 < b)
    (hanchor : b ≤ ‖s * preAnchorGwinTransformCoordinate i hT 0‖) :
    (sTrial_m_N i hT hE hNz) ^ 2 / Complex.normSq s ≤ L_m i / b ^ 2 := by
  have hL0 : 0 < L_m i := L_m_pos i
  have hsqL : 0 < Real.sqrt (L_m i) := Real.sqrt_pos.mpr hL0
  have hgN0 : 0 < ‖gTrial_m_N i hT hE‖ := hNz
  have hs : s ≠ 0 := by
    intro h0
    rw [h0, zero_mul, norm_zero] at hanchor
    linarith
  have hs0 : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hproj : inner ℂ (V_n_m i 0) (gTrial_m i hT hE) =
      inner ℂ (V_n_m i 0) ((gTrial_m_N i hT hE : H_m i)) :=
    (inner_V_P_eq i (gTrial_m i hT hE) (zero_mem_modeSet i)).symm
  have hCS : ‖inner ℂ (V_n_m i 0) (gTrial_m i hT hE)‖ ≤
      ‖gTrial_m_N i hT hE‖ := by
    rw [hproj]
    have h := norm_inner_le_norm (𝕜 := ℂ) (V_n_m i 0)
      ((gTrial_m_N i hT hE : H_m i))
    rw [(V_n_m_orthonormal i).1 0, one_mul, Submodule.norm_coe] at h
    exact h
  have hgwin := preAnchorGwin_zero_eq_sqrtL_mul_innerV0 i hT hE
  have hkey : b ≤ ‖s‖ * (Real.sqrt (L_m i) * ‖gTrial_m_N i hT hE‖) := by
    calc b ≤ ‖s * preAnchorGwinTransformCoordinate i hT 0‖ := hanchor
      _ = ‖s‖ * (Real.sqrt (L_m i) *
            ‖inner ℂ (V_n_m i 0) (gTrial_m i hT hE)‖) := by
          rw [norm_mul, hgwin, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ ‖s‖ * (Real.sqrt (L_m i) * ‖gTrial_m_N i hT hE‖) := by
          apply mul_le_mul_of_nonneg_left ?_ hs0.le
          exact mul_le_mul_of_nonneg_left hCS (Real.sqrt_nonneg _)
  have hdiv : b / Real.sqrt (L_m i) ≤ ‖s‖ * ‖gTrial_m_N i hT hE‖ := by
    rw [div_le_iff₀ hsqL]
    calc b ≤ ‖s‖ * (Real.sqrt (L_m i) * ‖gTrial_m_N i hT hE‖) := hkey
      _ = ‖s‖ * ‖gTrial_m_N i hT hE‖ * Real.sqrt (L_m i) := by ring
  have hsq : b ^ 2 / L_m i ≤ (‖s‖ * ‖gTrial_m_N i hT hE‖) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hdiv 2
    calc b ^ 2 / L_m i = (b / Real.sqrt (L_m i)) ^ 2 := by
          rw [div_pow, Real.sq_sqrt hL0.le]
      _ ≤ _ := h
  have hlhs : (sTrial_m_N i hT hE hNz) ^ 2 / Complex.normSq s =
      1 / (‖s‖ * ‖gTrial_m_N i hT hE‖) ^ 2 := by
    show (‖gTrial_m_N i hT hE‖⁻¹) ^ 2 / Complex.normSq s = _
    rw [Complex.normSq_eq_norm_sq]
    field_simp
  rw [hlhs]
  calc 1 / (‖s‖ * ‖gTrial_m_N i hT hE‖) ^ 2
      ≤ 1 / (b ^ 2 / L_m i) :=
        one_div_le_one_div_of_le (by positivity) hsq
    _ = L_m i / b ^ 2 := one_div_div _ _

/-! ## The public theorems -/

/-- **H2A.3, the quantitative rate.**  From the exact already-ratified mode
and chi rate contracts, the selected-shell odd mass is eventually at most
`C · log(m_k)/sqrt(m_k)`.  The route: full pointwise E-star error from
L73.3 + L73.4 at the recovered public rank; the exact `dStar` window
integral (`O(1/λ)`); the exactly inversion-even factor-four target; twice
Bessel on the exact selected row; and the central-anchor floor from the
selected-shell Müntz limit at `z = 0` against the nonzero `centeredXi 0`.
The source scale cancels — no normalization constant is fitted. -/
theorem selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates
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
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in Filter.atTop,
        selectedFerrersFiniteCCMOddMass P k ≤
          C * Real.log
              (((selectedFerrersCofinalSourceData P).index k).m : ℝ) /
            Real.sqrt
              (((selectedFerrersCofinalSourceData P).index k).m : ℝ) := by
  intro P
  obtain ⟨C1, hC1, hev1⟩ :=
    selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  obtain ⟨C2, hC2, hev2⟩ := selectedFerrersExplicitTargetTail_bound
  have hXi : (0:ℝ) < ‖centeredXi 0‖ :=
    norm_pos_iff.mpr centeredXi_zero_ne_zero
  refine ⟨4 * (C1 + C2) ^ 2 / ‖centeredXi 0‖ ^ 2, by positivity, ?_⟩
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
  have hfullk := (selectedFerrersCofinalPreAnchorRank_tendsto P).eventually hfull
  have hzero_mem : (0:ℂ) ∈ centeredCriticalStrip := by
    show |(0:ℂ).im| < 1 / 2
    norm_num
  have hpoint :=
    (selectedFerrersCofinalSourceData P).muntzLimit.tendsto_at hzero_mem
  have hanchor := hpoint.norm.eventually_const_le (half_lt_self hXi)
  filter_upwards [hfullk, hanchor] with k hkfull hkanch
  have hlam_eq : lambda_m ((selectedFerrersCofinalSourceData P).index k) =
      selectedFerrersPaperLambda (selectedFerrersCofinalPreAnchorRank P k) := by
    rw [selectedFerrersCofinalSourceData_index_eq_preAnchorIndex P k]
    exact lambda_paper_eq_lambda_m _
  have hIm_eq : I_m ((selectedFerrersCofinalSourceData P).index k) =
      sourceWindow
        (selectedFerrersPaperLambda (selectedFerrersCofinalPreAnchorRank P k)) := by
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
  have hcore := oddMass_core_le
    ((selectedFerrersCofinalSourceData P).index k)
    (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
    ((selectedFerrersCofinalSourceData P).eStar_memLp k)
    ((selectedFerrersCofinalSourceData P).trialNonzero k)
    ((selectedFerrersCofinalSourceData P).sourceScale k)
    ((selectedFerrersCofinalSourceData P).sourceScale_ne k)
  have hD := errVec_norm_sq_le
    ((selectedFerrersCofinalSourceData P).index k)
    (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
    ((selectedFerrersCofinalSourceData P).eStar_memLp k)
    ((selectedFerrersCofinalSourceData P).sourceScale k)
    (C1 + C2)
    (lambda_m_gen_ge_one _) (by positivity) herr
  have hEb := normalizer_ratio_le_of_anchor
    ((selectedFerrersCofinalSourceData P).index k)
    (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
    ((selectedFerrersCofinalSourceData P).eStar_memLp k)
    ((selectedFerrersCofinalSourceData P).trialNonzero k)
    ((selectedFerrersCofinalSourceData P).sourceScale k)
    (‖centeredXi 0‖ / 2) (half_pos hXi) hkanch
  have hL0 : 0 < L_m ((selectedFerrersCofinalSourceData P).index k) :=
    L_m_pos _
  have hlam0 : 0 < lambda_m ((selectedFerrersCofinalSourceData P).index k) :=
    lambda_m_gen_pos _
  have hoddeq : selectedFerrersFiniteCCMOddMass P k =
      ∑ j : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N,
        Complex.normSq
          ((c_n ((selectedFerrersCofinalSourceData P).index k)
              (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
              ((selectedFerrersCofinalSourceData P).eStar_memLp k)
              ((selectedFerrersCofinalSourceData P).trialNonzero k)
              (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j) -
            c_n ((selectedFerrersCofinalSourceData P).index k)
              (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
              ((selectedFerrersCofinalSourceData P).eStar_memLp k)
              ((selectedFerrersCofinalSourceData P).trialNonzero k)
              (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N
                (ccmNegFinite
                  ((selectedFerrersCofinalSourceData P).index k).N j))) / 2) :=
    rfl
  calc selectedFerrersFiniteCCMOddMass P k
      ≤ (sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k)) ^ 2 /
          Complex.normSq ((selectedFerrersCofinalSourceData P).sourceScale k) *
          ‖errVec ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)
            ((selectedFerrersCofinalSourceData P).sourceScale k)‖ ^ 2 := by
        rw [hoddeq]
        exact hcore
    _ ≤ (L_m ((selectedFerrersCofinalSourceData P).index k) /
          (‖centeredXi 0‖ / 2) ^ 2) *
        ((C1 + C2) ^ 2 /
          lambda_m ((selectedFerrersCofinalSourceData P).index k)) := by
        apply mul_le_mul hEb hD (by positivity) ?_
        exact div_nonneg hL0.le (by positivity)
    _ = 4 * (C1 + C2) ^ 2 / ‖centeredXi 0‖ ^ 2 *
          Real.log (((selectedFerrersCofinalSourceData P).index k).m : ℝ) /
          Real.sqrt (((selectedFerrersCofinalSourceData P).index k).m : ℝ) := by
        have h1 : L_m ((selectedFerrersCofinalSourceData P).index k) =
            Real.log (((selectedFerrersCofinalSourceData P).index k).m : ℝ) :=
          rfl
        have h2 : lambda_m ((selectedFerrersCofinalSourceData P).index k) =
            Real.sqrt (((selectedFerrersCofinalSourceData P).index k).m : ℝ) :=
          rfl
        rw [← h1, ← h2]
        have hXine : ‖centeredXi 0‖ ≠ 0 := ne_of_gt hXi
        field_simp
        ring

/-- **H2A.3, the limit.**  The selected-shell odd mass tends to zero along
the theorem-generated schedule: `log(m)/sqrt(m) → 0` composed with the
final-shell `m`-cofinality squeezes the nonnegative odd mass. -/
theorem selectedFerrersFiniteCCMOddMass_tendsto_zero_of_modeAndChiRates
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
    Filter.Tendsto (fun k => selectedFerrersFiniteCCMOddMass P k)
      Filter.atTop (nhds 0) := by
  intro P
  obtain ⟨C, hCnn, hev⟩ :=
    selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hm : Filter.Tendsto
      (fun k => (((selectedFerrersCofinalSourceData P).index k).m : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp
      (selectedFerrersCofinalSourceData P).mCofinal
  have hlogdiv : Filter.Tendsto
      (fun x : ℝ => Real.log x / x ^ ((1:ℝ) / 2))
      Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop
      (by norm_num : (0:ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hcomp := hlogdiv.comp hm
  have hbase : Filter.Tendsto
      (fun k => Real.log
          (((selectedFerrersCofinalSourceData P).index k).m : ℝ) /
        Real.sqrt (((selectedFerrersCofinalSourceData P).index k).m : ℝ))
      Filter.atTop (nhds 0) := by
    refine hcomp.congr fun k => ?_
    show Real.log _ / _ ^ ((1:ℝ) / 2) = _
    rw [Real.sqrt_eq_rpow]
  have hbound : Filter.Tendsto
      (fun k => C * Real.log
          (((selectedFerrersCofinalSourceData P).index k).m : ℝ) /
        Real.sqrt (((selectedFerrersCofinalSourceData P).index k).m : ℝ))
      Filter.atTop (nhds 0) := by
    have h2 := hbase.const_mul C
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    rw [mul_div_assoc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound ?_ hev
  refine Filter.Eventually.of_forall fun k => ?_
  show (0:ℝ) ≤ selectedFerrersFiniteCCMOddMass P k
  unfold selectedFerrersFiniteCCMOddMass
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

#print axioms selectedFerrersCofinalSourceData_index_eq_preAnchorIndex
#print axioms selectedFerrersCofinalSourceData_pair_eq_preAnchorPair
#print axioms selectedFerrersCofinalSourceData_sourceScale_eq_preAnchorScale
#print axioms selectedFerrersCofinalPreAnchorRank_tendsto
#print axioms selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates
#print axioms selectedFerrersFiniteCCMOddMass_tendsto_zero_of_modeAndChiRates
#print axioms vanishing_unnormalized_error_without_anchor_does_not_control_normalized_oddMass_plant

end Q3.RouteB.D0Pstar

end
