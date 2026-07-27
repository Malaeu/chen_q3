import Mathlib

open scoped BigOperators
open Complex (I normSq)
open Finset Real

noncomputable section
open Classical

/-! # Fejér Shrinking-Target Bridge

We prove a finite Fourier-analytic inequality that bounds the number of elements γ in a
finite set Γ satisfying ‖αγ‖ ≤ ε (distance to nearest integer) in terms of exponential sums.

## Main result

`fejer_shrinking_target_bridge`: For `0 < ε ≤ 1/4`, `H = ⌊1/(2ε)⌋`,
```
#{γ ∈ Γ : ‖αγ‖ ≤ ε} ≤ 2π²ε · |Γ| + 2π²ε · ∑_{j=1}^{H-1} ‖S_α(j)‖
```
-/

-- ============================================================================
-- Definitions
-- ============================================================================

/-- Distance from a real number to the nearest integer. -/
def distToInt (x : ℝ) : ℝ := |x - round x|

/-- Complex exponential e(x) = exp(2πix). -/
def eC (x : ℝ) : ℂ := Complex.exp (2 * ↑π * I * ↑x)

/-- Dirichlet-type sum D_H(x) = ∑_{j=0}^{H-1} e(jx). -/
def dirichletSum (H : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range H, eC (↑j * x)

/-- Exponential sum S(Γ, α, j) = ∑_{γ ∈ Γ} e(j · α · γ). -/
def expSum (Γ : Finset ℝ) (α : ℝ) (j : ℕ) : ℂ :=
  ∑ γ ∈ Γ, eC (↑j * α * γ)

/-- Shrinking-target count: #{γ ∈ Γ : distToInt(αγ) ≤ ε}. -/
def shrinkCount (Γ : Finset ℝ) (α ε : ℝ) : ℕ :=
  (Γ.filter (fun γ => distToInt (α * γ) ≤ ε)).card

/-- The Fejér parameter H = ⌊1/(2ε)⌋. -/
def fejerH (ε : ℝ) : ℕ := ⌊1 / (2 * ε)⌋₊

/-
============================================================================
Section 1: Basic properties of eC
============================================================================
-/
lemma eC_zero : eC 0 = 1 := by
  unfold eC; norm_num;

lemma eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  convert Complex.exp_add ( 2 * Real.pi * Complex.I * a ) ( 2 * Real.pi * Complex.I * b ) using 1 ; ring;
  rw [ eC ];
  push_cast; ring

lemma norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC; norm_num [ Complex.norm_exp ] ;

lemma eC_conj (x : ℝ) : starRingEnd ℂ (eC x) = eC (-x) := by
  unfold eC;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

lemma eC_int (n : ℤ) : eC (↑n : ℝ) = 1 := by
  exact Complex.exp_eq_one_iff.mpr ⟨ n, by simp +decide [ mul_assoc, mul_left_comm, mul_comm ] ⟩

lemma eC_pow (x : ℝ) (n : ℕ) : eC x ^ n = eC (↑n * x) := by
  induction n <;> simp_all +decide [ pow_succ, mul_comm, mul_assoc, mul_left_comm, Complex.exp_add, Complex.exp_nat_mul ];
  · exact eC_zero.symm
  · rw [ show x * ( ( _:ℕ ) + 1 ) = x + x * ( _:ℕ ) by ring, eC_add ]

/-
============================================================================
Section 2: Properties of fejerH
============================================================================
-/
lemma fejerH_ge_two (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 4) :
    2 ≤ fejerH ε := by
  exact Nat.le_floor <| by norm_num; nlinarith [ mul_inv_cancel₀ hε_pos.ne' ] ;

lemma eps_le_half_inv_fejerH (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 4) :
    ε ≤ 1 / (2 * ↑(fejerH ε)) := by
  rw [ le_div_iff₀ ] <;> norm_num;
  · nlinarith [ show ( fejerH ε : ℝ ) ≤ 1 / ( 2 * ε ) by exact_mod_cast Nat.floor_le ( by positivity ), mul_div_cancel₀ 1 ( by positivity : ( 2 * ε ) ≠ 0 ) ];
  · exact Nat.floor_pos.mpr ( by rw [ le_div_iff₀ ] <;> linarith )

lemma inv_fejerH_le (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 4) :
    1 / ↑(fejerH ε) ≤ 4 * ε := by
  -- By definition of $fejerH$, we know that $fejerH ε ≥ 1 / (2 * ε) - 1$.
  have h_fejerH : (fejerH ε : ℝ) ≥ 1 / (2 * ε) - 1 := by
    exact le_of_lt ( Nat.sub_one_lt_floor _ );
  rw [ div_le_iff₀ ] <;> nlinarith [ one_div_mul_cancel ( by positivity : ( 2 * ε ) ≠ 0 ) ]

/-
============================================================================
Section 3: Dirichlet sum properties
============================================================================

|exp(2πix) - 1| = 2|sin(πx)|
-/
lemma norm_eC_sub_one (x : ℝ) :
    ‖eC x - 1‖ = 2 * |Real.sin (π * x)| := by
  unfold eC; norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ] ; ring;
  rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> norm_num;
  · rw [ Real.sin_sq, Real.cos_sq ] ; ring;
    norm_num [ Real.sin_sq, Real.cos_sq ] ; ring;
  · nlinarith [ Real.cos_sq' ( Real.pi * x * 2 ) ]

/-
When eC(x) ≠ 1, D_H(x) is a geometric sum.
-/
lemma dirichletSum_geom (H : ℕ) (x : ℝ) (hx : eC x ≠ 1) :
    dirichletSum H x = (eC (↑H * x) - 1) / (eC x - 1) := by
  convert geom_sum_eq ?_ H using 1;
  rotate_left;
  convert rfl;
  · exact eC_pow x H
  · assumption;
  · exact Finset.sum_congr rfl fun _ _ => by rw [ eC_pow ] ;

/-
When eC(x) = 1, D_H(x) = H.
-/
lemma dirichletSum_at_periodic (H : ℕ) (x : ℝ) (hx : eC x = 1) :
    dirichletSum H x = ↑H := by
  convert Finset.sum_const ?_;
  convert Finset.sum_congr rfl fun j hj => ?_;
  rotate_right;
  exact 1;
  · rw [ ← eC_pow, hx, one_pow ];
  · norm_num

/-
|D_H(x)| = |sin(πHx)|/|sin(πx)| when sin(πx) ≠ 0.
-/
lemma norm_dirichletSum (H : ℕ) (x : ℝ) (hx : Real.sin (π * x) ≠ 0) :
    ‖dirichletSum H x‖ = |Real.sin (π * ↑H * x)| / |Real.sin (π * x)| := by
  rw [ dirichletSum_geom H x ];
  · simp +zetaDelta at *;
    rw [ norm_eC_sub_one, norm_eC_sub_one ] ; ring;
  · contrapose! hx;
    unfold eC at hx;
    rw [ Complex.exp_eq_one_iff ] at hx;
    exact Real.sin_eq_zero_iff.mpr ( by obtain ⟨ n, hn ⟩ := hx; exact ⟨ n, by norm_num [ Complex.ext_iff ] at hn; nlinarith [ Real.pi_pos ] ⟩ )

/-
============================================================================
Section 4: Key lower bound on the Dirichlet sum
============================================================================

Key lower bound: ‖D_H(x)‖ ≥ 2H/π when distToInt(x) ≤ 1/(2H).
    This uses Jordan's inequality and sin ≤ x.
-/
lemma dirichletSum_norm_lower (H : ℕ) (x : ℝ) (hH : 1 ≤ H)
    (hx : distToInt x ≤ 1 / (2 * ↑H)) :
    2 * ↑H / π ≤ ‖dirichletSum H x‖ := by
  by_cases h : Real.sin ( Real.pi * x ) = 0;
  · -- If sin(πx) = 0, then x is an integer (use Real.sin_eq_zero_iff).
    obtain ⟨k, hk⟩ : ∃ k : ℤ, x = k := by
      exact Real.sin_eq_zero_iff.mp h |> fun ⟨ k, hk ⟩ => ⟨ k, by nlinarith [ Real.pi_pos ] ⟩;
    rw [ dirichletSum_at_periodic ] <;> norm_num [ hk ];
    · rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_gt_three, show ( H : ℝ ) ≥ 1 by norm_cast ];
    · exact eC_int k
  · rw [ norm_dirichletSum H x h ];
    -- Let $s = x - \text{round}(x)$. Then $|s| = \text{distToInt}(x) \leq 1/(2H)$.
    set s : ℝ := x - round x
    have hs : |s| ≤ 1 / (2 * H) := by
      exact hx;
    -- Since $|s| \leq 1/(2H)$ and $s \neq 0$, we have $|\sin(\pi H s)| \geq (2/\pi)|\pi H s| = 2H|s|$ and $|\sin(\pi s)| \leq |\pi s| = \pi|s|$.
    have hs_bounds : |Real.sin (Real.pi * H * s)| ≥ 2 * H * |s| ∧ |Real.sin (Real.pi * s)| ≤ Real.pi * |s| := by
      have hs_bounds : |Real.sin (Real.pi * H * s)| ≥ (2 / Real.pi) * |Real.pi * H * s| ∧ |Real.sin (Real.pi * s)| ≤ |Real.pi * s| := by
        constructor;
        · have h_sin_bound : ∀ y : ℝ, |y| ≤ Real.pi / 2 → |Real.sin y| ≥ (2 / Real.pi) * |y| := by
            exact fun y hy => Real.mul_abs_le_abs_sin hy
          apply h_sin_bound;
          rw [ abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ H ) ];
          rw [ le_div_iff₀ ] at hs <;> nlinarith [ Real.pi_pos, show ( H : ℝ ) ≥ 1 by norm_cast ];
        · exact Real.abs_sin_le_abs
      simp_all +decide [ abs_mul, mul_assoc, Real.pi_pos.le ];
      exact ⟨ by rw [ abs_of_nonneg Real.pi_pos.le ] at hs_bounds; rw [ div_mul_eq_mul_div, div_le_iff₀ ] at hs_bounds <;> nlinarith [ Real.pi_gt_three ], by rw [ abs_of_nonneg Real.pi_pos.le ] at hs_bounds; exact hs_bounds.2 ⟩;
    -- Since $|s| \leq 1/(2H)$ and $s \neq 0$, we have $|\sin(\pi H x)| = |\sin(\pi H s)|$ and $|\sin(\pi x)| = |\sin(\pi s)|$.
    have hs_eq : |Real.sin (Real.pi * H * x)| = |Real.sin (Real.pi * H * s)| ∧ |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * s)| := by
      norm_num +zetaDelta at *;
      norm_num [ mul_sub, Real.sin_sub ];
      norm_num [ mul_assoc, mul_comm Real.pi ];
      norm_num [ show Real.sin ( H * ( round x * Real.pi ) ) = 0 from Real.sin_eq_zero_iff.mpr ⟨ H * round x, by push_cast; ring ⟩, show Real.cos ( H * ( round x * Real.pi ) ) = ( -1 : ℝ ) ^ ( H * round x ) from by rw [ ← Real.rpow_intCast, eq_comm ] ; rw [ Real.rpow_def_of_nonpos ] <;> norm_num ; ring ];
    rw [ hs_eq.1, hs_eq.2, div_le_div_iff₀ ] <;> nlinarith [ Real.pi_pos, abs_pos.mpr h, show ( H : ℝ ) ≥ 1 by norm_cast ]

/-
‖D_H(x)‖² ≥ 4H²/π² when distToInt(x) ≤ 1/(2H).
-/
lemma dirichletSum_normSq_lower (H : ℕ) (x : ℝ) (hH : 1 ≤ H)
    (hx : distToInt x ≤ 1 / (2 * ↑H)) :
    4 * ↑H ^ 2 / π ^ 2 ≤ ‖dirichletSum H x‖ ^ 2 := by
  convert pow_le_pow_left₀ ( by positivity ) ( dirichletSum_norm_lower H x hH hx ) 2 using 1 ; ring

/-
============================================================================
Section 5: Bound on sum of norm-squares
============================================================================

Key expansion bound: ∑_γ ‖D_H(αγ)‖² ≤ H|Γ| + 2H ∑_{j=1}^{H-1} ‖S(j)‖
-/
lemma sum_dirichletSum_normSq_bound (Γ : Finset ℝ) (α : ℝ) (H : ℕ) (hH : 1 ≤ H) :
    ∑ γ ∈ Γ, ‖dirichletSum H (α * γ)‖ ^ 2 ≤
      ↑H * ↑(Γ.card) + 2 * ↑H * ∑ j ∈ range (H - 1), ‖expSum Γ α (j + 1)‖ := by
  -- Expanding the sum using the normSq identity.
  have h_expand : ∑ γ ∈ Γ, (‖dirichletSum H (α * γ)‖ ^ 2 : ℝ) = ∑ j ∈ Finset.range H, ∑ k ∈ Finset.range H, ∑ γ ∈ Γ, Complex.re (eC ((j - k) * α * γ)) := by
    -- By definition of norm squared, we have:
    have h_norm_sq : ∀ γ ∈ Γ, ‖dirichletSum H (α * γ)‖ ^ 2 = ∑ j ∈ Finset.range H, ∑ k ∈ Finset.range H, Complex.re (eC ((j - k) * α * γ)) := by
      intros γ hγ
      have h_dirichlet_sum : ‖dirichletSum H (α * γ)‖ ^ 2 = Complex.re (∑ j ∈ Finset.range H, ∑ k ∈ Finset.range H, eC ((j - k) * α * γ)) := by
        have h_dirichlet_sum : ‖dirichletSum H (α * γ)‖ ^ 2 = Complex.re (dirichletSum H (α * γ) * starRingEnd ℂ (dirichletSum H (α * γ))) := by
          simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
          norm_cast;
        convert h_dirichlet_sum using 1;
        unfold dirichletSum; simp +decide [ sub_mul, mul_sub, Finset.mul_sum _ _ _, Finset.sum_mul, eC_conj ] ;
        simp +decide [ eC, Complex.exp_re, Complex.exp_im, mul_sub, sub_mul ];
        simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [ Real.cos_sub ] ; ring;
      aesop;
    rw [ Finset.sum_congr rfl h_norm_sq, Finset.sum_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm;
  -- For each fixed j, the sum over k≠j has |j-k| taking values in {1,...,H-1}, with each value m appearing at most twice (for k=j-m and k=j+m).
  have h_off_diag : ∑ j ∈ Finset.range H, ∑ k ∈ Finset.range H, (∑ γ ∈ Γ, Complex.re (eC ((j - k) * α * γ))) ≤ H * Γ.card + ∑ j ∈ Finset.range H, ∑ k ∈ Finset.range H, if j ≠ k then ‖expSum Γ α (Int.natAbs (j - k))‖ else 0 := by
    have h_off_diag : ∀ j k : ℕ, j < H → k < H → j ≠ k → Complex.re (∑ γ ∈ Γ, eC ((j - k) * α * γ)) ≤ ‖expSum Γ α (Int.natAbs (j - k))‖ := by
      intros j k hj hk hjk
      have h_abs : ‖∑ γ ∈ Γ, eC ((j - k) * α * γ)‖ = ‖expSum Γ α (Int.natAbs (j - k))‖ := by
        cases le_total j k <;> simp_all +decide [ abs_of_nonneg, abs_of_nonpos, sub_mul ];
        · rw [ ← Complex.norm_conj ] ; simp +decide [ eC_conj, expSum ] ;
          rw [ abs_of_nonpos ( sub_nonpos.mpr ( Nat.cast_le.mpr ‹_› ) ) ] ; congr ; ext ; ring;
        · unfold expSum; simp +decide [ *, abs_of_nonneg, sub_mul ] ;
      exact h_abs ▸ Complex.re_le_norm _;
    refine' le_trans ( Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => _ ) _;
    use fun i j => if i = j then Γ.card else ‖expSum Γ α ( Int.natAbs ( i - j ) )‖;
    · split_ifs with h <;> simp_all +decide [ Complex.exp_re ];
      norm_num [ eC_zero ];
    · simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
      rw [ Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range.mp hx ) ] ] ; norm_num [ Finset.sum_add_distrib ];
  -- For each fixed j, the sum over k≠j has |j-k| taking values in {1,...,H-1}, with each value m appearing at most twice (for k=j-m and k=j+m). So ∑_{k≠j} ‖expSum Γ α |j-k|‖ ≤ 2 ∑_{m=1}^{H-1} ‖expSum Γ α m‖.
  have h_off_diag_bound : ∀ j ∈ Finset.range H, ∑ k ∈ Finset.range H, (if j ≠ k then ‖expSum Γ α (Int.natAbs (j - k))‖ else 0) ≤ 2 * ∑ m ∈ Finset.range (H - 1), ‖expSum Γ α (m + 1)‖ := by
    intros j hj
    have h_split : ∑ k ∈ Finset.range H, (if j ≠ k then ‖expSum Γ α (Int.natAbs (j - k))‖ else 0) = ∑ m ∈ Finset.range j, ‖expSum Γ α (j - m)‖ + ∑ m ∈ Finset.Ico (j + 1) H, ‖expSum Γ α (m - j)‖ := by
      simp +decide [ Finset.sum_ite, Finset.filter_ne ];
      rw [ show ( Finset.range H ).erase j = Finset.range j ∪ Finset.Ico ( j + 1 ) H from ?_, Finset.sum_union ];
      · refine' congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun x hx => _ ) ( Finset.sum_congr rfl fun x hx => _ ) <;> norm_cast;
        · rw [ Int.subNatNat_of_le ( Finset.mem_range_le hx ) ] ; norm_cast;
        · rw [ Int.subNatNat_eq_coe ] ; rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( by linarith [ Finset.mem_Ico.mp hx ] : j ≤ x ), abs_of_nonpos ( by linarith [ Finset.mem_Ico.mp hx ] : ( j : ℤ ) - x ≤ 0 ) ];
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp hx₁, Finset.mem_Ico.mp hx₂ ] ;
      · grind;
    -- For each fixed j, the sum over k≠j has |j-k| taking values in {1,...,H-1}, with each value m appearing at most twice (for k=j-m and k=j+m). So we can bound the sum by considering these pairs.
    have h_pair : ∑ m ∈ Finset.range j, ‖expSum Γ α (j - m)‖ ≤ ∑ m ∈ Finset.range j, ‖expSum Γ α (m + 1)‖ ∧ ∑ m ∈ Finset.Ico (j + 1) H, ‖expSum Γ α (m - j)‖ ≤ ∑ m ∈ Finset.range (H - j - 1), ‖expSum Γ α (m + 1)‖ := by
      constructor;
      · rw [ ← Finset.sum_range_reflect ];
        exact Finset.sum_le_sum fun i hi => by rw [ tsub_tsub, tsub_tsub_cancel_of_le ( by linarith [ Finset.mem_range.mp hi ] ) ] ; ring_nf; norm_num;
      · rw [ Finset.sum_Ico_eq_sum_range ];
        simp +decide [ add_assoc, Nat.sub_sub ];
        norm_num [ add_comm ];
    simp_all +decide [ two_mul, tsub_tsub ];
    exact add_le_add ( le_trans h_pair.1 ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by omega ) ) fun _ _ _ => norm_nonneg _ ) ) ( le_trans h_pair.2 ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by omega ) ) fun _ _ _ => norm_nonneg _ ) );
  exact h_expand ▸ h_off_diag.trans ( by simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum h_off_diag_bound )

/-
============================================================================
Section 6: Main theorem
============================================================================

**Fejér shrinking-target bridge**: The number of γ ∈ Γ with ‖αγ‖ ≤ ε is bounded by
    `2π²ε · |Γ| + 2π²ε · ∑_{j=1}^{H-1} ‖S_α(j)‖` where `H = ⌊1/(2ε)⌋`.
-/
theorem fejer_shrinking_target_bridge
    (Γ : Finset ℝ) (α ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 4) :
    (shrinkCount Γ α ε : ℝ) ≤
      2 * π ^ 2 * ε * ↑(Γ.card) +
      2 * π ^ 2 * ε * ∑ j ∈ range (fejerH ε - 1), ‖expSum Γ α (j + 1)‖ := by
  -- Let H = fejerH ε. By fejerH_ge_two, H ≥ 2, so H ≥ 1.
  let H := fejerH ε
  have hH_ge_two : 2 ≤ H := by
    exact fejerH_ge_two ε hε_pos hε_le
  have hH_ge_one : 1 ≤ H := by
    grind;
  -- For each γ with distToInt(α*γ) ≤ ε, we have 1 ≤ (π²/(4*H²)) * ‖D_H(α*γ)‖².
  have h_gamma_bound : ∀ γ ∈ Γ.filter (fun γ => distToInt (α * γ) ≤ ε), 1 ≤ (Real.pi ^ 2 / (4 * H ^ 2)) * ‖dirichletSum H (α * γ)‖ ^ 2 := by
    -- By the properties of the Dirichlet sum, we have ‖D_H(α*γ)‖² ≥ 4*H²/π² when distToInt(α*γ) ≤ 1/(2H).
    have h_dirichlet_bound : ∀ γ ∈ Γ.filter (fun γ => distToInt (α * γ) ≤ ε), ‖dirichletSum H (α * γ)‖ ^ 2 ≥ 4 * H ^ 2 / Real.pi ^ 2 := by
      intros γ hγ
      apply dirichletSum_normSq_lower H (α * γ) hH_ge_one;
      exact le_trans ( Finset.mem_filter.mp hγ |>.2 ) ( eps_le_half_inv_fejerH ε hε_pos hε_le );
    intro γ hγ; rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> first | positivity | nlinarith [ h_dirichlet_bound γ hγ, Real.pi_pos, show ( H : ℝ ) ≥ 2 by exact_mod_cast hH_ge_two, mul_div_cancel₀ ( 4 * ( H : ℝ ) ^ 2 ) ( ne_of_gt ( sq_pos_of_pos Real.pi_pos ) ) ] ;
  -- So shrinkCount ≤ (π²/(4*H²)) * ∑_{γ ∈ Γ} ‖D_H(α*γ)‖².
  have h_shrinkCount_bound : (shrinkCount Γ α ε : ℝ) ≤ (Real.pi ^ 2 / (4 * H ^ 2)) * ∑ γ ∈ Γ, ‖dirichletSum H (α * γ)‖ ^ 2 := by
    have h_shrinkCount_bound : (shrinkCount Γ α ε : ℝ) ≤ ∑ γ ∈ Γ.filter (fun γ => distToInt (α * γ) ≤ ε), (Real.pi ^ 2 / (4 * H ^ 2)) * ‖dirichletSum H (α * γ)‖ ^ 2 := by
      exact le_trans ( by norm_num [ shrinkCount ] ) ( Finset.sum_le_sum h_gamma_bound );
    exact h_shrinkCount_bound.trans ( by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => by positivity );
  -- By sum_dirichletSum_normSq_bound, ∑_{γ ∈ Γ} ‖D_H(α*γ)‖² ≤ H*|Γ| + 2*H * ∑_{j=1}^{H-1} ‖S(j)‖.
  have h_sum_bound : ∑ γ ∈ Γ, ‖dirichletSum H (α * γ)‖ ^ 2 ≤ H * (Γ.card : ℝ) + 2 * H * ∑ j ∈ range (H - 1), ‖expSum Γ α (j + 1)‖ := by
    convert sum_dirichletSum_normSq_bound Γ α H hH_ge_one using 1;
  -- By inv_fejerH_le, 1/H ≤ 4*ε.
  have h_inv_fejerH_le : (1 : ℝ) / H ≤ 4 * ε := by
    exact inv_fejerH_le ε hε_pos hε_le
  refine le_trans h_shrinkCount_bound ?_;
  refine le_trans ( mul_le_mul_of_nonneg_left h_sum_bound <| by positivity ) ?_;
  field_simp;
  rw [ div_le_iff₀ ] at h_inv_fejerH_le <;> nlinarith [ show ( H : ℝ ) ≥ 2 by norm_cast, show ( 0 : ℝ ) ≤ ∑ j ∈ Finset.range ( H - 1 ), ‖expSum Γ α ( j + 1 )‖ by exact Finset.sum_nonneg fun _ _ => norm_nonneg _ ]

end