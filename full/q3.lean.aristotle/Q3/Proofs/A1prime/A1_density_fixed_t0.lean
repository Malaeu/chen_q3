/-
A1' density theorem with fixed t₀: W_K is dense in AtomCone_K_fixed.

This file uses:
- HatInterpBounded.lean: hat interpolation with bounded mesh δ ≤ δ_max
- HeatError.lean: heat kernel error bounds

The key improvement over A1_density.lean is using bounded δ to control
the heat kernel approximation error.
-/

import Q3.Proofs.A1prime.HatInterpBounded
import Q3.Proofs.A1prime.HeatError
import Q3.Proofs.A1_density

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace A1prime

/-- A1' density theorem with fixed t₀.
    For any Φ ∈ W_K and ε > 0, there exists g ∈ AtomCone_K_fixed K t₀
    such that sup|Φ - g| < ε on [-K, K].

    This version uses bounded hat interpolation to control heat kernel error. -/
theorem A1_density_WK_fixed_t0 (K : ℝ) (hK : K > 0) (t0 : ℝ) (ht0 : t0 > 0) :
    ∀ Φ ∈ W_K K, ∀ ε > 0,
      ∃ g ∈ Q3.AtomCone_K_fixed K t0,
        sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε := by
  intro Φ hΦ ε hε
  obtain ⟨hΦ_cont, hΦ_supp, hΦ_even, hΦ_nonneg⟩ := hΦ

  -- Boundary values vanish
  have hΦ_boundary : Φ (-K) = 0 ∧ Φ K = 0 := by
    constructor
    · by_contra h
      have hmem : -K ∈ Function.support Φ := by simpa [Function.mem_support] using h
      have hmem' := hΦ_supp hmem
      simp only [Set.mem_Ioo] at hmem'
      linarith [hmem'.1]
    · by_contra h
      have hmem : K ∈ Function.support Φ := by simpa [Function.mem_support] using h
      have hmem' := hΦ_supp hmem
      simp only [Set.mem_Ioo] at hmem'
      linarith [hmem'.2]

  -- Get sup norm bound M on Φ
  have hΦ_cont_on : ContinuousOn Φ (Set.Icc (-K) K) := hΦ_cont.continuousOn
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (CompactIccSpace.isCompact_Icc) hΦ_cont_on
  let M' : ℝ := max M 1
  have hM'_pos : 0 < M' := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_right _ _)
  have hM_bound : ∀ x ∈ Set.Icc (-K) K, |Φ x| ≤ M' := by
    intro x hx
    exact le_trans (by simpa [Real.norm_eq_abs] using hM x hx) (le_max_left _ _)

  -- Heat kernel at origin with fixed t₀
  let H0 : ℝ := HeatKernel t0 0
  have hH0_pos : H0 > 0 := by
    unfold H0 HeatKernel
    apply mul_pos
    · apply Real.rpow_pos_of_pos; nlinarith [Real.pi_pos, ht0]
    · exact Real.exp_pos _

  -- Get Lipschitz constant for heat kernel on [-2K, 2K]
  -- (atoms have support up to 2K when |τ| + δ ≤ K)
  have h2K_pos : 2 * K > 0 := by linarith
  obtain ⟨L, hL_pos, hL_lip⟩ := HeatKernel_LipschitzOn t0 ht0 (2 * K) h2K_pos

  -- Choose δ_max such that heat error ≤ ε/4:
  -- Key insight: |g - h_even| ≤ (L*δ/H0) * h_even ≤ (L*δ/H0) * (M' + ε/4)
  -- We need (L*δ/H0) * (M' + ε/4) ≤ ε/4
  -- So: δ ≤ ε * H0 / (4 * L * (M' + ε/4))
  let M'' : ℝ := M' + ε / 4  -- Upper bound on h_even
  have hM''_pos : M'' > 0 := by unfold M''; nlinarith [hM'_pos, hε]
  let δ_max : ℝ := ε * H0 / (4 * L * M'')
  have hδ_max_pos : δ_max > 0 := by
    unfold δ_max
    apply div_pos
    · exact mul_pos hε hH0_pos
    · nlinarith [hL_pos, hM''_pos]

  -- Step 1: Bounded hat interpolation on Φ
  have hε4 : ε / 4 > 0 := by linarith
  obtain ⟨n, τ, δ, hn_pos, hδ_pos, hδ_le_max, hτ_in, hmargin, h_hat_approx, h_hat_nonneg⟩ :=
    HatInterp.hat_interpolation_approx_bounded K hK Φ hΦ_cont.continuousOn
      (fun x _ => hΦ_nonneg x) hΦ_boundary (ε / 4) hε4 δ_max hδ_max_pos

  -- Convert FejerKernel between namespaces
  have hFejer_convert : ∀ x, HatInterp.FejerKernel δ x = FejerKernel δ x := by
    intro x
    unfold HatInterp.FejerKernel FejerKernel
    rw [max_comm]

  -- Step 2: Evenize the hat sum
  let h : ℝ → ℝ := fun x => ∑ i, Φ (τ i) * FejerKernel δ (x - τ i)
  let h_even : ℝ → ℝ := fun x => (h x + h (-x)) / 2

  have h_even_approx : ∀ x ∈ Set.Icc (-K) K, |h_even x - Φ x| < ε / 4 := by
    intro x hx
    -- Convert from HatInterp.FejerKernel to FejerKernel
    have h_hat_x : |∑ i, Φ (τ i) * HatInterp.FejerKernel δ (x - τ i) - Φ x| < ε / 4 :=
      h_hat_approx x hx
    have h_eq : ∑ i, Φ (τ i) * HatInterp.FejerKernel δ (x - τ i) =
                ∑ i, Φ (τ i) * FejerKernel δ (x - τ i) := by
      congr 1; ext i; rw [hFejer_convert]
    have h1 : |h x - Φ x| < ε / 4 := by
      unfold h
      rw [← h_eq]
      exact h_hat_x
    have hx_neg : -x ∈ Set.Icc (-K) K := by
      simp only [Set.mem_Icc] at hx ⊢
      constructor <;> linarith [hx.1, hx.2]
    have h_hat_neg : |∑ i, Φ (τ i) * HatInterp.FejerKernel δ ((-x) - τ i) - Φ (-x)| < ε / 4 :=
      h_hat_approx (-x) hx_neg
    have h_eq_neg : ∑ i, Φ (τ i) * HatInterp.FejerKernel δ ((-x) - τ i) =
                    ∑ i, Φ (τ i) * FejerKernel δ ((-x) - τ i) := by
      congr 1; ext i; rw [hFejer_convert]
    have h2 : |h (-x) - Φ (-x)| < ε / 4 := by
      unfold h
      rw [← h_eq_neg]
      exact h_hat_neg
    have h2' : |h (-x) - Φ x| < ε / 4 := by simpa [hΦ_even x] using h2
    -- |h_even x - Φ x| ≤ (|h x - Φ x| + |h (-x) - Φ x|) / 2 < ε/4
    have h_eq_form : h_even x - Φ x = ((h x - Φ x) + (h (-x) - Φ x)) / 2 := by
      unfold h_even h; ring
    have h_abs_sum := abs_add_le (h x - Φ x) (h (-x) - Φ x)
    have h_sum_lt : |h x - Φ x| + |h (-x) - Φ x| < ε / 2 := by linarith [add_lt_add h1 h2']
    calc |h_even x - Φ x|
        = |((h x - Φ x) + (h (-x) - Φ x)) / 2| := by rw [h_eq_form]
      _ = |(h x - Φ x) + (h (-x) - Φ x)| / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      _ ≤ (|h x - Φ x| + |h (-x) - Φ x|) / 2 := by
          exact div_le_div_of_nonneg_right h_abs_sum (by norm_num : (0:ℝ) ≤ 2)
      _ < (ε / 2) / 2 := by
          exact div_lt_div_of_pos_right h_sum_lt (by norm_num : (0:ℝ) < 2)
      _ = ε / 4 := by ring

  -- Step 3: Convert to Fejér×heat atoms with FIXED t₀
  -- Coefficients: c_i = Φ(τ_i) / (2 * H0)
  let c : Fin n → ℝ := fun i => Φ (τ i) / (2 * H0)

  -- The approximant g using FIXED t₀ for all atoms
  let g : ℝ → ℝ := fun x => ∑ i, c i * Atom δ t0 (τ i) x

  -- Prove g ∈ AtomCone_K_fixed K t₀
  have hg_mem : g ∈ Q3.AtomCone_K_fixed K t0 := by
    refine ⟨n, c, (fun _ => δ), τ, ?_, ?_, ?_, ?_, ?_⟩
    · -- coefficients nonnegative
      intro i
      have hΦ_nonneg_i : 0 ≤ Φ (τ i) := hΦ_nonneg (τ i)
      have hden_pos : 0 < 2 * H0 := by nlinarith [hH0_pos]
      exact div_nonneg hΦ_nonneg_i (le_of_lt hden_pos)
    · -- B_i = δ > 0
      intro _; exact hδ_pos
    · -- support control: |τ_i| + δ ≤ K
      exact hmargin
    · -- g is the sum
      intro x
      unfold g
      congr 1
      ext i
      have hAtom := Atom_eq_q3 δ t0 (τ i) x ht0
      simp [hAtom]
    · -- g ∈ W_K K
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- continuous
        apply continuous_finset_sum
        intro i _
        have hAtom_cont : Continuous (fun x => Atom δ t0 (τ i) x) := by
          unfold Atom FejerKernel HeatKernel
          apply Continuous.add <;>
          apply Continuous.mul <;>
          try exact continuous_const.max (continuous_const.sub
            ((continuous_abs.comp (continuous_sub_right _)).div_const _))
          try exact continuous_const.mul (Real.continuous_exp.comp
            (((continuous_sub_right _).pow 2).neg.div_const _))
          try exact continuous_const.max (continuous_const.sub
            ((continuous_abs.comp (continuous_add_right _)).div_const _))
          try exact continuous_const.mul (Real.continuous_exp.comp
            (((continuous_add_right _).pow 2).neg.div_const _))
        exact continuous_const.mul hAtom_cont
      · -- support ⊆ (-K, K)
        intro x hx_supp
        simp only [Function.mem_support, ne_eq] at hx_supp
        simp only [Set.mem_Ioo]
        by_contra hx_not
        have hg_zero : g x = 0 := by
          unfold g
          apply Finset.sum_eq_zero
          intro i _
          have hmargin_i := hmargin i
          have hAtom_zero : Atom δ t0 (τ i) x = 0 := by
            apply Atom_eq_zero_outside_open hK hδ_pos hmargin_i
            simp only [Set.mem_Ioo]
            exact hx_not
          simp [hAtom_zero]
        exact hx_supp hg_zero
      · -- even
        intro x
        unfold g
        congr 1
        ext i
        unfold Atom
        have hFejer_even : ∀ u, FejerKernel δ (-u) = FejerKernel δ u := by
          intro u; unfold FejerKernel; simp [abs_neg]
        have hHeat_even : ∀ u, HeatKernel t0 (-u) = HeatKernel t0 u := by
          intro u; unfold HeatKernel; simp [neg_sq]
        have h1 : -x - τ i = -(x + τ i) := by ring
        have h2 : -x + τ i = -(x - τ i) := by ring
        rw [h1, h2, hFejer_even, hHeat_even, hFejer_even, hHeat_even]
        ring
      · -- nonnegative
        intro x
        unfold g
        apply Finset.sum_nonneg
        intro i _
        apply mul_nonneg
        · have hΦ_nonneg_i : 0 ≤ Φ (τ i) := hΦ_nonneg (τ i)
          have hden_pos : 0 < 2 * H0 := by nlinarith [hH0_pos]
          exact div_nonneg hΦ_nonneg_i (le_of_lt hden_pos)
        · unfold Atom
          apply add_nonneg <;>
          apply mul_nonneg <;>
          try exact (FejerKernel_bounds δ hδ_pos _).1
          all_goals {
            unfold HeatKernel
            apply mul_nonneg
            · apply Real.rpow_nonneg; nlinarith [Real.pi_pos, ht0]
            · exact le_of_lt (Real.exp_pos _)
          }

  -- Step 4: Prove approximation bound |g - h_even| ≤ ε/2
  -- NEW APPROACH: Use h_even itself as the "mass" bound, no partition of unity needed!
  have h_g_h_even : ∀ x ∈ Set.Icc (-K) K, |g x - h_even x| ≤ ε / 2 := by
    intro x hx

    -- (A) h_even is nonnegative (sum of nonnegative terms)
    have h_even_nonneg : 0 ≤ h_even x := by
      unfold h_even h
      apply div_nonneg
      · apply add_nonneg
        · apply Finset.sum_nonneg
          intro i _
          apply mul_nonneg (hΦ_nonneg (τ i)) (FejerKernel_bounds δ hδ_pos _).1
        · apply Finset.sum_nonneg
          intro i _
          apply mul_nonneg (hΦ_nonneg (τ i)) (FejerKernel_bounds δ hδ_pos _).1
      · norm_num

    -- (B) Upper bound on h_even from approximation: h_even x ≤ Φ x + ε/4 ≤ M' + ε/4 = M''
    have h_even_le : h_even x ≤ M'' := by
      have hΦ_le : Φ x ≤ M' := by
        have hΦ_abs := hM_bound x hx
        exact le_trans (le_abs_self _) hΦ_abs
      have h_dist := h_even_approx x hx
      -- |h_even x - Φ x| < ε/4, so h_even x - Φ x < ε/4, so h_even x < Φ x + ε/4 ≤ M' + ε/4 = M''
      have h_sub : h_even x - Φ x ≤ |h_even x - Φ x| := le_abs_self _
      have h_lt : h_even x - Φ x < ε / 4 := lt_of_le_of_lt h_sub h_dist
      -- h_even x < Φ x + ε/4 ≤ M' + ε/4 = M''
      unfold M''
      linarith

    -- (C) Key bound: δ chosen so that (L*δ/H0) * M'' ≤ ε/4
    have hδ_small : (L * δ / H0) * M'' ≤ ε / 4 := by
      have hδ_le : δ ≤ δ_max := hδ_le_max
      have hL_δ : L * δ ≤ L * δ_max := mul_le_mul_of_nonneg_left hδ_le (le_of_lt hL_pos)
      -- δ_max = ε * H0 / (4 * L * M'')
      -- So L * δ_max = ε * H0 / (4 * M'')
      -- And (L * δ_max / H0) * M'' = ε/4
      have hH0_ne : H0 ≠ 0 := ne_of_gt hH0_pos
      have hM''_ne : M'' ≠ 0 := ne_of_gt hM''_pos
      have hL_ne : L ≠ 0 := ne_of_gt hL_pos
      have h4LM''_ne : (4 : ℝ) * L * M'' ≠ 0 := by nlinarith
      calc (L * δ / H0) * M''
          ≤ (L * δ_max / H0) * M'' := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hM''_pos)
              apply div_le_div_of_nonneg_right hL_δ (le_of_lt hH0_pos)
        _ = (L * (ε * H0 / (4 * L * M'')) / H0) * M'' := by rfl
        _ = ε / 4 := by field_simp [hH0_ne, hM''_ne, hL_ne, h4LM''_ne]

    -- (D) Core error bound: |g x - h_even x| ≤ (L*δ/H0) * h_even x
    -- This is the key insight: the error is proportional to h_even itself
    -- because we're replacing Heat(u)/H0 with 1, and the "mass" is h_even
    have h_core : |g x - h_even x| ≤ (L * δ / H0) * h_even x := by
      -- Rewrite h_even in the form expected by total_atom_error_even
      -- h_even x = (h x + h (-x)) / 2
      --          = (Σ Φ(τ i) * F(x - τ i) + Σ Φ(τ i) * F(-x - τ i)) / 2
      --          = Σ Φ(τ i) * (F(x - τ i) + F(-(x + τ i))) / 2
      --          = Σ Φ(τ i) * (F(x - τ i) + F(x + τ i)) / 2   (Fejér is even)

      -- Show h_even has the right form
      have h_even_form : h_even x = ∑ i, Φ (τ i) * (FejerKernel δ (x - τ i) + FejerKernel δ (x + τ i)) / 2 := by
        unfold h_even h
        -- (Σ Φ(τ i) * F(x - τ i) + Σ Φ(τ i) * F(-x - τ i)) / 2
        -- = Σ (Φ(τ i) * F(x - τ i) + Φ(τ i) * F(-x - τ i)) / 2
        -- = Σ Φ(τ i) * (F(x - τ i) + F(-x - τ i)) / 2
        -- = Σ Φ(τ i) * (F(x - τ i) + F(x + τ i)) / 2  (since F is even)
        have hFejer_even : ∀ i, FejerKernel δ ((-x) - τ i) = FejerKernel δ (x + τ i) := by
          intro i
          have h1 : (-x) - τ i = -(x + τ i) := by ring
          rw [h1]
          unfold FejerKernel
          simp only [abs_neg]
        -- Rewrite second sum using Fejér evenness
        have h_sum_eq : ∑ i, Φ (τ i) * FejerKernel δ ((-x) - τ i) =
            ∑ i, Φ (τ i) * FejerKernel δ (x + τ i) := by
          congr 1
          ext i
          rw [hFejer_even i]
        rw [h_sum_eq, ← Finset.sum_add_distrib, Finset.sum_div]
        congr 1
        ext i
        ring

      -- Show g has the right form
      have g_form : g x = ∑ i, (Φ (τ i) / (2 * H0)) *
          (FejerKernel δ (x - τ i) * HeatKernel t0 (x - τ i) +
           FejerKernel δ (x + τ i) * HeatKernel t0 (x + τ i)) := by
        unfold g c Atom
        rfl

      -- Get Lipschitz condition on [-δ, δ]
      -- From margin condition: |τ 0| + δ ≤ K and τ 0 ∈ (-K, K), so δ < K + K = 2K
      -- Actually simpler: δ ≤ K since margin gives |τ i| + δ ≤ K and |τ i| ≥ 0
      have hδK : δ ≤ K := by
        let i0 : Fin n := ⟨0, hn_pos⟩
        have hm := hmargin i0
        have hτ_nonneg : 0 ≤ |τ i0| := abs_nonneg _
        linarith

      have hL_lip_δ : ∀ y ∈ Set.Icc (-δ) δ, ∀ z ∈ Set.Icc (-δ) δ,
          |HeatKernel t0 y - HeatKernel t0 z| ≤ L * |y - z| := by
        intro y hy z hz
        have hy' : y ∈ Set.Icc (-(2*K)) (2*K) := by
          simp only [Set.mem_Icc] at hy ⊢
          constructor <;> linarith [hy.1, hy.2, hδK]
        have hz' : z ∈ Set.Icc (-(2*K)) (2*K) := by
          simp only [Set.mem_Icc] at hz ⊢
          constructor <;> linarith [hz.1, hz.2, hδK]
        exact hL_lip y hy' z hz'

      -- Apply total_atom_error_even
      rw [g_form, h_even_form]
      exact HeatError.total_atom_error_even t0 δ ht0 hδ_pos (fun i => Φ (τ i))
        (fun i => hΦ_nonneg (τ i)) τ x L hL_pos hL_lip_δ

    -- (E) Final calc
    calc |g x - h_even x|
        ≤ (L * δ / H0) * h_even x := h_core
      _ ≤ (L * δ / H0) * M'' := by
          apply mul_le_mul_of_nonneg_left h_even_le
          apply div_nonneg (mul_nonneg (le_of_lt hL_pos) (le_of_lt hδ_pos)) (le_of_lt hH0_pos)
      _ ≤ ε / 4 := hδ_small
      _ ≤ ε / 2 := by linarith

  -- Step 5: Tight bound |Φ x - g x| < ε
  have h_pointwise_tight : ∀ x ∈ Set.Icc (-K) K, |Φ x - g x| < 3 * ε / 4 := by
    intro x hx
    have h1 : |Φ x - h_even x| < ε / 4 := by
      have := h_even_approx x hx
      calc |Φ x - h_even x| = |h_even x - Φ x| := abs_sub_comm _ _
        _ < ε / 4 := this
    have h2 : |h_even x - g x| ≤ ε / 2 := by
      have := h_g_h_even x hx
      calc |h_even x - g x| = |g x - h_even x| := abs_sub_comm _ _
        _ ≤ ε / 2 := this
    calc |Φ x - g x|
        ≤ |Φ x - h_even x| + |h_even x - g x| := abs_sub_le _ _ _
      _ < ε / 4 + ε / 2 := by nlinarith
      _ = 3 * ε / 4 := by ring

  have h_approx : sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε := by
    have h0_mem : (0 : ℝ) ∈ Set.Icc (-K) K := by constructor <;> nlinarith [hK]
    have hs_nonempty : ({|Φ x - g x| | x ∈ Set.Icc (-K) K} : Set ℝ).Nonempty :=
      ⟨|Φ 0 - g 0|, ⟨0, h0_mem, rfl⟩⟩
    have h_sSup_le : sSup ({|Φ x - g x| | x ∈ Set.Icc (-K) K} : Set ℝ) ≤ 3 * ε / 4 := by
      apply csSup_le hs_nonempty
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact le_of_lt (h_pointwise_tight x hx)
    calc sSup ({|Φ x - g x| | x ∈ Set.Icc (-K) K} : Set ℝ)
        ≤ 3 * ε / 4 := h_sSup_le
      _ < ε := by linarith

  exact ⟨g, hg_mem, h_approx⟩

end A1prime

end
