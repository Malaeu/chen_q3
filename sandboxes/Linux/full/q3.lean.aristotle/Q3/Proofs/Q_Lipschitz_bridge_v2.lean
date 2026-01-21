/-
Q_Lipschitz Bridge v2 (CLEAN - uses Tier-1 axioms only)
========================================================

This file creates a CLEAN bridge for Q Lipschitz theorem.
Uses Q3.Basic.Defs + Q3.Clean.AxiomsTier1 (Tier-1 classical axioms).
NO import of Q3.Axioms (Tier-2)!

The theorem states: Q is Lipschitz on W_K with constant L_Q = 2K·M_a + W_sum
where M_a = sup|a_star| on [-K,K].
-/

import Q3.Basic.Defs
import Q3.Clean.AxiomsTier1  -- Tier-1 axioms only (a_star bounds)

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Nat Classical Pointwise
open MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

noncomputable section

namespace Q3.Proofs.QLipschitzBridgeV2

/-! ## Definitions -/

/-- Sup of a_star on [-K, K] -/
def M_a (K : ℝ) : ℝ := sSup (Q3.a_star '' Set.Icc (-K) K)

/-- Lipschitz constant for Q on W_K -/
def L_Q (K : ℝ) : ℝ := 2 * K * M_a K + Q3.W_sum K

/-! ## Lipschitz Theorem -/

/-- Sup norm of difference on [-K, K] -/
def sup_norm_diff (K : ℝ) (Φ Ψ : ℝ → ℝ) : ℝ :=
  sSup (Set.image (fun x => |Φ x - Ψ x|) (Set.Icc (-K) K))

/-! ## Helper lemmas using Tier-1 axioms

Q is Lipschitz on W_K. Mathematical argument:
1. |Q(Φ) - Q(Ψ)| = |arch_term(Φ-Ψ) - prime_term(Φ-Ψ)|
2. |arch_term(Φ-Ψ)| ≤ ∫ |a_star| |Φ-Ψ| ≤ M_a · ∫ |Φ-Ψ| ≤ M_a · 2K · ‖Φ-Ψ‖_∞
3. |prime_term(Φ-Ψ)| ≤ Σ w_Q(n) |Φ-Ψ|(ξ_n) ≤ W_sum · ‖Φ-Ψ‖_∞
4. So |Q(Φ) - Q(Ψ)| ≤ (2K·M_a + W_sum) · ‖Φ-Ψ‖_∞ = L_Q · ‖Φ-Ψ‖_∞

Requires Tier-1 axioms:
- a_star_bdd_on_compact: M_a is well-defined
- a_star_pos: a_star > 0
-/

/-- a_star is bounded above on [-K, K] (from Tier-1) -/
lemma a_star_bdd_above (K : ℝ) (hK : K > 0) : BddAbove (Q3.a_star '' Set.Icc (-K) K) := by
  obtain ⟨M, _, hM⟩ := Q3.Clean.a_star_bdd_on_compact K hK
  use M
  intro y hy
  obtain ⟨ξ, hξ, rfl⟩ := hy
  exact hM ξ hξ

/-- a_star image is nonempty -/
lemma a_star_image_nonempty (K : ℝ) (hK : K > 0) :
    (Q3.a_star '' Set.Icc (-K) K).Nonempty := by
  use Q3.a_star 0, 0
  constructor
  · constructor <;> linarith
  · rfl

/-- M_a K is positive -/
lemma M_a_pos (K : ℝ) (hK : K > 0) : M_a K > 0 := by
  have h_bdd := a_star_bdd_above K hK
  have h_pos : Q3.a_star 0 > 0 := Q3.Clean.a_star_pos 0
  have h_mem : Q3.a_star 0 ∈ Q3.a_star '' Set.Icc (-K) K := by
    use 0
    constructor
    · constructor <;> linarith
    · rfl
  exact lt_of_lt_of_le h_pos (le_csSup h_bdd h_mem)

/-- a_star ξ ≤ M_a K for ξ ∈ [-K, K] -/
lemma a_star_le_M_a (K : ℝ) (hK : K > 0) (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-K) K) :
    Q3.a_star ξ ≤ M_a K := by
  apply le_csSup (a_star_bdd_above K hK)
  exact ⟨ξ, hξ, rfl⟩

/-! ## L_Q positivity -/

/-- L_Q K is positive for K > 0 -/
lemma L_Q_pos (K : ℝ) (hK : K > 0) : L_Q K > 0 := by
  unfold L_Q
  have hM := M_a_pos K hK
  have hW : Q3.W_sum K ≥ 0 := by
    -- W_sum = Σ w_Q(n) where w_Q(n) ≥ 0
    unfold Q3.W_sum
    apply tsum_nonneg
    intro n
    split_ifs
    · exact Q3.w_Q_nonneg n
    · rfl
  have h1 : 2 * K * M_a K > 0 := by positivity
  linarith

/-! ## Sup norm and arch term bounds -/

lemma sup_norm_diff_bddAbove (K : ℝ) (Φ Ψ : ℝ → ℝ)
    (hcontΦ : ContinuousOn Φ (Set.Icc (-K) K))
    (hcontΨ : ContinuousOn Ψ (Set.Icc (-K) K)) :
    BddAbove (Set.image (fun x => |Φ x - Ψ x|) (Set.Icc (-K) K)) := by
  have hcomp : IsCompact (Set.Icc (-K) K) := isCompact_Icc
  have hcont : ContinuousOn (fun x => |Φ x - Ψ x|) (Set.Icc (-K) K) :=
    ContinuousOn.abs (hcontΦ.sub hcontΨ)
  exact (hcomp.image_of_continuousOn hcont).bddAbove

lemma sup_norm_diff_nonneg (K : ℝ) (Φ Ψ : ℝ → ℝ) : 0 ≤ sup_norm_diff K Φ Ψ := by
  apply Real.sSup_nonneg
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact abs_nonneg _

/-- Local arch_term as set integral on [-K, K]. -/
def arch_term_local (K : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  ∫ ξ in Set.Icc (-K) K, Q3.a_star ξ * Φ ξ

lemma arch_term_eq_local (K : ℝ) (Φ : ℝ → ℝ)
    (hsupp : Function.support Φ ⊆ Set.Icc (-K) K) :
    Q3.arch_term Φ = arch_term_local K Φ := by
  unfold Q3.arch_term arch_term_local
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro ξ hξ
  simp only [Set.mem_Icc, not_and, not_le] at hξ
  by_cases h_neg : ξ < -K
  · have h : Φ ξ = 0 := by
      by_contra hne
      have := hsupp hne
      simp only [Set.mem_Icc] at this
      linarith
    simp [h]
  · push_neg at h_neg
    have h_big : ξ > K := hξ h_neg
    have h : Φ ξ = 0 := by
      by_contra hne
      have := hsupp hne
      simp only [Set.mem_Icc] at this
      linarith
    simp [h]

lemma volume_real_Icc (K : ℝ) (hK : K > 0) :
    volume.real (Set.Icc (-K) K) = 2 * K := by
  rw [Measure.real_def, Real.volume_Icc]
  simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ K - (-K))]
  ring_nf

lemma arch_term_Lipschitz_local (K : ℝ) (hK : K > 0) (Φ Ψ : ℝ → ℝ)
    (hcontΦ : ContinuousOn Φ (Set.Icc (-K) K))
    (hcontΨ : ContinuousOn Ψ (Set.Icc (-K) K)) :
    |arch_term_local K Φ - arch_term_local K Ψ| ≤
      2 * K * M_a K * sup_norm_diff K Φ Ψ := by
  set D := sup_norm_diff K Φ Ψ with hD_def
  have hD_bdd : BddAbove (Set.image (fun x => |Φ x - Ψ x|) (Set.Icc (-K) K)) :=
    sup_norm_diff_bddAbove K Φ Ψ hcontΦ hcontΨ
  have h_diff : arch_term_local K Φ - arch_term_local K Ψ =
      ∫ ξ in Set.Icc (-K) K, Q3.a_star ξ * (Φ ξ - Ψ ξ) := by
    unfold arch_term_local
    rw [← MeasureTheory.integral_sub]
    · congr 1; ext ξ; ring_nf
    · apply ContinuousOn.integrableOn_Icc
      exact (Q3.Clean.a_star_continuous.continuousOn.mul hcontΦ)
    · apply ContinuousOn.integrableOn_Icc
      exact (Q3.Clean.a_star_continuous.continuousOn.mul hcontΨ)
  calc |arch_term_local K Φ - arch_term_local K Ψ|
      = |∫ ξ in Set.Icc (-K) K, Q3.a_star ξ * (Φ ξ - Ψ ξ)| := by
          rw [h_diff]
    _ ≤ ∫ ξ in Set.Icc (-K) K, |Q3.a_star ξ * (Φ ξ - Ψ ξ)| := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ = ∫ ξ in Set.Icc (-K) K, Q3.a_star ξ * |Φ ξ - Ψ ξ| := by
          congr 1; ext ξ
          rw [abs_mul, abs_of_pos (Q3.Clean.a_star_pos ξ)]
    _ ≤ ∫ ξ in Set.Icc (-K) K, M_a K * D := by
          apply MeasureTheory.setIntegral_mono_on
          · apply ContinuousOn.integrableOn_Icc
            exact (Q3.Clean.a_star_continuous.continuousOn.mul (ContinuousOn.abs (hcontΦ.sub hcontΨ)))
          · exact integrableOn_const (hs := measure_Icc_lt_top.ne) (hC := ENNReal.coe_ne_top)
          · exact measurableSet_Icc
          · intro ξ hξ
            apply mul_le_mul
            · exact a_star_le_M_a K hK ξ hξ
            · apply le_csSup hD_bdd
              exact ⟨ξ, hξ, rfl⟩
            · exact abs_nonneg _
            · exact le_of_lt (M_a_pos K hK)
    _ = M_a K * D * volume.real (Set.Icc (-K) K) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
    _ = M_a K * D * (2 * K) := by
          rw [volume_real_Icc K hK]
    _ = 2 * K * M_a K * D := by ring_nf

/-! ## Prime term bounds -/

def N_K (K : ℝ) : ℕ := Nat.floor (Real.exp (2 * Real.pi * K))

lemma Nodes_subset_Icc (K : ℝ) : Q3.Nodes K ⊆ Set.Icc 2 (N_K K + 1) := by
  intro n hn
  unfold Q3.Nodes Q3.xi_n at hn
  constructor
  · exact hn.2
  · have h_le_NK : n ≤ Nat.floor (Real.exp (2 * Real.pi * K)) := by
      have h_log : Real.log n ≤ 2 * Real.pi * K := by
        have := hn.1
        rw [abs_le] at this
        have h := this.2
        have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
        rw [div_le_iff₀ hpi] at h
        linarith
      have hn_pos : (0 : ℝ) < n := by
        have := hn.2
        exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) this)
      exact Nat.le_floor <| by
        rw [← Real.log_le_iff_le_exp hn_pos]
        exact h_log
    exact Nat.le_succ_of_le h_le_NK

lemma Nodes_finite (K : ℝ) : (Q3.Nodes K).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 2 (N_K K + 1))
  exact Nodes_subset_Icc K

lemma Phi_zero_outside_support (K : ℝ) (Φ : ℝ → ℝ)
    (hsupp : Function.support Φ ⊆ Set.Icc (-K) K) (n : ℕ) (hn : |Q3.xi_n n| > K) :
    Φ (Q3.xi_n n) = 0 := by
  by_contra h
  have hmem : Q3.xi_n n ∈ Function.support Φ := h
  have hIcc : Q3.xi_n n ∈ Set.Icc (-K) K := hsupp hmem
  rw [Set.mem_Icc] at hIcc
  have habs : |Q3.xi_n n| ≤ K := abs_le.mpr hIcc
  linarith

lemma w_Q_zero_of_lt_two (n : ℕ) (hn : n < 2) : Q3.w_Q n = 0 := by
  simp only [Q3.w_Q]
  interval_cases n
  · simp only [ArithmeticFunction.map_zero, zero_div, mul_zero]
  · simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, mul_zero]

lemma summable_w_Q_Phi (K : ℝ) (Φ : ℝ → ℝ)
    (hsupp : Function.support Φ ⊆ Set.Icc (-K) K) :
    Summable (fun n => Q3.w_Q n * Φ (Q3.xi_n n)) := by
  have h_finite : Set.Finite {n : ℕ | Q3.w_Q n * Φ (Q3.xi_n n) ≠ 0} := by
    apply Set.Finite.subset (Nodes_finite K)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    constructor
    · -- |xi_n n| ≤ K
      by_contra h_abs
      push_neg at h_abs
      have hzero := Phi_zero_outside_support K Φ hsupp n h_abs
      simp [hzero] at hn
    · -- n ≥ 2 (otherwise w_Q n = 0)
      by_contra h_small
      have h_small' : n < 2 := lt_of_not_ge h_small
      have h_wq : Q3.w_Q n = 0 := w_Q_zero_of_lt_two n h_small'
      simp [h_wq] at hn
  exact summable_of_ne_finset_zero (s := h_finite.toFinset)
    (fun n hn => by
      simp only [Set.Finite.mem_toFinset] at hn
      exact Classical.not_not.mp hn)

lemma prime_term_Lipschitz (K : ℝ) (hK : K > 0) (Φ Ψ : ℝ → ℝ)
    (hcontΦ : ContinuousOn Φ (Set.Icc (-K) K))
    (hcontΨ : ContinuousOn Ψ (Set.Icc (-K) K))
    (hsuppΦ : Function.support Φ ⊆ Set.Icc (-K) K)
    (hsuppΨ : Function.support Ψ ⊆ Set.Icc (-K) K) :
    |Q3.prime_term Φ - Q3.prime_term Ψ| ≤ Q3.W_sum K * sup_norm_diff K Φ Ψ := by
  set D := sup_norm_diff K Φ Ψ with hD_def
  have hD_bdd : BddAbove (Set.image (fun x => |Φ x - Ψ x|) (Set.Icc (-K) K)) :=
    sup_norm_diff_bddAbove K Φ Ψ hcontΦ hcontΨ
  have hsumΦ := summable_w_Q_Phi K Φ hsuppΦ
  have hsumΨ := summable_w_Q_Phi K Ψ hsuppΨ
  have h_diff : Q3.prime_term Φ - Q3.prime_term Ψ =
      ∑' n, Q3.w_Q n * (Φ (Q3.xi_n n) - Ψ (Q3.xi_n n)) := by
    unfold Q3.prime_term
    rw [← Summable.tsum_sub hsumΦ hsumΨ]
    congr 1
    ext n
    ring_nf
  rw [h_diff]
  have h_summable_diff :
      Summable (fun n => Q3.w_Q n * (Φ (Q3.xi_n n) - Ψ (Q3.xi_n n))) := by
    have h_eq :
        (fun n => Q3.w_Q n * (Φ (Q3.xi_n n) - Ψ (Q3.xi_n n))) =
          (fun n => Q3.w_Q n * Φ (Q3.xi_n n) - Q3.w_Q n * Ψ (Q3.xi_n n)) := by
      ext n; ring_nf
    rw [h_eq]
    exact Summable.sub hsumΦ hsumΨ
  have h_summable_abs :
      Summable (fun n => |Q3.w_Q n * (Φ (Q3.xi_n n) - Ψ (Q3.xi_n n))|) :=
    h_summable_diff.abs
  calc |∑' n, Q3.w_Q n * (Φ (Q3.xi_n n) - Ψ (Q3.xi_n n))|
      ≤ ∑' n, |Q3.w_Q n * (Φ (Q3.xi_n n) - Ψ (Q3.xi_n n))| := by
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm h_summable_abs
    _ = ∑' n, |Q3.w_Q n| * |Φ (Q3.xi_n n) - Ψ (Q3.xi_n n)| := by
          congr 1; ext n; exact abs_mul _ _
    _ = ∑' n, Q3.w_Q n * |Φ (Q3.xi_n n) - Ψ (Q3.xi_n n)| := by
          congr 1; ext n; rw [abs_of_nonneg (Q3.w_Q_nonneg n)]
    _ ≤ Q3.W_sum K * D := by
          have h_term_bound : ∀ n, Q3.w_Q n * |Φ (Q3.xi_n n) - Ψ (Q3.xi_n n)| ≤
              (if n ∈ Q3.Nodes K then Q3.w_Q n else 0) * D := by
            intro n
            by_cases h_active : n ∈ Q3.Nodes K
            · simp only [h_active, ite_true]
              apply mul_le_mul_of_nonneg_left _ (Q3.w_Q_nonneg n)
              apply le_csSup hD_bdd
              have hxi : Q3.xi_n n ∈ Set.Icc (-K) K := by
                have h := (abs_le.mp h_active.1)
                exact h
              exact ⟨Q3.xi_n n, hxi, rfl⟩
            · simp only [h_active, ite_false, zero_mul]
              have h_cases : |Q3.xi_n n| > K ∨ n < 2 := by
                have h' : ¬(|Q3.xi_n n| ≤ K ∧ n ≥ 2) := by
                  simpa [Q3.Nodes] using h_active
                have h'' := not_and_or.mp h'
                rcases h'' with h_abs | h_n
                · exact Or.inl (lt_of_not_ge h_abs)
                · exact Or.inr (lt_of_not_ge h_n)
              rcases h_cases with h_abs | h_small
              · have h1 := Phi_zero_outside_support K Φ hsuppΦ n h_abs
                have h2 := Phi_zero_outside_support K Ψ hsuppΨ n h_abs
                simp [h1, h2]
              · have h_wq : Q3.w_Q n = 0 := w_Q_zero_of_lt_two n h_small
                simp [h_wq]
          have h_summable_bound :
              Summable (fun n => (if n ∈ Q3.Nodes K then Q3.w_Q n else 0) * D) := by
            apply Summable.mul_right
            have h_fin : (Q3.Nodes K).Finite := Nodes_finite K
            refine summable_of_ne_finset_zero (s := h_fin.toFinset) ?_
            intro n hn
            simp only [Set.Finite.mem_toFinset] at hn
            simp [hn]
          have h_summable_lhs :
              Summable (fun n => Q3.w_Q n * |Φ (Q3.xi_n n) - Ψ (Q3.xi_n n)|) := by
            apply Summable.of_nonneg_of_le
            · intro n; exact mul_nonneg (Q3.w_Q_nonneg n) (abs_nonneg _)
            · exact h_term_bound
            · exact h_summable_bound
          calc ∑' n, Q3.w_Q n * |Φ (Q3.xi_n n) - Ψ (Q3.xi_n n)|
              ≤ ∑' n, (if n ∈ Q3.Nodes K then Q3.w_Q n else 0) * D :=
                Summable.tsum_le_tsum h_term_bound h_summable_lhs h_summable_bound
            _ = (∑' n, if n ∈ Q3.Nodes K then Q3.w_Q n else 0) * D := tsum_mul_right
            _ = Q3.W_sum K * D := by unfold Q3.W_sum; rfl

/-! ## Main theorems -/

theorem Q_Lipschitz_on_W_K (K : ℝ) (hK : K > 0) :
    ∀ Φ Ψ : ℝ → ℝ, Φ ∈ Q3.W_K K → Ψ ∈ Q3.W_K K →
      |Q3.Q Φ - Q3.Q Ψ| ≤ L_Q K * sup_norm_diff K Φ Ψ := by
  intro Φ Ψ hΦ hΨ
  -- Q(Φ) - Q(Ψ) = (arch_term Φ - arch_term Ψ) - (prime_term Φ - prime_term Ψ)
  -- |Q(Φ) - Q(Ψ)| ≤ |arch_term(Φ-Ψ)| + |prime_term(Φ-Ψ)|
  -- |arch_term(Φ-Ψ)| = |∫ a_star · (Φ-Ψ)| ≤ M_a · ∫_{-K}^K |Φ-Ψ| ≤ M_a · 2K · ‖Φ-Ψ‖_∞
  -- |prime_term(Φ-Ψ)| = |Σ w_Q(n)(Φ-Ψ)(ξ_n)| ≤ W_sum · ‖Φ-Ψ‖_∞
  -- Total: ≤ (2K·M_a + W_sum) · ‖Φ-Ψ‖_∞ = L_Q · ‖Φ-Ψ‖_∞
  obtain ⟨hcontΦ, hsuppΦ, _, _⟩ := hΦ
  obtain ⟨hcontΨ, hsuppΨ, _, _⟩ := hΨ
  have hcontΦ' : ContinuousOn Φ (Set.Icc (-K) K) := hcontΦ.continuousOn
  have hcontΨ' : ContinuousOn Ψ (Set.Icc (-K) K) := hcontΨ.continuousOn
  have hsuppΦ' : Function.support Φ ⊆ Set.Icc (-K) K :=
    Set.Subset.trans hsuppΦ Set.Ioo_subset_Icc_self
  have hsuppΨ' : Function.support Ψ ⊆ Set.Icc (-K) K :=
    Set.Subset.trans hsuppΨ Set.Ioo_subset_Icc_self
  have h_arch : |Q3.arch_term Φ - Q3.arch_term Ψ| ≤
      2 * K * M_a K * sup_norm_diff K Φ Ψ := by
    have h_eqΦ := arch_term_eq_local K Φ hsuppΦ'
    have h_eqΨ := arch_term_eq_local K Ψ hsuppΨ'
    have h_local := arch_term_Lipschitz_local K hK Φ Ψ hcontΦ' hcontΨ'
    simpa [h_eqΦ, h_eqΨ] using h_local
  have h_prime : |Q3.prime_term Φ - Q3.prime_term Ψ| ≤
      Q3.W_sum K * sup_norm_diff K Φ Ψ := by
    exact prime_term_Lipschitz K hK Φ Ψ hcontΦ' hcontΨ' hsuppΦ' hsuppΨ'
  calc |Q3.Q Φ - Q3.Q Ψ|
      = |(Q3.arch_term Φ - Q3.prime_term Φ) - (Q3.arch_term Ψ - Q3.prime_term Ψ)| := rfl
    _ = |(Q3.arch_term Φ - Q3.arch_term Ψ) - (Q3.prime_term Φ - Q3.prime_term Ψ)| := by ring_nf
    _ ≤ |Q3.arch_term Φ - Q3.arch_term Ψ| + |Q3.prime_term Φ - Q3.prime_term Ψ| :=
        abs_sub _ _
    _ ≤ 2 * K * M_a K * sup_norm_diff K Φ Ψ + Q3.W_sum K * sup_norm_diff K Φ Ψ :=
        add_le_add h_arch h_prime
    _ = (2 * K * M_a K + Q3.W_sum K) * sup_norm_diff K Φ Ψ := by ring_nf
    _ = L_Q K * sup_norm_diff K Φ Ψ := by rfl

/-- Corollary: Q is uniformly continuous on W_K -/
theorem Q_uniformly_continuous_on_W_K (K : ℝ) (hK : K > 0) (ε : ℝ) (hε : ε > 0) :
    ∃ δ > 0, ∀ Φ Ψ : ℝ → ℝ, Φ ∈ Q3.W_K K → Ψ ∈ Q3.W_K K →
      sup_norm_diff K Φ Ψ < δ → |Q3.Q Φ - Q3.Q Ψ| < ε := by
  -- From Lipschitz: take δ = ε / (L_Q K + 1)
  have hL := L_Q_pos K hK
  have hL_pos : L_Q K + 1 > 0 := by linarith
  use ε / (L_Q K + 1)
  constructor
  · exact div_pos hε hL_pos
  · intro Φ Ψ hΦ hΨ hdiff
    have h_lip := Q_Lipschitz_on_W_K K hK Φ Ψ hΦ hΨ
    calc |Q3.Q Φ - Q3.Q Ψ|
        ≤ L_Q K * sup_norm_diff K Φ Ψ := h_lip
      _ < L_Q K * (ε / (L_Q K + 1)) := by gcongr
      _ < (L_Q K + 1) * (ε / (L_Q K + 1)) := by gcongr; linarith
      _ = ε := by field_simp

end Q3.Proofs.QLipschitzBridgeV2

/-!
# Summary

CLEAN bridge for Q_Lipschitz:
- Imports only Q3.Basic.Defs (no Q3.Axioms!)
- Defines L_Q (Lipschitz constant)
- Proves Lipschitz theorem in the clean chain

Requires Tier-1 axioms (a_star bounds).
The clean chain will provide these via AxiomsTier1.lean.

# Verification
```
lake build Q3.Proofs.Q_Lipschitz_bridge_v2
#print axioms Q3.Proofs.QLipschitzBridgeV2.Q_Lipschitz_on_W_K
```
Expected: [propext, Classical.choice, Quot.sound]
-/
