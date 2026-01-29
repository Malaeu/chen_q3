/-
Q_nonneg supporting lemmas (A1, A2 from Q_nonneg decomposition)

A1: Linearity of Q over finite sums
A2: Nonnegativity of prime sum

Integration: change-durch: claude-code 2026-01-17 Q_nonneg_lemmas
-/

import Q3.Axioms
-- Note: P_A_Toeplitz_bridge and Rayleigh_Q_identification are heavy imports
-- We use forward declarations for the lemmas we need

set_option linter.mathlibStandardSet false

open scoped BigOperators

noncomputable section

namespace Q3.Proofs.Q_nonneg_lemmas

/-! ## A2: Nonnegativity of prime sum -/

/-- The finite prime sum over nodes is nonnegative for fejer_heat_window.
    Uses: Finset.sum_nonneg, mul_nonneg, w_Q_nonneg, fejer_heat_window_nonneg. -/
lemma prime_sum_nonneg (K B t : ℝ) [Fintype (Q3.Nodes K)]
    (_hB : B > 0) (_ht : t > 0) :
    0 ≤ ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg
  · exact Q3.w_Q_nonneg n
  · exact Q3.fejer_heat_window_nonneg B t (Q3.xi_n n)

/-! ## A1: Linearity of Q over finite sums -/

/-- arch_term is linear over finite sums.
    Requires integrability of each a_star * atom. -/
lemma arch_term_sum {n : ℕ} (atoms : Fin n → ℝ → ℝ) (coeffs : Fin n → ℝ)
    (h : ∀ i, MeasureTheory.Integrable (fun x => Q3.a_star x * atoms i x)) :
    Q3.arch_term (fun x => ∑ i, coeffs i * atoms i x) =
      ∑ i, coeffs i * Q3.arch_term (atoms i) := by
  classical
  simp only [Q3.arch_term]
  -- a_star * (sum) = sum (a_star * ...)
  have hsum : (fun x => Q3.a_star x * ∑ i, coeffs i * atoms i x) =
      (fun x => ∑ i, coeffs i * (Q3.a_star x * atoms i x)) := by
    ext x
    rw [Finset.mul_sum]
    congr 1
    ext i
    ring
  rw [hsum, MeasureTheory.integral_finset_sum]
  · congr 1
    ext i
    rw [MeasureTheory.integral_mul_left]
  · intro i _
    exact (h i).const_mul (coeffs i)

/-- prime_term is linear over finite sums.
    Requires summability of each w_Q * atom evaluated at xi_n. -/
lemma prime_term_sum {n : ℕ} (atoms : Fin n → ℝ → ℝ) (coeffs : Fin n → ℝ)
    (h : ∀ i, Summable (fun k => Q3.w_Q k * atoms i (Q3.xi_n k))) :
    Q3.prime_term (fun x => ∑ i, coeffs i * atoms i x) =
      ∑ i, coeffs i * Q3.prime_term (atoms i) := by
  classical
  simp only [Q3.prime_term]
  -- Rewrite inside tsum: w(k) * (Σᵢ cᵢ * fᵢ(ξₖ)) = Σᵢ cᵢ * (w(k) * fᵢ(ξₖ))
  have hsum : (fun k => Q3.w_Q k * ∑ i, coeffs i * atoms i (Q3.xi_n k)) =
      (fun k => ∑ i, coeffs i * (Q3.w_Q k * atoms i (Q3.xi_n k))) := by
    ext k
    rw [Finset.mul_sum]
    congr 1
    ext i
    ring
  rw [hsum]
  -- Interchange tsum and Finset.sum using Summable.tsum_finsetSum
  have h_sum_summable : ∀ i ∈ Finset.univ, Summable (fun k => coeffs i * (Q3.w_Q k * atoms i (Q3.xi_n k))) := by
    intro i _
    exact (h i).mul_left (coeffs i)
  rw [Summable.tsum_finsetSum h_sum_summable]
  congr 1
  ext i
  rw [tsum_mul_left]

/-- Q is linear over finite sums: Q(Σ cᵢ · Φᵢ) = Σ cᵢ · Q(Φᵢ).
    Requires integrability and summability hypotheses. -/
lemma Q_finset_sum {n : ℕ} (atoms : Fin n → ℝ → ℝ) (coeffs : Fin n → ℝ)
    (h_int : ∀ i, MeasureTheory.Integrable (fun x => Q3.a_star x * atoms i x))
    (h_sum : ∀ i, Summable (fun k => Q3.w_Q k * atoms i (Q3.xi_n k))) :
    Q3.Q (fun x => ∑ i, coeffs i * atoms i x) =
      ∑ i, coeffs i * Q3.Q (atoms i) := by
  simp only [Q3.Q]
  rw [arch_term_sum atoms coeffs h_int, prime_term_sum atoms coeffs h_sum]
  -- ∑ᵢ cᵢ·arch(Φᵢ) - ∑ᵢ cᵢ·prime(Φᵢ) = ∑ᵢ cᵢ·(arch(Φᵢ) - prime(Φᵢ))
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext i
  ring

/-! ## A4: Rayleigh lower bound on basis0 from A3 bridge -/

-- A4 lemma (rayleigh_basis0_of_A3):
-- From A3 bridge data, extract Rayleigh lower bound on basis0 (constant vector).
-- This is just an instantiation of the ∀ v bound with v = basis0.
-- NOTE: This lemma requires imports from Rayleigh_Q_identification which is
-- computationally expensive (645+ min CPU). The full proof is in that module.
-- The proof is trivial: hA3 gives ∀ v ≠ 0, bound, and basis0 ≠ 0.
-- Full version is in Q3.Proofs.RayleighQId namespace once that module compiles.

/-! ## Integrability and Summability for Fejer_heat_atom -/

/-- Fejer_kernel vanishes when |x| ≥ B -/
lemma Fejer_kernel_eq_zero_of_abs_ge (B x : ℝ) (hB : B > 0) (hx : B ≤ |x|) :
    Q3.Fejer_kernel B x = 0 := by
  simp only [Q3.Fejer_kernel]
  rw [max_eq_left_iff]
  have h : 1 - |x| / B ≤ 0 := by
    have hB' : 0 < B := hB
    have h1 : |x| / B ≥ 1 := by
      rw [ge_iff_le, one_le_div hB']
      exact hx
    linarith
  exact h

/-- Fejer_heat_atom vanishes when ξ is far from both ±τ -/
lemma Fejer_heat_atom_eq_zero_of_far (B t τ ξ : ℝ) (hB : B > 0)
    (h1 : B ≤ |ξ - τ|) (h2 : B ≤ |ξ + τ|) :
    Q3.Fejer_heat_atom B t τ ξ = 0 := by
  simp only [Q3.Fejer_heat_atom]
  rw [Fejer_kernel_eq_zero_of_abs_ge B (ξ - τ) hB h1,
      Fejer_kernel_eq_zero_of_abs_ge B (ξ + τ) hB h2]
  ring

/-- Support of Fejer_heat_atom is contained in [-|τ|-B, |τ|+B] -/
lemma Fejer_heat_atom_support_subset (B t τ : ℝ) (hB : B > 0) :
    Function.support (Q3.Fejer_heat_atom B t τ) ⊆ Set.Icc (-(|τ| + B)) (|τ| + B) := by
  intro ξ hξ
  simp only [Function.mem_support] at hξ
  -- If ξ ∉ Icc(-|τ|-B, |τ|+B), then both |ξ-τ| ≥ B and |ξ+τ| ≥ B
  by_contra h_not
  simp only [Set.mem_Icc, not_and_or, not_le] at h_not
  -- Show Fejer_heat_atom = 0, contradiction
  have h1 : B ≤ |ξ - τ| := by
    cases h_not with
    | inl h => -- ξ < -(|τ| + B)
      have : ξ - τ < -B := by
        have hτ : -|τ| ≤ τ := neg_abs_le τ
        linarith
      rw [abs_of_neg (by linarith : ξ - τ < 0)]
      linarith
    | inr h => -- |τ| + B < ξ
      have : B < ξ - τ := by
        have hτ : τ ≤ |τ| := le_abs_self τ
        linarith
      rw [abs_of_pos (by linarith : 0 < ξ - τ)]
      linarith
  have h2 : B ≤ |ξ + τ| := by
    cases h_not with
    | inl h => -- ξ < -(|τ| + B)
      have : ξ + τ < -B := by
        have hτ : τ ≤ |τ| := le_abs_self τ
        linarith
      rw [abs_of_neg (by linarith : ξ + τ < 0)]
      linarith
    | inr h => -- |τ| + B < ξ
      have : B < ξ + τ := by
        have hτ : -|τ| ≤ τ := neg_abs_le τ
        linarith
      rw [abs_of_pos (by linarith : 0 < ξ + τ)]
      linarith
  have h_zero := Fejer_heat_atom_eq_zero_of_far B t τ ξ hB h1 h2
  exact hξ h_zero

/-- Fejer_kernel is continuous -/
lemma Fejer_kernel_continuous (B : ℝ) : Continuous (Q3.Fejer_kernel B) := by
  unfold Q3.Fejer_kernel
  exact continuous_const.max (continuous_const.sub (continuous_abs.div_const _))

/-- heat_kernel_A1 is continuous -/
lemma heat_kernel_A1_continuous (t : ℝ) : Continuous (Q3.heat_kernel_A1 t) := by
  unfold Q3.heat_kernel_A1
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_id.pow 2 |>.neg.div_const _))

/-- Fejer_heat_atom is continuous -/
lemma Fejer_heat_atom_continuous (B t τ : ℝ) : Continuous (Q3.Fejer_heat_atom B t τ) := by
  unfold Q3.Fejer_heat_atom
  refine Continuous.add ?_ ?_ <;> refine Continuous.mul ?_ ?_
  · exact (Fejer_kernel_continuous B).comp (continuous_id.sub continuous_const)
  · exact (heat_kernel_A1_continuous t).comp (continuous_id.sub continuous_const)
  · exact (Fejer_kernel_continuous B).comp (continuous_id.add continuous_const)
  · exact (heat_kernel_A1_continuous t).comp (continuous_id.add continuous_const)

/-- a_star * Fejer_heat_atom is integrable.
    Uses: compact support + continuity → Integrable. -/
lemma fejer_heat_atom_integrable_with_a_star (B t τ : ℝ) (hB : B > 0) (_ht : t > 0) :
    MeasureTheory.Integrable (fun x => Q3.a_star x * Q3.Fejer_heat_atom B t τ x) := by
  -- 1. Fejer_heat_atom has compact support (support ⊆ Icc which is compact)
  have h_atom_hcs : HasCompactSupport (Q3.Fejer_heat_atom B t τ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (Fejer_heat_atom_support_subset B t τ hB)
  -- 2. The product is continuous
  have h_prod_cont : Continuous (fun x => Q3.a_star x * Q3.Fejer_heat_atom B t τ x) :=
    Q3.a_star_continuous.mul (Fejer_heat_atom_continuous B t τ)
  -- 3. The product has compact support (via mul_left)
  have h_prod_hcs : HasCompactSupport (fun x => Q3.a_star x * Q3.Fejer_heat_atom B t τ x) :=
    h_atom_hcs.mul_left
  -- 4. Continuous + HasCompactSupport → Integrable
  exact h_prod_cont.integrable_of_hasCompactSupport h_prod_hcs

/-- xi_n k is large for large k -/
lemma xi_n_large_of_k_large (k : ℕ) (C : ℝ) (hk : k > Nat.ceil (Real.exp (2 * Real.pi * C))) :
    Q3.xi_n k > C := by
  simp only [Q3.xi_n]
  have hexp_pos : 0 < Real.exp (2 * Real.pi * C) := Real.exp_pos _
  have hceil_le : Nat.ceil (Real.exp (2 * Real.pi * C)) ≥ 1 := Nat.one_le_ceil_iff.mpr hexp_pos
  have hk_pos : (0 : ℝ) < k := by
    have : k ≥ Nat.ceil (Real.exp (2 * Real.pi * C)) + 1 := hk
    have : k ≥ 2 := by omega
    positivity
  have h1 : (k : ℝ) > Real.exp (2 * Real.pi * C) := by
    calc (k : ℝ) > Nat.ceil (Real.exp (2 * Real.pi * C)) := Nat.cast_lt.mpr hk
      _ ≥ Real.exp (2 * Real.pi * C) := Nat.le_ceil _
  have h2 : Real.log k > 2 * Real.pi * C := by
    rw [← Real.log_exp (2 * Real.pi * C)]
    exact Real.log_lt_log (Real.exp_pos _) h1
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [gt_iff_lt, ← sub_pos]
  have heq : Real.log k / (2 * Real.pi) - C = (Real.log k - 2 * Real.pi * C) / (2 * Real.pi) := by
    field_simp
  rw [heq]
  exact div_pos (sub_pos.mpr h2) hpi

/-- The prime sum for Fejer_heat_atom is summable (actually finite).
    Uses: Fejer_heat_atom vanishes for large xi_n k. -/
lemma fejer_heat_atom_prime_summable (B t τ : ℝ) (hB : B > 0) (_ht : t > 0) :
    Summable (fun k => Q3.w_Q k * Q3.Fejer_heat_atom B t τ (Q3.xi_n k)) := by
  -- Let N = ⌈exp(2π(|τ|+B))⌉ + 1
  let N := Nat.ceil (Real.exp (2 * Real.pi * (|τ| + B))) + 1
  -- Use summable_of_ne_finset_zero
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  -- Need to show: w_Q k * Fejer_heat_atom B t τ (xi_n k) = 0
  -- Suffices to show: Fejer_heat_atom B t τ (xi_n k) = 0
  suffices h : Q3.Fejer_heat_atom B t τ (Q3.xi_n k) = 0 by simp [h]
  -- xi_n k > |τ| + B for k ≥ N
  have h_xi_large : Q3.xi_n k > |τ| + B := by
    apply xi_n_large_of_k_large
    omega
  -- Therefore xi_n k ∉ support of Fejer_heat_atom
  have h_supp := Fejer_heat_atom_support_subset B t τ hB
  -- xi_n k ∉ Icc (-(|τ|+B)) (|τ|+B)
  have h_not_in_Icc : Q3.xi_n k ∉ Set.Icc (-(|τ| + B)) (|τ| + B) := by
    simp only [Set.mem_Icc, not_and_or, not_le]
    right; exact h_xi_large
  -- So Fejer_heat_atom = 0
  by_contra h_ne
  exact h_not_in_Icc (h_supp (Function.mem_support.mpr h_ne))

/-! ## A5: Extension from atoms to AtomCone_K -/

/-- If Q ≥ 0 on each Fejer_heat_atom, then Q ≥ 0 on AtomCone_K.
    Uses linearity of Q and Finset.sum_nonneg. -/
lemma Q_nonneg_on_atomcone_of_atoms (K : ℝ) (_hK : K ≥ 1)
    (h_atom : ∀ B t τ, B > 0 → t > 0 → |τ| + B ≤ K →
              Q3.Q (Q3.Fejer_heat_atom B t τ) ≥ 0) :
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 := by
  intro g hg
  -- Destructure g ∈ AtomCone_K K
  obtain ⟨n, c, B, t, τ, hc_nonneg, hB_pos, ht_pos, h_support, hg_eq, _hg_WK⟩ := hg
  -- Rewrite Q(g) using the representation
  have hg_fn : g = fun x => ∑ i, c i * Q3.Fejer_heat_atom (B i) (t i) (τ i) x := by
    ext x; exact hg_eq x
  rw [hg_fn]
  -- Prove integrability and summability for each atom
  have h_int : ∀ i, MeasureTheory.Integrable
      (fun x => Q3.a_star x * Q3.Fejer_heat_atom (B i) (t i) (τ i) x) := by
    intro i
    exact fejer_heat_atom_integrable_with_a_star (B i) (t i) (τ i) (hB_pos i) (ht_pos i)
  have h_sum : ∀ i, Summable
      (fun k => Q3.w_Q k * Q3.Fejer_heat_atom (B i) (t i) (τ i) (Q3.xi_n k)) := by
    intro i
    exact fejer_heat_atom_prime_summable (B i) (t i) (τ i) (hB_pos i) (ht_pos i)
  -- Apply linearity: Q(∑ cᵢ · atomᵢ) = ∑ cᵢ · Q(atomᵢ)
  rw [Q_finset_sum _ _ h_int h_sum]
  -- Now show ∑ᵢ cᵢ · Q(atomᵢ) ≥ 0
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact hc_nonneg i
  · exact h_atom (B i) (t i) (τ i) (hB_pos i) (ht_pos i) (h_support i)

/-! ## A5 (fixed-t): Extension from atoms to AtomCone_K_fixed -/

/-- If Q ≥ 0 on each Fejer_heat_atom with fixed t0, then Q ≥ 0 on AtomCone_K_fixed. -/
lemma Q_nonneg_on_atomcone_fixed_of_atoms (K t0 : ℝ) (_hK : K ≥ 1) (ht0 : t0 > 0)
    (h_atom : ∀ B τ, B > 0 → |τ| + B ≤ K →
              Q3.Q (Q3.Fejer_heat_atom B t0 τ) ≥ 0) :
    ∀ g ∈ Q3.AtomCone_K_fixed K t0, Q3.Q g ≥ 0 := by
  intro g hg
  obtain ⟨n, c, B, τ, hc_nonneg, hB_pos, h_support, hg_eq, _hg_WK⟩ := hg
  have hg_fn : g = fun x => ∑ i, c i * Q3.Fejer_heat_atom (B i) t0 (τ i) x := by
    ext x; exact hg_eq x
  rw [hg_fn]
  have h_int : ∀ i, MeasureTheory.Integrable
      (fun x => Q3.a_star x * Q3.Fejer_heat_atom (B i) t0 (τ i) x) := by
    intro i
    exact fejer_heat_atom_integrable_with_a_star (B i) t0 (τ i) (hB_pos i) ht0
  have h_sum : ∀ i, Summable
      (fun k => Q3.w_Q k * Q3.Fejer_heat_atom (B i) t0 (τ i) (Q3.xi_n k)) := by
    intro i
    exact fejer_heat_atom_prime_summable (B i) t0 (τ i) (hB_pos i) ht0
  rw [Q_finset_sum _ _ h_int h_sum]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact hc_nonneg i
  · exact h_atom (B i) (τ i) (hB_pos i) (h_support i)

end Q3.Proofs.Q_nonneg_lemmas
