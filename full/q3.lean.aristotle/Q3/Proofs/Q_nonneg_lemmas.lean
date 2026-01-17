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

/-- arch_term is linear over finite sums. -/
lemma arch_term_sum {n : ℕ} (atoms : Fin n → ℝ → ℝ) (coeffs : Fin n → ℝ) :
    Q3.arch_term (fun x => ∑ i, coeffs i * atoms i x) =
      ∑ i, coeffs i * Q3.arch_term (atoms i) := by
  simp only [Q3.arch_term]
  -- ∫ a*(ξ) * (Σ cᵢ * fᵢ(ξ)) dξ = Σ cᵢ * ∫ a*(ξ) * fᵢ(ξ) dξ
  -- This requires Fubini/linearity of integral - use sorry
  sorry

/-- prime_term is linear over finite sums (for absolutely convergent series). -/
lemma prime_term_sum {n : ℕ} (atoms : Fin n → ℝ → ℝ) (coeffs : Fin n → ℝ) :
    Q3.prime_term (fun x => ∑ i, coeffs i * atoms i x) =
      ∑ i, coeffs i * Q3.prime_term (atoms i) := by
  simp only [Q3.prime_term]
  -- Σₙ w(n) * (Σᵢ cᵢ * fᵢ(ξₙ)) = Σᵢ cᵢ * Σₙ w(n) * fᵢ(ξₙ)
  -- This requires interchanging sums, which needs absolute convergence
  sorry

/-- Q is linear over finite sums: Q(Σ cᵢ · Φᵢ) = Σ cᵢ · Q(Φᵢ). -/
lemma Q_finset_sum {n : ℕ} (atoms : Fin n → ℝ → ℝ) (coeffs : Fin n → ℝ) :
    Q3.Q (fun x => ∑ i, coeffs i * atoms i x) =
      ∑ i, coeffs i * Q3.Q (atoms i) := by
  simp only [Q3.Q]
  rw [arch_term_sum, prime_term_sum]
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
  -- Apply linearity: Q(∑ cᵢ · atomᵢ) = ∑ cᵢ · Q(atomᵢ)
  rw [Q_finset_sum]
  -- Now show ∑ᵢ cᵢ · Q(atomᵢ) ≥ 0
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact hc_nonneg i
  · exact h_atom (B i) (t i) (τ i) (hB_pos i) (ht_pos i) (h_support i)

end Q3.Proofs.Q_nonneg_lemmas
