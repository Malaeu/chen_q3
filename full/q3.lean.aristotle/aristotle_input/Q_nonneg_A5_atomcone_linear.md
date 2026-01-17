# Q_nonneg_A5: Extension from Atoms to AtomCone_K

## Goal
Prove Q ≥ 0 on AtomCone_K given Q ≥ 0 on individual atoms.

## Lean Statement
```lean
import Mathlib
import Q3.Basic.Defs

/-- AtomCone_K: nonnegative linear combinations of fejer_heat atoms -/
def AtomCone_K (K : ℝ) : Set (ℝ → ℝ) :=
  {g | ∃ (n : ℕ) (atoms : Fin n → ℝ → ℝ) (coeffs : Fin n → ℝ),
       (∀ i, ∃ B t τ, atoms i = Q3.Fejer_heat_atom B t τ) ∧
       (∀ i, coeffs i ≥ 0) ∧
       g = fun x => ∑ i, coeffs i * atoms i x}

/-- If Q ≥ 0 on each atom, then Q ≥ 0 on AtomCone_K -/
lemma Q_nonneg_on_atomcone_of_atoms
    (K : ℝ) (hK : K ≥ 1)
    (h_atom : ∀ B t τ, B > 0 → t > 0 → |τ| ≤ K →
              Q3.Q (Q3.Fejer_heat_atom B t τ) ≥ 0) :
    ∀ g ∈ AtomCone_K K, Q3.Q g ≥ 0 := by
  sorry
```

## Proof Strategy
1. Take g ∈ AtomCone_K, destructure into atoms and coefficients
2. Use linearity: Q(∑ᵢ cᵢ · atomᵢ) = ∑ᵢ cᵢ · Q(atomᵢ) (from A1)
3. Each Q(atomᵢ) ≥ 0 by h_atom
4. Each cᵢ ≥ 0 by AtomCone_K definition
5. Conclude: ∑ᵢ cᵢ · Q(atomᵢ) ≥ 0 by `Finset.sum_nonneg`

## Available Lemmas
- `Q_finset_sum` — linearity of Q (from A1)
- `Finset.sum_nonneg` — sum of nonneg terms is nonneg
- `mul_nonneg` — product of nonneg is nonneg

## Policy
- Use `intro g ⟨n, atoms, coeffs, h_atoms, h_coeffs, hg⟩`
- Apply linearity first, then positivity
- Use `gcongr` or `nlinarith` for final step
