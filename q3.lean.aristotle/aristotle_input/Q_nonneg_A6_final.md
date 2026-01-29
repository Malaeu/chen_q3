# Q_nonneg_A6: Final Theorem (Replace Axiom)

## Goal
Replace the axiom `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` with a theorem
that combines A3 bridge + RKHS cap to prove Q ≥ 0 on AtomCone_K.

## Lean Statement
```lean
import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.P_A_Toeplitz_bridge
import Q3.Proofs.RKHS_cap_rayleigh
import Q3.Proofs.Rayleigh_Q_identification

/-- Main theorem: Q ≥ 0 on AtomCone_K given A3 bridge and RKHS contraction -/
theorem Q_nonneg_on_atoms_of_A3_Fourier_RKHS
    (K : ℝ) (hK : K ≥ 1) [Fintype (Q3.Nodes K)]
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K)
    (hRKHS : Q3.RKHS_contraction_data K) :
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 := by
  sorry
```

## Proof Strategy (high-level)
1. Apply `Q_nonneg_on_atomcone_of_atoms` (A5): reduce to proving Q ≥ 0 on single atoms
2. For each atom `Fejer_heat_atom B t τ`:
   - Use `rayleigh_basis0_of_A3` (A4) to get Rayleigh lower bound
   - Use `weight_sum_le_rho_one` from hRKHS to get RKHS cap
   - Apply `Q_nonneg_fejer_heat_window` (A3) to conclude Q ≥ 0

## Dependencies
- **A1** `Q_finset_sum` — linearity
- **A2** `prime_sum_nonneg` — positivity of prime sum
- **A3** `Q_nonneg_fejer_heat_window` — atom lower bound
- **A4** `rayleigh_basis0_of_A3` — extract Rayleigh bound from A3
- **A5** `Q_nonneg_on_atomcone_of_atoms` — extend to cone

## Key Constants (verified)
```
c* = 11/10 = 1.1
c*/4 = 0.275
ρ₁ = 1/25 = 0.04
c*/4 - ρ₁ = 0.235 > 0  ← positivity margin
```

## Available Lemmas (already proven in project)
- `Q3.Proofs.RayleighQId.honest_formula`
- `Q3.Proofs.RayleighQId.rayleigh_Q_eq_Q`
- `Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum`
- `Q3.Proofs.RKHS_cap.weight_sum_le_rho_one`
- `c_star_div_four_le_sub_rho_one`

## Policy
- This is the **composition** of A1-A5
- Use `suffices` to structure the proof
- Apply each sub-lemma in order
- Use `nlinarith` for the final arithmetic

## Success Criteria
After integrating this theorem:
1. `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` removed from axioms
2. `#print axioms Q3.Main.RH_of_Weil_and_Q3` shows 9 axioms (not 10)
