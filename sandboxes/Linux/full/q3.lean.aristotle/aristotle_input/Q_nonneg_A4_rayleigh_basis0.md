# Q_nonneg_A4: Rayleigh Lower Bound on basis0 from A3 Bridge

## Goal
Extract the Rayleigh lower bound on basis0 from A3_bridge_data_rayleigh_Fourier.

## Lean Statement
```lean
import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.P_A_Toeplitz_bridge

/-- From A3 bridge data, extract Rayleigh lower bound on constant vector -/
lemma rayleigh_basis0_of_A3
    (K : ℝ) (hK : K ≥ 1) [Fintype (Q3.Nodes K)]
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K) :
    ∃ t > 0, ∃ B > 0, ∀ M : ℕ,
      Q3.Proofs.RayleighQId.rayleigh_quotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
         Q3.T_P_comp_real K B t M)
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  sorry
```

## A3_bridge_data_rayleigh_Fourier (structure)
This structure provides:
- For all v ≠ 0: RQ(Toeplitz - T_P_comp, v) ≥ c*/4
- In particular, for v = basis0 (the constant vector)

## Proof Strategy
1. Obtain existential witnesses (t, B) from `hA3`
2. Use `basis0_ne_zero` to show basis0 ≠ 0
3. Instantiate the ∀ v statement with v = basis0
4. The bound follows directly

## Available Lemmas
- `Q3.Proofs.RayleighQId.basis0_ne_zero` — basis0 M ≠ 0 for M ≥ 0
- `A3_bridge_data_rayleigh_Fourier.rayleigh_lower` — the ∀ v bound

## Policy
- This is a straightforward unfolding/instantiation
- Use `obtain` to destructure existentials
- Use `exact` with explicit application
- Short proof expected (< 15 lines)
