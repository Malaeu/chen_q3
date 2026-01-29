# Q_nonneg_A3: Lower Bound for Q on Single Atom

## Goal
Prove Q ≥ 0 for a single fejer_heat_window using Rayleigh identification + RKHS cap.

## Lean Statement
```lean
import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.RKHS_cap_rayleigh

open scoped BigOperators

/-- Q is nonnegative on a single fejer_heat_window atom -/
lemma Q_nonneg_fejer_heat_window
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (hB : 0 < B) (hK : B ≤ K) (ht : t > 0)
    (hM : 0 < 2 * M + 1)
    (h_rayleigh : Q3.Proofs.RayleighQId.rayleigh_quotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
         Q3.T_P_comp_real K B t M)
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4)
    (h_cap : ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) ≤ rho_one) :
    Q3.Q (Q3.fejer_heat_window B t) ≥ 0 := by
  sorry
```

## Key Identity (honest_formula, proven)
```
RQ(Toeplitz - T_P_comp, basis0) = arch_term - (1/(2M+1)) · prime_sum
```

## Proof Strategy
1. Use `honest_formula` to get: `arch_term = RQ(...) + (1/(2M+1)) · prime_sum`
2. From `h_rayleigh`: `RQ(...) ≥ c*/4`
3. So: `arch_term ≥ c*/4 + (1/(2M+1)) · prime_sum`
4. Q = arch_term - prime_sum ≥ c*/4 + (1/(2M+1) - 1) · prime_sum
5. Since `1/(2M+1) - 1 = -2M/(2M+1)` and `2M/(2M+1) < 1`:
   Q ≥ c*/4 - prime_sum ≥ c*/4 - rho_one > 0

## Key Constants
- c* = 11/10 = 1.1
- c*/4 = 0.275
- rho_one = 1/25 = 0.04
- c*/4 - rho_one = 0.235 > 0

## Available Lemmas
- `Q3.Proofs.RayleighQId.honest_formula` — the key identity
- `Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum` — finite sum = tsum
- `c_star_div_four_le_sub_rho_one` — c*/4 - ρ₁ > 0
- `prime_sum_nonneg` — from A2

## Policy
- Use `suffices` to reduce to arithmetic
- Use `nlinarith` for final bound
- Avoid heavy `aesop`
