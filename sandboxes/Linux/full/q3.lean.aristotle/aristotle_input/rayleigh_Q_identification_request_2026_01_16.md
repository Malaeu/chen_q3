# Rayleigh–Q identification (Theorem 3.3) for Fejer×heat window

Goal: prove the Rayleigh–Q identification used to remove
`Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`.

Target file suggestion: `Q3/Proofs/Rayleigh_Q_identification.lean`.

## Target statement (Lean sketch)

We want the equality from tex Theorem 3.3:

```
  ⟨(T_M[P_A] - T_P^{(M)}) 1, 1⟩ = Q(Φ_{B,t})
```

Translated to Lean with our definitions:

```
import Q3.Axioms
import Q3.Basic.Defs
import Q3.Proofs.Rayleigh_Fourier
import A3_FLOOR_v22_stage4_floor

noncomputable section

open scoped BigOperators

namespace Q3.Proofs

-- basis vector for the constant polynomial p ≡ 1
noncomputable def basis0 (M : ℕ) : Fin (2 * M + 1) → ℝ :=
  let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩
  fun i => if i = i0 then (1 : ℝ) else 0

/-- Rayleigh–Q identification (tex Thm 3.3). -/
theorem rayleigh_Q_identification
    (B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes B)] :
    (2 * M + 1 : ℝ) *
      Q3.RayleighQuotient
        (Q3.Proofs.RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t)
          - Q3.T_P_comp_real B B t M)
        (basis0 M)
    =
      Q3.Q (fun ξ => Q3.fejer_heat_window B t ξ) := by
  -- proof
  -- 1) quadratic form for Toeplitz part with basis0 gives integral of P_A
  -- 2) quadratic form for T_P_comp_real with basis0 gives (1/(2M+1)) * prime term
  -- 3) periodization integral: ∫_{-1/2}^{1/2} P_A = ∫ a_star * fejer_heat_window
  -- 4) prime term reduces to sum over Nodes B because window has support |ξ| ≤ B
  -- combine
  sorry

end Q3.Proofs
```

Notes:
- `P_A` is defined in `A3_FLOOR_v22_stage4_floor.lean` as the periodized symbol.
- `fejer_heat_window` is defined in `Q3.Basic.Defs` and is the window used in A3.
- The factor `(2*M+1)` is expected due to the normalization in `prime_vec`.
  (See `prime_vec_norm` and `prime_vec_norm_sq_sum` in `Q3/Basic/Defs.lean`.)

## Helpful lemmas / hints

1) For ToeplitzEntry diagonal:
```
ToeplitzEntry P i i = ∫ θ in (-1/2)..(1/2), (P θ : ℂ)
```
(since exp term is 1).

2) For the quadratic form with `basis0`, the double sum reduces to the diagonal entry.

3) For the prime operator diagonal:
use `prime_vec_norm` / `prime_vec_norm_sq_sum` to show
```
(Q3.T_P_comp_real B B t M) i0 i0
  = (1 / (2*M+1)) * ∑ n : Nodes B, w_Q n * fejer_heat_window B t (xi_n n)
```

4) Periodization integral:
```
∫_{-1/2}^{1/2} P_A B t θ dθ = ∫_ℝ a_star ξ * fejer_heat_window B t ξ dξ
```
Use periodization lemmas from `Q3/Archive/04_A3_aristotle.lean` if needed
(e.g., `integral_eq_sum_integral_shift`).

5) Prime term reduction:
Since `fejer_heat_window B t ξ = 0` for |ξ| ≥ B, the `prime_term` equals
`∑ n : Nodes B, w_Q n * fejer_heat_window B t (xi_n n)`.

Please provide a complete Lean proof with no `sorry`/`exact?`.
