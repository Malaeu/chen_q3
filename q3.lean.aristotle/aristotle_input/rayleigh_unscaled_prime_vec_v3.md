# Unscaled prime_vec vs normalized prime_vec v3

## Goal
Introduce the unnormalized evaluation vector and show it is a scalar multiple of `prime_vec`.
Then show the corresponding prime operator is scaled by `(2M+1)`.
This formalizes the source of the factor.

### Target statements (Lean-style)

```lean
noncomputable def prime_vec_unscaled (M : ℕ) (ξ : ℝ) : Fin (2*M+1) → ℂ :=
  fun i =>
    Complex.exp
      (-2 * Real.pi * Complex.I * ((Q3.fourier_index M i : ℤ) : ℂ) * (ξ : ℂ))

lemma prime_vec_unscaled_smul
  (M : ℕ) (ξ : ℝ) :
  prime_vec_unscaled M ξ
    = ((Real.sqrt (2*M+1 : ℝ)) : ℂ) • Q3.prime_vec M ξ := by
  -- expand `Q3.prime_vec`, simplify
```

Define a scaled operator (same sum, using `prime_vec_unscaled`):

```lean
noncomputable def T_P_comp_unscaled (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    Matrix (Fin (2*M+1)) (Fin (2*M+1)) ℂ :=
  fun i j =>
    ∑ n : Q3.Nodes K,
      ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
        prime_vec_unscaled M (Q3.xi_n n) i *
        Complex.conj (prime_vec_unscaled M (Q3.xi_n n) j)
```

Show scaling:

```lean
lemma T_P_comp_unscaled_eq
  (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
  T_P_comp_unscaled K B t M
    = ((2*M+1 : ℝ) : ℂ) • Q3.T_P_comp K B t M := by
  -- use prime_vec_unscaled_smul and distribute scalar through sum
```

## Available Lemmas
- `Q3.prime_vec` and `Q3.fourier_index` in `Q3/Basic/Defs.lean`.
- `Complex.conj_mul`, `mul_smul`, `smul_mul_assoc`, `Finset.sum_mul`.

## Proof Strategy
1) Expand `prime_vec_unscaled` and `Q3.prime_vec` to show scalar multiple.
2) Substitute into the sum and factor the scalar.
3) Use `(√(2M+1))^2 = 2M+1`.

## Policy
- Avoid `exact?` and heavy `aesop`.
- Prefer `simp`, `ring`, `nlinarith`.
