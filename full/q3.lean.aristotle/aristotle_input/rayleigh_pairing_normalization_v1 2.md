# Rayleigh Pairing Normalization v1 (prime_vec vs evaluation)

## Goal
Prove the exact normalization relation between the evaluation functional and `prime_vec`.
We want a lemma that makes the (2M+1) factor explicit.

### Target statement (Lean-style)
Introduce a symmetric trigonometric polynomial using `fourier_index`:

```lean
noncomputable def trigPoly_sym (M : ℕ) (v : Fin (2*M+1) → ℂ) (θ : ℝ) : ℂ :=
  ∑ i : Fin (2*M+1), v i *
    Complex.exp (2 * Real.pi * Complex.I * ((Q3.fourier_index M i : ℤ) : ℂ) * (θ : ℂ))
```

Prove:

```lean
lemma inner_prime_vec_eq_eval
  (M : ℕ) (v : Fin (2*M+1) → ℂ) (ξ : ℝ) :
  (∑ i : Fin (2*M+1), Complex.conj (Q3.prime_vec M ξ i) * v i)
    = ((1 / Real.sqrt (2*M+1 : ℝ)) : ℂ) * trigPoly_sym M v ξ := by
  -- explicit expansion + simp [Q3.prime_vec, trigPoly_sym]
```

Corollary (explicit factor):

```lean
lemma eval_factor
  (M : ℕ) (v : Fin (2*M+1) → ℂ) (ξ : ℝ) :
  trigPoly_sym M v ξ
    = ((Real.sqrt (2*M+1 : ℝ)) : ℂ) *
        (∑ i, Complex.conj (Q3.prime_vec M ξ i) * v i) := by
  -- algebraic rearrangement of inner_prime_vec_eq_eval
```

## Available Lemmas
- `Q3.prime_vec` in `Q3/Basic/Defs.lean`.
- `Q3.fourier_index` in `Q3/Basic/Defs.lean`.
- `Complex.exp_mul`, `Complex.conj_mul`, `Complex.conj_exp`.

## Proof Strategy
1) Expand the sum using the definition of `prime_vec`.
2) Simplify the conjugate of the exponential.
3) Factor out the constant `1/√(2M+1)`.

## Policy
- Avoid `exact?` and heavy `aesop`.
- Prefer `simp`, `ring`, `by` rewrites, and `suffices`.

## Definitions
Use the exact definitions from `Q3/Basic/Defs.lean` for `prime_vec` and `fourier_index`.
