# Rayleigh Scaling Obstruction v2 (uniform cap vs (2M+1))

## Goal
Formalize that scaling the operator by `(2M+1)` multiplies all Rayleigh quotients,
so a uniform cap cannot survive when M grows.

### Target statements (Lean-style)

```lean
lemma rayleigh_smul
  (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (c : ℝ) :
  Q3.RayleighQuotient (c • A) v = c * Q3.RayleighQuotient A v := by
  -- unfold RayleighQuotient, simp [Matrix.smul_mulVec, dotProduct, mul_comm, mul_assoc]
```

Corollary (uniform cap obstruction):

```lean
lemma rayleigh_cap_scales
  (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (c : ℝ) :
  Q3.RayleighQuotient A v ≤ ρ →
  Q3.RayleighQuotient (c • A) v ≤ |c| * ρ := by
  -- use rayleigh_smul + `mul_le_mul_of_nonneg_left`
```

Specialize to `c = (2*M+1)` and `A = Q3.T_P_comp_real K K t M` to show
that any uniform bound in M is destroyed by `(2M+1)•A`.

## Available Lemmas
- `Q3.RayleighQuotient` definition in `Q3/Axioms.lean` or `Q3/Proofs/Rayleigh_utils.lean`.
- `Matrix.smul_mulVec`, `Matrix.dotProduct` simp lemmas.

## Proof Strategy
1) Expand Rayleigh quotient.
2) Pull scalar out of numerator.
3) Rewrite inequality with absolute value.

## Policy
- Avoid `exact?` and heavy `aesop`.
- Prefer `simp`, `ring`, `nlinarith`.
