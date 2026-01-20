# Insight: Carleson Measure Property — Implicit Proof

**Date:** 2026-01-17
**Category:** Analysis / RKHS
**Status:** Documented

## Discovery

The Carleson measure property for prime sampling is **already implicitly proven** in the existing codebase!

## What is Carleson Measure

For an RKHS H with reproducing kernel K, a measure μ is C-Carleson if:
```
∑_n μ_n |f(x_n)|² ≤ C · ‖f‖²_H  for all f ∈ H
```

## Proof Chain (Already Exists!)

1. **Node spacing** (`node_spacing.lean`):
   ```
   |ξ_i - ξ_j| ≥ |i-j| · δ_K
   ```

2. **Off-diagonal decay** (`off_diag_exp_sum.lean`):
   ```
   ∑_{j≠i} exp(-(ξ_i - ξ_j)²/(4t)) ≤ S_K = 2r/(1-r)
   ```
   where r = exp(-δ_K²/(4t)) — geometric series bound.

3. **Weight sum bound** (`RKHS_cap_rayleigh.lean`):
   ```
   ∑_n w_Q(n)·Φ(ξ_n) ≤ ρ₁ = 1/25
   ```

4. **Schur test** → Operator norm ≤ row sum → ρ₁

## Result

```lean
theorem prime_sampling_is_carleson (K : ℝ) (hK : K > 0) [Fintype (Q3.Nodes K)] :
    is_carleson K t_rkhs_cap rho_one
```

The prime sampling measure μ = Σ w_Q(n)·δ_{ξ_n} is a ρ₁-Carleson measure for heat RKHS.

Since **ρ₁ = 1/25 < 1**, the sampling is **contractive** — enables arch ≥ prime argument.

## Key Files

| Component | File |
|-----------|------|
| Node spacing | `Q3/Proofs/node_spacing.lean` |
| Off-diagonal | `Q3/Proofs/off_diag_exp_sum.lean` |
| Weight sum | `Q3/Proofs/RKHS_cap_rayleigh.lean` |
| Carleson explicit | `Q3/Proofs/Carleson_prime.lean` |

## Impact

No new axioms needed — this is **documentation of existing proof**, not new mathematics.
