# Q3-2_rel: Minimal Fix from GPT 5.2 PRO (P1)

**Date:** 2024-12-23

## Problem with G^{-1} Rayleigh

The absolute Rayleigh quotient with G^{-1}:
```
‖B_α‖² = sup_{y≠0} [y*(W U_α G U_α* W)y] / [y* G^{-1} y]
```

Is:
- **Formally correct** for absolute norm
- **Too strong** as a mathematical target (spiky vectors don't see phases)
- **Numerically toxic** when G is ill-conditioned (cond ~ 10^17)

## The Fix: Q3-2_rel (Relative Contraction)

### Definition (relative contraction ratio)

On each dyadic block j, define:
- **B_{α,j} := G_j^{1/2} · W_j · U_{α,j} · G_j^{1/2}**
- **B_{0,j} := G_j^{1/2} · W_j · G_j^{1/2}**  (baseline α=0)

and the **relative ratio**:
```
r(α;N,j) := ‖B_{α,j}‖₂ / ‖B_{0,j}‖₂
```

### Q3-2_rel (Minimal Statement)

There exist constants **ρ ∈ (0,1)** and **N₀** such that for all **N ≥ N₀** and all **α ∈ 𝔪(N;Q)** we have, uniformly in dyadic blocks j:
```
r(α;N,j) ≤ ρ
```

Equivalently (top-eigenvalue form):
```
λ_max(B_{α,j} B_{α,j}*) ≤ ρ² · λ_max(B_{0,j} B_{0,j}*)
```

**This matches the empirical observable r_worst exactly!**

### Optional normalization (cleanest for chaining)

Let λ_j := ‖B_{0,j}‖₂ and define:
```
B̂_{α,j} := (1/λ_j) · B_{α,j}
```

Then Q3-2_rel becomes absolute contraction:
```
‖B̂_{α,j}‖₂ ≤ ρ < 1
```

## From Rep(N) + Q3-2_rel to Q3-1

If you have Q3-2_rel:
```
∀j, ∀α ∈ 𝔪: ‖B_{α,j}‖ ≤ ρ · ‖B_{0,j}‖  with 0 < ρ < 1
```

Then:
```
|S_ψ(α;N)| ≤ ‖u_N‖ · ‖v_N‖ · ∏_{j=0}^{J-1} ‖B_{α,j}‖ + |Err|
          ≤ ‖u_N‖ · ‖v_N‖ · ρ^J · ∏_{j=0}^{J-1} ‖B_{0,j}‖ + |Err|
```

### Mass Lemma (required separately)

```
‖u_N‖ · ‖v_N‖ · ∏_{j=0}^{J-1} ‖B_{0,j}‖ ≪ N^{1/2}
```

Then since J ≍ log N, ρ^J = N^{-δ} and:
```
|S_ψ(α;N)| ≪ N^{1/2 - δ'}
```

## Key Insight: G^{-1} is still correct but fragile

> Note: the identity
> ```
> ‖B_{α,j}‖₂² = sup_{y≠0} [y*(W_j U_{α,j} G_j U_{α,j}* W_j)y] / [y* G_j^{-1} y]
> ```
> is still correct, but it is **numerically fragile** when G_j is ill-conditioned.
> The **relative ratio** ‖B_{α,j}‖/‖B_{0,j}‖ is the stable "physics" observable.

## Reality-check: t parameter

For heat kernel `exp(-(Δξ)²/(4t))`:
- Increasing t makes G **more flat** (worse!)
- To decrease off-diagonal, t needs to **decrease**
- Or use per-block scaling: t_j ~ 2^{-2j}

## Numerical Results (v4 Power Iteration)

| N | ‖B_0‖ | ‖B_α‖_bdry | r_bdry | Status |
|---|-------|------------|--------|--------|
| 5k | 13.1 | 5.73 | 0.437 | ✅ |
| 10k | 19.2 | 8.46 | 0.440 | ✅ |
| 20k | 26.3 | 11.5 | 0.438 | ✅ |
| 30k | 52.0 | 24.0 | 0.462 | ✅ |
| 50k | 74.6 | 33.4 | 0.448 | ✅ |
| 100k | 104.7 | 46.5 | 0.444 | ✅ |

**r_bdry ≈ 0.44 stable for all N up to 100k!**

## Code: boundary_alpha_stress_test_v4.py

Uses Power Iteration without G^{-1} inversion.
Implements exactly the Q3-2_rel metric.
