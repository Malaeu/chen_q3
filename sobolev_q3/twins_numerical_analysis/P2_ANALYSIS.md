# P2 Analysis: Power Iteration and Debug (2024-12-23)

## Key Insight from P2

### Why α = 1/2 shows no cancellation

For odd primes p:
```
e(p/2) = exp(2πi · p · 1/2) = exp(πi · p) = (-1)^p = -1
```

So for α = 1/2, U_α = -I for all odd primes. The phase doesn't create any cancellation — this is **normal and expected!**

### Where cancellation SHOULD happen

At α ≈ 1/6 ± Q/(qN), the phases create destructive interference:
```
Expected: r_bdry ≈ 0.4-0.5 < 1
```

Our v5 results confirm this:
```
α ≈ 1/6 (q=6): r_bdry ≈ 0.44 ✅
```

## The Correct Computation

### Object we compute:
```
‖B_α‖² = sup_{y≠0} [y*(W U_α G U_α* W)y] / [y* G^{-1} y]
```

### Stable reformulation (no explicit G^{-1}):

Let G = LL* (Cholesky), then y = Lu gives:
```
‖B_α‖² = λ_max(L* (W U_α G U_α* W) L)
```

This is just the largest eigenvalue of a Hermitian PSD matrix M_α = L* A_α L.

### Power iteration:

```python
def rho_abs_power(G, w, phase, ...):
    L, jitter, kind = stable_factor_psd(G)

    def apply_A(x):
        return w * (phase * (G @ (conj_phase * (w * x))))

    def mv(u):
        return L.conj().T @ apply_A(L @ u)

    lam, v, it = power_iteration_hermitian(mv, n)
    return sqrt(lam)
```

## Debug Verification

For small blocks (n ≤ 200), compare power iteration with exact eigvalsh:

```python
# Exact computation
M = L.conj().T @ A @ L
lam_exact = eigvalsh(M)[-1]

# Power iteration
lam_power, v, it = power_iteration_hermitian(mv, n)

# Compare
rel_err = abs(lam_power - lam_exact) / max(lam_exact, 1e-12)
```

**Our results: rel_err ≈ 10^{-14}** — excellent agreement!

## Summary

| Issue | Solution | Status |
|-------|----------|--------|
| G^{-1} unstable | Use L* A L factorization | ✅ |
| Monte-Carlo noise | Power iteration | ✅ |
| α = 1/2 no cancellation | Normal! Use α ≈ 1/6 | ✅ |
| Verify correctness | Debug: power vs exact | ✅ |

## Files

- `boundary_alpha_stress_test_v5.py` — with P2 debug functions
- `Q3_2_REL_FIX.md` — P1's Q3-2_rel formulation
- `Q3_2_REL_FORMALIZATION.md` — Aristotle input

## Numerical Evidence

| N | r_bdry | worst q | Status |
|---|--------|---------|--------|
| 5k | 0.437 | 6 | ✅ |
| 10k | 0.440 | 6 | ✅ |
| 20k | 0.438 | 6 | ✅ |
| 50k | 0.448 | 6 | ✅ |
| 100k | 0.444 | 6 | ✅ |
| 200k | 0.443 | 6 | ✅ |
| 500k | 0.462 | 6 | ✅ |

**Conclusion:** Q3-2_rel confirmed numerically with r ≈ 0.44-0.46 stable from N=5k to 500k (166 min compute time for 500k).
