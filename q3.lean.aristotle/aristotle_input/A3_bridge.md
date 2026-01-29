# A3 Toeplitz-Symbol Bridge Theorem

## Setup

Define:
- Fejér×heat window: Φ_{B,t}(ξ) = (1 - |ξ|/B)_+ · exp(-4π²t·ξ²)
- P_A = smoothed Archimedean symbol on [-B,B]
- w(n) = 2Λ(n)/√n (prime weights)
- ξ_n = log(n)/(2π) (prime nodes)
- T_M[P_A] = Toeplitz operator on trigonometric polynomials of degree ≤ M
- T_P^{(M)} = compression of prime operator to same space
- c_0(K) = inf{a*(ξ) : |ξ| ≤ K} > 0 (archimedean lower bound)

## Theorem (A3 Bridge)

For K ≥ 1, there exist M₀ ∈ ℕ and t > 0 such that for all M ≥ M₀:
```
λ_min(T_M[P_A] - T_P^{(M)}) ≥ c_0(K)/4
```

Equivalently, for all nonzero v ∈ ℝ^M:
```
⟨(T_M[P_A] - T_P)v, v⟩ / ⟨v, v⟩ ≥ c_0(K)/4
```

## Proof Structure

**Step 1 (Rayleigh identification):**
For any trigonometric polynomial p:
```
⟨(T_M[P_A] - T_P^{(M)})p, p⟩ = ∫ P_A(θ)|p(θ)|²dθ/(2π) - Σ w(n)Φ_{B,t}(ξ_n)|p(ξ_n)|²
```

**Step 2 (Link to Q functional):**
For p ≡ 1 (constant):
```
⟨(T_M[P_A] - T_P^{(M)})1, 1⟩ = Q(Φ_{B,t})/(2π)
```

**Step 3 (Szegő-Böttcher approximation):**
By Szegő limit theorem, as M → ∞:
```
λ_min(T_M[P_A]) → inf P_A(θ) ≥ c_0(K)
```

**Step 4 (RKHS contraction):**
Choose t so that ‖T_P‖ ≤ c_0(K)/4 (from RKHS theorem).
Then:
```
λ_min(T_M[P_A] - T_P) ≥ λ_min(T_M[P_A]) - ‖T_P‖
                       ≥ c_0(K) - c_0(K)/4 = 3c_0(K)/4
```

For finite M, continuity of modulus gives M₀ such that for M ≥ M₀:
```
λ_min(T_M[P_A] - T_P) ≥ c_0(K)/2 > c_0(K)/4
```

## Key Lemmas

1. **Toeplitz quadratic form**: Standard Szegő-Böttcher theory

2. **Rayleigh quotient identity**: Combine model space restriction with prime sum

3. **Szegő limit theorem**: λ_min(T_M[f]) → ess inf f as M → ∞

4. **Modulus of continuity**: ω_{P_A}(π/M) → 0 as M → ∞
