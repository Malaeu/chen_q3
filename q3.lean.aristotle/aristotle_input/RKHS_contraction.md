# RKHS Contraction Theorem

## Setup

Define:
- w_RKHS(n) = Λ(n)/√n where Λ is von Mangoldt function
- w_max = sup_n w_RKHS(n) = 2/e ≈ 0.7358 < 1
- δ_K = minimal spacing between nodes on [-K,K]
- S_K(t) = Σ_{m≠n} exp(-(α_m - α_n)²/(4t))

The prime operator T_P has matrix elements:
```
T_P[i,j] = √w_RKHS(i) · √w_RKHS(j) · exp(-(ξ_i - ξ_j)²/(4t))
```

## Theorem (RKHS Contraction)

For K ≥ 1, there exists t > 0 and ρ < 1 such that ‖T_P‖ ≤ ρ.

## Proof Structure

**Step 1 (Gershgorin bound):**
By Gershgorin circle theorem applied to W^{1/2} G W^{1/2}:
```
‖T_P‖ ≤ w_max + √w_max · S_K(t)
```

**Step 2 (Geometric series bound for S_K):**
Since nodes are separated by at least δ_K:
```
S_K(t) ≤ 2·exp(-δ_K²/(4t)) / (1 - exp(-δ_K²/(4t)))
```

**Step 3 (Choose t to make S_K small):**
Set η_K = (1 - w_max - ε_K) / √w_max for small ε_K > 0.
Choose:
```
t_min(K) = δ_K² / (4·ln((2 + η_K)/η_K))
```
Then S_K(t_min) ≤ η_K.

**Step 4 (Contraction):**
```
ρ_K = w_max + √w_max · S_K(t_min)
    ≤ w_max + √w_max · η_K
    = w_max + (1 - w_max - ε_K)
    = 1 - ε_K < 1
```

## Key Lemmas

1. **Weight cap**: w_max = 2/e < 1
   - Proof: max of f(x) = log(x)/√x occurs at x = e² with f(e²) = 2/e

2. **Gershgorin bound**: ‖T_P‖ ≤ w_max + √w_max · S_K(t)
   - Proof: Apply Gershgorin to symmetric W^{1/2} G W^{1/2}

3. **Geometric tail**: S_K(t) ≤ 2q/(1-q) where q = exp(-δ_K²/(4t))
   - Proof: Nodes at distance ≥ jδ_K, geometric series bound

4. **t_min formula**: For t ≥ t_min(K), S_K(t) ≤ η_K
   - Proof: Solve 2q/(1-q) ≤ η for q, then for t
