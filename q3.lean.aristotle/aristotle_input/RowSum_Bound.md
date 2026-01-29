# T_P Matrix Row Sum Bound (Gershgorin-style)

## Setup

Let K ≥ 1 and t > 0 be parameters. Let Nodes_K be a finite set of natural numbers.

Define:
- **w_RKHS(n)** = Λ(n)/√n where Λ is the von Mangoldt function
- **w_max** = 2/e ≈ 0.7358 (maximum of w_RKHS over all n)
- **ξ_n** = log(n)/(2π) (spectral coordinate)
- **δ_K** = 1/(2π·N_K) where N_K = ⌊exp(2πK)⌋ (minimum node spacing)
- **S_K(t)** = 2x/(1-x) where x = exp(-δ_K²/(4t)) (geometric series tail bound)

The T_P matrix is defined by:
T_P[i,j] = √(w_RKHS(i)) · √(w_RKHS(j)) · exp(-(ξ_i - ξ_j)²/(4t))

## Theorem 1: Off-diagonal exponential sum bound

For any node i in Nodes_K:
Σ_{j≠i} exp(-(ξ_i - ξ_j)²/(4t)) ≤ S_K(t)

### Proof Sketch

1. **Node spacing**: Consecutive nodes are separated by at least δ_K in ξ-coordinates.
   For adjacent nodes n, m with n < m: |ξ_m - ξ_n| = |log(m) - log(n)|/(2π) ≥ δ_K.

2. **Geometric series bound**:
   The terms exp(-(ξ_i - ξ_j)²/(4t)) decay exponentially with distance.
   For j at distance k·δ_K from i:
   exp(-(k·δ_K)²/(4t)) = exp(-k²·δ_K²/(4t)) ≤ x^k where x = exp(-δ_K²/(4t))

3. **Sum bound**:
   Σ_{j≠i} exp(...) ≤ 2 · Σ_{k=1}^∞ x^k = 2x/(1-x) = S_K(t)
   (Factor 2 for both directions from i.)

## Theorem 2: Row sum bound for T_P

For any row i:
Σ_j |T_P[i,j]| ≤ w_max + √w_max · S_K(t)

### Proof Sketch

**Step 1: All entries are nonnegative**
T_P[i,j] = √w_i · √w_j · exp(-...) ≥ 0
So |T_P[i,j]| = T_P[i,j].

**Step 2: Split into diagonal and off-diagonal**
Σ_j T_P[i,j] = T_P[i,i] + Σ_{j≠i} T_P[i,j]

**Step 3: Diagonal bound**
T_P[i,i] = √w_i · √w_i · exp(0) = w_RKHS(i) ≤ w_max

**Step 4: Off-diagonal bound**
Σ_{j≠i} T_P[i,j] = √w_i · Σ_{j≠i} √w_j · exp(-(ξ_i - ξ_j)²/(4t))
                 ≤ √w_max · Σ_{j≠i} √w_max · exp(...)
                 = w_max · Σ_{j≠i} exp(...)
                 ≤ w_max · S_K(t)

Wait, this gives w_max + w_max·S_K, not w_max + √w_max·S_K.

**Corrected Step 4:**
Actually factor more carefully:
Σ_{j≠i} T_P[i,j] = √w_i · Σ_{j≠i} √w_j · exp(...)

The sum Σ_{j≠i} √w_j · exp(...) can be bounded as:
≤ √w_max · Σ_{j≠i} exp(...) ≤ √w_max · S_K(t)

Then total off-diagonal ≤ √w_i · √w_max · S_K ≤ √w_max · √w_max · S_K = w_max · S_K.

Hmm, the axiom says √w_max · S_K. Let me reconsider...

Actually the bound in the axiom is:
Σ_j |T_P[i,j]| ≤ w_max + √w_max · S_K

This suggests a tighter bound on off-diagonal. Perhaps:
Σ_{j≠i} T_P[i,j] ≤ √w_max · S_K

This would require: √w_i · Σ_{j≠i} √w_j · exp(...) ≤ √w_max · S_K

Since √w_i ≤ √w_max and Σ_{j≠i} √w_j · exp(...) ≤ ???

The issue is whether we need both √w_i and √w_j factors absorbed.

**Alternative proof**: Use Schur test formulation where row sums incorporate the weight pattern differently.

## Key Lemmas Needed

1. w_RKHS(n) ≤ w_max for all n (proven: log(n)/√n ≤ 2/e)
2. √w_RKHS(n) ≤ √w_max (follows from above)
3. Node spacing ≥ δ_K
4. Geometric series: Σ_{k=1}^∞ x^k = x/(1-x) for 0 < x < 1

## Expected Lean Statement

```lean
theorem T_P_row_sum_bound (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    (Nodes_K : Set ℕ) [Fintype Nodes_K] (T_P : Matrix Nodes_K Nodes_K ℝ)
    (hT_P : ∀ i j, T_P i j = √(w_RKHS i) * √(w_RKHS j) * exp(-(ξ_i - ξ_j)²/(4t))) :
    ∀ i, Σ j, |T_P i j| ≤ w_max + √w_max * S_K K t
```
