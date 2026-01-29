# Prime Term ↔ Nodes K Bridge

**Date:** 2026-01-17
**Status:** IMPLEMENTED (1 sorry for tsum=finite_sum machinery)
**Files:** `Q3/Proofs/Rayleigh_Q_identification.lean` (lines 420-481)

## The Gap

`rayleigh_Q_identification` proves:
```
RQ(Toeplitz) − (2M+1)·RQ(T_P_comp) = arch_term - Σ_{n : Nodes K} w_Q(n)·Φ(ξ_n)
```

But `Q3.Q` uses `prime_term` which is a **tsum over all n**:
```lean
def prime_term (Φ : ℝ → ℝ) : ℝ := ∑' n, w_Q n * Φ (xi_n n)
```

## The Bridge

For `Φ` with compact support in `[-B, B]` and `K ≥ B`:

```
prime_term Φ = ∑ n : Nodes K, w_Q n * Φ (xi_n n)
```

**Why this works:**
1. For `n < 2`: `w_Q n = 0` (vonMangoldt vanishes)
2. For `n ≥ 2` with `|xi_n n| > K`: `Φ(xi_n n) = 0` (outside support)
3. Therefore: tsum = finite sum over `{n | |xi_n n| ≤ K ∧ n ≥ 2}` = `Nodes K`

## For `fejer_heat_window B t`

Support: `{ξ | |ξ| ≤ B}` (Fejér kernel vanishes at `|ξ| > B`)

So choosing `K ≥ B` gives:
```
prime_term (fejer_heat_window B t) = ∑ n : Nodes K, w_Q n * fejer_heat_window B t (xi_n n)
```

## Implementation (DONE)

Added to `Q3/Proofs/Rayleigh_Q_identification.lean`:

1. ✓ `fejer_heat_window_support`: `|ξ| > B → fejer_heat_window B t ξ = 0`
2. ✓ `w_Q_zero_of_lt_two`: `n < 2 → w_Q n = 0`
3. ✓ `prime_term_eq_nodes_sum`: main bridge (1 sorry for tsum machinery)
4. ✓ `rayleigh_Q_eq_Q`: final Q3.Q identification

## Result

```lean
theorem rayleigh_Q_eq_Q (B t K : ℝ) (M : ℕ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hK : B ≤ K)
    (hP : Continuous (P_A B t)) (hM : 0 < 2 * M + 1) :
    RQ(Toeplitz) − (2M+1)·RQ(T_P_comp) = Q3.Q (fejer_heat_window B t)
```

## Remaining Sorry

`prime_term_eq_nodes_sum`: The tsum→finite_sum conversion requires showing that
for a function vanishing outside a finite set, tsum equals the finite sum.
This is standard Mathlib machinery (`tsum_eq_sum`).
