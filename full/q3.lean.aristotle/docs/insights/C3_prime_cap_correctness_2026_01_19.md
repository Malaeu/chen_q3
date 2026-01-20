# C3 Prime Cap Correctness Fix

**Date:** 2026-01-19
**Author:** Claude + Ылша
**Status:** DIAGNOSED, FIX IN PROGRESS

---

## The Bug

The lemma `prime_term_le_rho_one_of_bounded` claimed:

```lean
∀ Φ with |Φ| ≤ 1, |prime_term Φ| ≤ rho_one  -- FALSE!
```

### Why It's Wrong

1. `w_Q(n) = 2·Λ(n)/√n` (von Mangoldt weights)
2. `Nodes K = {n ≥ 2 : xi_n ≤ K}` where `xi_n = log(n)/(2π)`
3. This means `n ≤ e^{2πK}` for nodes in `[-K, K]`
4. Sum of weights: `∑_{n∈Nodes K} |w_Q(n)| ~ O(e^{πK})`
5. But `rho_one = 1/25 = 0.04`

**For K = 1:** The sum of weights is >> 40, not < 0.04!

---

## What `rho_one` Actually Is

The `rho_one = 1/25` bound is on the **operator norm** `‖T_P‖` in the RKHS:

```
‖T_P‖ ≤ ρ(t₀) ≤ 1971/50000 ≈ 0.03942 < 1/25
```

This is a **quadratic form** bound:
```
⟨T_P p, p⟩ ≤ ‖T_P‖ · ‖p‖² ≤ rho_one · ‖p‖²
```

NOT a bound on `∑ |w_Q(n)|`!

---

## The Fix (Option B)

For `phi_shift`, use **window-specific structure**:

```lean
/-- phi_shift has Fejér×heat decay structure -/
phi_shift B t τ ξ = fejer_heat_window B t (ξ - τ)
```

### Proof Strategy

1. **Termwise bound:** For each n ∈ Nodes K:
   ```
   |w_Q(n) * phi_shift(xi_n)| = |w_Q(n) * window(xi_n - τ)|
   ```

2. **Window decay compensates:** The function `fejer_heat_window(x)` decays
   exponentially for |x| large, regardless of shift τ.

3. **Same majorant:** The bound `≤ (4/e) * pow_inv_shift(n-2)` still applies
   because it depends on the decay rate, not the center.

4. **Sum converges:** `∑ pow_inv_shift(n) ≤ rho_one` (proven in RKHS_cap_rayleigh.lean)

---

## Files Changed

- `Q3/Proofs/Q_nonneg_atoms_proof.lean`:
  - Removed false generic lemma `prime_term_le_rho_one_of_bounded`
  - Updated `prime_term_phi_shift_le` with correct approach
  - Added detailed comments explaining the fix

---

## TODO

1. [ ] Prove shifted weight bound: `|w_Q(n) * window(xi_n - τ)| ≤ (4/e) * pow_inv_shift(n-2)`
2. [ ] Adapt `weight_sum_le_rho_one` for shifted windows
3. [ ] Close the sorry in `prime_term_phi_shift_le`

---

## Key Lesson

**The rho_one bound is about operator structure, not raw weight sums!**

When formalizing bounds from papers, verify:
- What mathematical object is being bounded (operator norm vs sum)
- What assumptions are implicit (RKHS membership vs L∞ bound)
- Whether the bound is K-independent or K-dependent
