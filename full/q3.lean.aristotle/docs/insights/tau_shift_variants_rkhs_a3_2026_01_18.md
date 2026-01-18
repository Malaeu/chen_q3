# Tau-shift: variants for prime cap and A3 floor

Context
- Goal: close tau-general case in `Q_nonneg_atoms_proof.lean`.
- Current state: shift layer + Rayleigh wrappers are in place; two blockers remain:
  1) prime cap (RKHS/trace) for shifted window,
  2) tau-compatibility of A3 floor (Toeplitz lower bound).

This note records three variants for the prime cap/A3 floor coupling, with trade-offs and dependencies.

---

## Variant 1: Coarse `rho_oneK` (fast, formal, but weak)

Idea
- Keep the existing `rho_one` chain intact and introduce a K-dependent bound for the shift:
  `rho_oneK K := exp(8*pi^2*t_rkhs_cap*K^2) * rho_one`.
- Use a cheap exponential inequality to bound the shifted window by the unshifted Gaussian.

Implementation sketch
- In `Q3/Proofs/RKHS_cap_rayleigh.lean`:
  - `exp_shift_le_exp_mul` (shifted Gaussian bound),
  - `weight_term_shift_le_pow_inv`,
  - `weight_sum_le_rho_oneK`,
  - `prime_rayleigh_shift_le_rho_oneK`.
- This gives the tau-cap on `(2M+1) * RQ(T_P_comp_real_shift)` at `basis0`.

Pros
- Fast to implement; no new mathlib or Proshka requests.
- Minimal surface area: does not break existing `rho_one` uses.

Cons / risk
- The factor `exp(8*pi^2*t_rkhs_cap*K^2)` can explode, which may kill the inequality
  `c_star/4 - rho_oneK K > 0` unless K is small or chosen carefully.

When to use
- Short-term unblocker to finish `Q_nonneg_atoms_proof.lean` plumbing.
- Acceptable if K is small or if a later pass will tighten the cap.

---

## Variant 2: Text-accurate cap (Lemma 9.25 style)

Idea
- Implement the manuscript cap:
  `||T_P|| <= exp(pi*K) * (rho(t) + 2*pi*K*sigma(t))` (up to exact constants).
- This is shift-robust by design and keeps the K-dependence controlled.

Dependencies
- Define `rho(t)` and `sigma(t)` in Lean (not currently present).
- Prove the prime sum domination (likely needs a Proshka pass).

Pros
- Matches the text and is numerically far better than Variant 1.
- The `exp(pi*K)` factor is much milder than the `exp(K^2)` from Variant 1.

Cons
- Requires new definitions + proofs; may need Aristotle/Proshka iteration.

When to use
- If Variant 1 fails the numeric inequality (cap too big).
- If we need a stable K-range without freezing K globally.

---

## Variant 3: General PSD/trace cap (all vectors v)

Idea
- Prove a general inequality: for PSD `A`, `RQ(A, v) <= trace(A)`.
- Compute `trace(T_P_comp_real_shift)` directly as the weight sum.

Pros
- Architecture-clean: provides a cap for any vector `v` (not just `basis0`).
- Aligns well with the linear-algebra structure.

Cons
- Slightly more algebra in Lean (PSD, trace, etc.).
- Still needs a good bound on the shifted weight sum (so may combine with Variant 1 or 2).

When to use
- If later steps require caps for non-basis vectors or operator norm proofs.

---

## Decision (current)

We proceed with Variant 1 first to unblock `Q_nonneg_atoms_proof.lean`.
- Track the risk: check `c_star/4 - rho_oneK K > 0` for the relevant K.
- If it fails, move to Variant 2 (text-accurate cap) rather than hacking constants.

## Sanity check (rho_oneK vs c_star/4)

Using `c_star = 11/10`, `rho_one = 1/25`, `t_rkhs_cap = 40`:

```
rho_oneK K = exp(8*pi^2*t_rkhs_cap*K^2) * rho_one
```

Quick numeric check:
- K = 1.0   -> overflow (rho_oneK enormous), definitely fails.
- K = 0.1   -> c*/4 - rho_oneK < 0
- K = 0.05  -> c*/4 - rho_oneK < 0
- K = 0.02  -> c*/4 - rho_oneK > 0

Conclusion: Variant 1 only stays positive for very small K (roughly K ≤ 0.02).

Related files
- `Q3/Proofs/ShiftedWindows.lean`
- `Q3/Proofs/Rayleigh_Q_identification.lean`
- `Q3/Proofs/RKHS_cap_rayleigh.lean`
- `Q3/Proofs/Q_nonneg_atoms_proof.lean`
