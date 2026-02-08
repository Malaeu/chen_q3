---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Prime-term certificate @ t_critical (updated with 2026-01-26 output)

Goal: support the single-scale prime bound

```
prime_term(phi_shift_critical B tau) <= arch_term(phi_shift_critical B tau)
```

for the mainline t_critical case, with numerical evidence (tau = 0, B = B_min = 3).

## Method (scripted)

Script: `scripts/prime_term_cert.py`

1) **Exact finite sum (prime powers)** up to `N = 1_000_000`:

```
prime_sum = Sum_{p^k <= N} 2 log p / sqrt(p^k) * phi_shift_critical(xi_{p^k})
```

2) **Tail bound** for `n > N` using only:

- `Lambda(n) <= log n`
- `phi_shift_critical(xi) <= exp(-t_critical * (log n)^2)` (since Fejer <= 1)

So

```
Sum_{n>N} 2 log n / sqrt(n) * exp(-t (log n)^2)
  <= integral_{N..inf} 2 log x / sqrt(x) * exp(-t (log x)^2) dx
```

After substitution `x = e^u`, the integral becomes

```
integral_{u0..inf} 2 u * exp(-t u^2 + u/2) du,  u0 = log N.
```

3) **Arch term** by numerical integration (mpmath):

```
arch_term = integral_{-B..B} a_star(xi) * phi_shift_critical(xi) dxi
```

`a_star(xi) = 2*pi * (log pi - Re(digamma(1/4 + i*pi*xi)))`.

## Results (from output/prime_cert_tcritical_2026-01-26_0046.txt)

- `B_min = 3`, `t_critical = 0.15`, `tau = 0`
- `prime_sum (n<=N)` = **8.7135790788318**
- `tail_bound (n>N)` = **2.783997684e-9**
- `prime_upper_bound` = **8.7135790816158**
- `arch_term (numeric)` = **9.5700363933902**
- `margin (arch - prime_ub)` = **0.8564573117744**

## Lean integration

In `Q3/Proofs/Q_nonneg_t_critical.lean` we wired a placeholder axiom:

```
axiom prime_term_le_at_t_critical_axiom :
  prime_term (phi_shift_critical ...) <= arch_term (phi_shift_critical ...)
```

The constants recorded in the file:

```
prime_cert_N = 1_000_000
prime_cert_prime_ub = 8.714
prime_cert_arch_lb = 9.57
```

These match the script and give a comfortable margin.

Lean now includes certificate axioms for the **B = B_min, τ = 0** case:

```
axiom prime_term_cert_on_Bmin_tau0 :
  prime_term (phi_shift_critical B_min 0) ≤ prime_cert_prime_ub

axiom arch_term_cert_on_Bmin_tau0 :
  prime_cert_arch_lb ≤ arch_term (phi_shift_critical B_min 0)
```

and a lemma:

```
lemma prime_term_le_at_t_critical_Bmin_tau0 :
  prime_term (phi_shift_critical B_min 0) ≤ arch_term (phi_shift_critical B_min 0)
```

`prime_term_le_at_t_critical` now uses the certificate when `(B, τ) = (B_min, 0)`
and falls back to the general axiom otherwise.

## B-range extension (tau = 0)

We also generated a **B-range** certificate on `[B_min, 4.9]`:\n
`docs/insights/prime_cert_brange_tcritical_2026_01_25.md`

`prime_term_le_at_t_critical` now uses this when `τ = 0` and `B ∈ [B_min, 4.9]`,
and falls back to the general axiom outside that range.

## Notes / next tightening

- This cert is for **tau = 0**, **B = B_min**.
- If we need a fully uniform statement in B, tau, we need to extend the bound
  (either monotonicity or a certified sweep over B with Lipschitz control).
- For now this supports the single-scale path and is documented as an axiom.
