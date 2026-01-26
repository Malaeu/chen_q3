# Prime-term B-range certificate @ t_critical (updated with 2026-01-26 output)

Goal: bound the single-scale prime term for **tau = 0** over **B ∈ [B_min, B_max]**:

```
prime_term(phi_shift_critical B 0) <= arch_term(phi_shift_critical B 0)
```

## Script

`scripts/prime_term_cert_brange.py`

- Grid in **B** with step `h = 0.1` on `[3.0, 4.9]`.
- For each B:
  - exact prime-power sum up to `N = 1_000_000`
  - tail bound using `Lambda(n) <= log n`
  - numeric arch-term via mpmath
- Margin: `arch_term(B) - prime_upper_bound(B)`
- Lipschitz estimate in B from finite differences.

## Output

`output/prime_cert_brange_tcritical_2026-01-26_0050.txt`

Key values:

- `min_margin_grid` = **0.5145928084**
- `L_ub` (finite-diff) = **0.2844034068**
- `margin_lb` = **0.5003726381**

We record a conservative Lean margin **`1/2`**.

## Lean integration

In `Q3/Proofs/Q_nonneg_t_critical.lean`:

```
prime_cert_B_max = 4.9
prime_cert_B_h = 0.1
prime_cert_margin_lb = 1/2
prime_cert_L_ub = 3/10
```

and an axiom:

```
prime_cert_margin_on_Brange_axiom :
  ∀ B ∈ Icc B_min prime_cert_B_max,
    prime_cert_margin_lb ≤ arch_term(phi_shift_critical B 0)
                             - prime_term(phi_shift_critical B 0)
```

This yields:

```
prime_term_le_arch_term_on_Brange_tau0 :
  ∀ B ∈ Icc B_min prime_cert_B_max,
    prime_term(phi_shift_critical B 0) ≤ arch_term(phi_shift_critical B 0)
```

and is used in `prime_term_le_at_t_critical` when `τ = 0` and `B ∈ [B_min, B_max]`.

## Notes

- This is a **single-scale** certificate (t = t_critical, τ = 0).
- If we need full `B`-uniformity, we must extend the B-range or prove monotonicity.
