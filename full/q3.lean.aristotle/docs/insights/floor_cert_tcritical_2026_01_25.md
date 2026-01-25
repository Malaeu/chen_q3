# Floor certificate @ t_critical (2026-01-25)

Goal: show the P_A floor at t_critical on Icc[-1/2, 1/2].

```
forall theta in Icc(-1/2, 1/2), c_star <= P_A(B_min, t_critical, theta)
```

## Method (grid + Lipschitz)

Script: `scripts/pa_floor_cert.py`

- Grid on Icc(-1/2, 1/2) with step h = 1/4000
- Lipschitz bound L <= 180
- Min grid value >= 1.66
- Certificate: min_grid - L*h/2 >= 1.6375 > c_star (1.1)

## Results (from output/floor_cert_tcritical_2026-01-25_1615.txt)

- min P_A approx = 1.662239195
- L approx = 179.771492
- h = 1/4000
- margin >= 1.6375

## Lean integration

In `Q3/Proofs/Q_nonneg_t_critical.lean`:

- `floor_cert_min_lb = 83/50`
- `floor_cert_L_ub = 180`
- `floor_cert_h = 1/4000`
- `P_A_floor_cert_on_Icc_axiom` records the certificate
- `P_A_ge_c_star_at_t_critical` follows by periodicity

This is currently documented as an axiom-backed certificate.
