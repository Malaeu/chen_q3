# Floor certificate at t_critical (2026-01-25)

## Goal
Provide a **grid + Lipschitz** certificate for the pointwise floor on
`P_A B_min t_critical` over `Icc (-1/2) (1/2)`, feeding
`P_A_floor_cert_on_Icc_cert` in `Q3/Proofs/Q_nonneg_t_critical.lean`.

## Script
- `scripts/floor_cert_tcritical.py`

## Output
- `output/floor_cert_tcritical_2026-01-25_2219.txt`
- `output/floor_grid_tcritical_2026-01-25_2219.txt` (full grid values)

## Parameters (Lean constants)
- `floor_cert_N      = 4000`
- `floor_cert_min_lb = 831/500 = 1.662`
- `floor_cert_L_ub   = 2493/10 = 249.3`
- `floor_cert_h      = 1/4000 = 0.00025`

## Derived margin
`floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 = 1.6308375 > c_star (= 1.1)`

## Notes
- This is a **tau = 0**, single-scale (t_critical) certificate.
- Grid part: `P_A_floor_cert_on_grid_cert` (lower bounds at grid points).
- Lipschitz part: `P_A_Lipschitz_on_Icc_cert` + `floor_cert_grid_cover_cert`.
- These combine into `P_A_floor_cert_on_Icc_cert`, which feeds `P_A_ge_c_star_at_t_critical`.
