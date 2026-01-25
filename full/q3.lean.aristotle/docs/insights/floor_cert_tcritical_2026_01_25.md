# Floor certificate at t_critical (2026-01-25)

## Goal
Provide a **grid + Lipschitz** certificate for the pointwise floor on
`P_A B_min t_critical` over `Icc (-1/2) (1/2)`, feeding
`P_A_floor_cert_on_Icc_axiom` in `Q3/Proofs/Q_nonneg_t_critical.lean`.

## Script
- `scripts/floor_cert_tcritical.py`

## Output
- `output/floor_cert_tcritical_2026-01-25_2145.txt`

## Parameters (Lean constants)
- `floor_cert_min_lb = 831/500 = 1.662`
- `floor_cert_L_ub   = 2493/10 = 249.3`
- `floor_cert_h      = 1/4000 = 0.00025`

## Derived margin
`floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 = 1.6308375 > c_star (= 1.1)`

## Notes
- This is a **tau = 0**, single-scale (t_critical) certificate.
- Uses finite grid + finite-difference derivative bound (Lipschitz) with 10% safety factor.
- If tighter margin is needed, decrease `h` or increase precision in the script.
