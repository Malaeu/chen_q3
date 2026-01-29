# Prime-term B-range certificate (t_critical, tau = 0) — 2026‑01‑26

**Goal:** certify `margin(B) = arch_term(B) − prime_term(B) ≥ prime_cert_margin_lb`
for all `B ∈ [B_min, B_max]`.

**Method:** grid in `B` + finite-difference Lipschitz margin.
- Precompute prime power contributions once (`N = 1_000_000`).
- For each grid `B = 3.0 + 0.1·i`, compute:
  - `prime_sum`, `prime_ub`, `arch_term`, `margin`.
- Estimate `L_ub` by finite differences on the grid.
- Certificate: `min_margin_grid − L_ub·(B_h/2)`.

**Parameters used:**
- `B_min = 3.0`, `B_max = 4.9`, `B_h = 0.1`
- `t_critical = 0.15`, `tau = 0`
- `N = 1_000_000`

**Result (numerical):**
- `min_margin_grid ≈ 0.514592808436`
- `L_ub (finite-diff) ≈ 0.284403406843`
- `margin_lb ≈ 0.500372638094`

**Artifacts:**
- Script: `scripts/prime_term_cert_brange.py`
- Output: `full/q3.lean.aristotle/output/prime_cert_brange_tcritical_2026-01-26_0050.txt`
- Lean grid: `Q3/Proofs/PrimeCert/BrangeGrid_2046.lean`

**Lean integration plan:**
- Keep conservative constants in `Q3.Proofs.PrimeCert.Defs`:
  - `prime_cert_margin_lb = 499/1000 = 0.499`
  - `prime_cert_L_ub = 3/10 = 0.3`
- Grid table is rounded down to 12 decimals to preserve ≤.
