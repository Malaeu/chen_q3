# Floor certificate (t_critical, B_min) — 2026‑01‑25

**Goal:** certify `P_A(B_min, t_critical, θ) ≥ c_star` on `θ ∈ [-1/2, 1/2]`.

**Method:** grid + Lipschitz margin.
- Compute `min_grid = min_{θ_i} P_A(θ_i)` on a uniform grid `θ_i`.
- Compute a Lipschitz bound `L ≈ sup_θ 2π Σ |g'(θ+m)|` on the same grid.
- Certificate: `min_grid − L*h/2 ≥ c_star` where `h` is grid spacing.

**Parameters used:**
- `B_min = 3`
- `t_critical = 3/20 = 0.15`
- `N = 4000` (grid on `[-1/2, 1/2]`), `h = 1/4000`
- Precision: 80 digits (mpmath)

**Result (numerical):**
- `min_grid ≈ 1.66223919518145`
- `L ≈ 179.77149229567`
- `L_ub = 249.3` (conservative cap used in Lean)
- `L_ub*h/2 = 0.0311625`
- `min_grid − L_ub*h/2 ≈ 1.63107669518145`
- `c_star = 11/10 = 1.1`
- **margin ≈ 0.53108**

**Artifacts:**
- Script: `scripts/pa_floor_cert.py`
- Output: `output/floor_cert_tcritical_2026-01-26_0100.txt`
- Lipschitz check: `output/lipschitz_cert_tcritical_2026-01-26_0100.txt`

**Lean integration plan:**
- Use conservative rational bounds: `min_grid ≥ 83/50`, `L ≤ 2493/10`, `h = 1/4000`.
- Then `83/50 − (2493/10)*(1/4000)/2 = 65243/40000 = 1.631075 > 1.1`.
- The remaining formal step is to connect these bounds to a formal lemma
  `∀ θ ∈ Icc (-1/2) (1/2), P_A B_min t_critical θ ≥ 83/50`.
