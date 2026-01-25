# FloorCert (t_critical)

Source of truth for the single‑scale floor certificate at `t_critical`.

ASCII map:
```
FloorCert/
  Defs.lean         -- numeric constants (N, h, L_ub, min_lb)
  Grid_2219.lean     -- grid values + grid axioms (2026‑01‑25 22:19)
  Lipschitz_2219.lean-- Lipschitz axiom (from same cert run)
```

Regenerate grid table (use the exact output file to keep the numbers stable):
```
scripts/floor_grid_to_lean.py \
  --input full/q3.lean.aristotle/output/floor_grid_tcritical_2026-01-25_2219.txt \
  --output full/q3.lean.aristotle/Q3/Proofs/FloorCert/Grid_2219.lean \
  --digits 18
```

Primary evidence file:
- `full/q3.lean.aristotle/output/floor_cert_tcritical_2026-01-25_2219.txt`
- `full/q3.lean.aristotle/output/floor_grid_tcritical_2026-01-25_2219.txt`

Integration point:
- `full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean`
