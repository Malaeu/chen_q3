---
tags: [proof, axiom, pipeline, primecert]
priority: high
last_updated: 2026-02-09
---

# GT10000 fallback removal (PrimeCert heat chain)

- `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean` now imports
  `BrangeHeatCert_2026_01_28_PrimePowAutoGT10000` directly.
- Temporary module
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000Fallback.lean`
  was converted to a compatibility shim and no longer declares an `axiom`.
- `prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all` is now sourced
  from the generated GT10000 theorem chain.
- Bucket0/GT10000 namespace clash resolved by renaming bucket0 constants:
  `pi_lb`, `pi_lb_le_pi`, `pi_lb_pos` -> `pi_lb_bucket0*`.
- Verification pass:
  - `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
  - `lake env lean Q3/CheckAxioms.lean`
  - `./scripts/check_axioms.sh`
- Remaining mainline PrimeCert blockers after this closure:
  `prime_heat_bounds_arch_data`, `prime_b_grid_bucket_bounds`,
  `prime_b_grid_arch_bounds_data`.
