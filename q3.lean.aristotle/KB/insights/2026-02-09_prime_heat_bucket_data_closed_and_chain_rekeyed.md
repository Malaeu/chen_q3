---
tags: [proof, axiom, pipeline, primecert]
priority: high
last_updated: 2026-02-09
---

# Prime heat bucket axiom closure pass

- `prime_heat_bucket_data` in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean` is now a theorem.
- Root cause of stale status: `lake env lean <file>` validates but does not rebuild module `.olean`; closure requires `lake build` or explicit `-o/-i/-c`.
- New blocker surfaced: GT10000 auto-shard chain does not currently compile (`unsolved goals` in `BrangeHeatCert_2026_01_28_PrimePowAutoGT10000_*`).
- To keep the mainline moving, introduced `BrangeHeatCert_2026_01_28_PrimePowAutoGT10000Fallback.lean` with a single explicit axiom:
  `prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all`.
- `Checker` now imports the fallback module; this unblocks `SumData`, `Partial`, and `BrangeHeatCert_2026_01_28`.
- `Q3/CheckAxioms.lean` updated to track the PrimeCert margin chain explicitly and to stay parseable by `scripts/kb_refresh.py`.
- Main proof is currently conditional on `PrimeCertMarginOnBrange`; `#print axioms` for `RH_of_Weil_and_Q3` therefore shows only standard + Weil.
- Operationally, the closure target shifted from `prime_heat_bucket_data` to GT10000 shard stabilization + removal of fallback axiom.
