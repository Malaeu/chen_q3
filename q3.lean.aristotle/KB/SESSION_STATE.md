---
tags: [proof, axiom, pipeline]
priority: high
last_updated: 2026-02-09
---

# SESSION_STATE

Current chain: Single-scale, t_critical = 3/20, tau = 0, BaseAtomCone (B-range).

Accepted axioms (do NOT close):
- Standard: `propext`, `Classical.choice`, `Quot.sound`
- Weil: `Q3.Weil_criterion_tau0`

Mainline axioms to close (remaining work):
- `Q3.Proofs.PrimeCert.prime_b_grid_arch_bounds_data` in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean`
- `Q3.Proofs.PrimeCert.prime_b_grid_bucket_bounds` in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
- `Q3.Proofs.PrimeCert.prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all` in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000Fallback.lean`

Next expected step:
- Follow `KB/axioms/closure_plan.md` (priority order + success checks).

Checklist (close remaining mainline axioms):
- [ ] Replace `prime_b_grid_arch_bounds_data` with theorem in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean`.
- [ ] Replace `prime_b_grid_bucket_bounds` with theorem in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`.
- [ ] Replace `prime_heat_bounds_arch_data` with theorem in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.
- [ ] Replace `prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all` with theorem in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000Fallback.lean`.
- [ ] Verify: `lake env lean Q3/CheckAxioms.lean` shows only standard + Weil.
- [ ] Verify: `./scripts/check_axioms.sh` clean.
- [ ] Update: `KB/axioms/AXIOM_REGISTRY.md`, `KB/maps/open_lemmas.md`, and add 1 new `KB/insights/YYYY-MM-DD_*.md`.

Last synthesis:
- `KB/insights/2026-02-09_prime_heat_bucket_data_closed_and_chain_rekeyed.md`

Open lemmas list:
- `KB/maps/open_lemmas.md`
