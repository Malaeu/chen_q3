---
tags: [proof, axiom, pipeline]
priority: high
last_updated: 2026-02-08
---

# SESSION_STATE

Current chain: Single-scale, t_critical = 3/20, tau = 0, BaseAtomCone (B-range).

Accepted axioms (do NOT close):
- Standard: `propext`, `Classical.choice`, `Quot.sound`
- Weil: `Q3.Weil_criterion_tau0`

Mainline axioms to close (remaining work):
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data` in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
- `Q3.Proofs.PrimeCert.prime_heat_bucket_data` in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`

Next expected step:
- Follow `KB/axioms/closure_plan.md` (priority order + success checks).

Checklist (close remaining mainline axioms):
- [ ] Replace `prime_b_grid_bounds_data` with theorem in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean`.
- [ ] Replace `prime_heat_bounds_arch_data` with theorem in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.
- [ ] Replace `prime_heat_bucket_data` with theorem in `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`.
- [ ] Verify: `lake env lean Q3/CheckAxioms.lean` shows only standard + Weil.
- [ ] Verify: `./scripts/check_axioms.sh` clean.
- [ ] Update: `KB/axioms/AXIOM_REGISTRY.md`, `KB/maps/open_lemmas.md`, and add 1 new `KB/insights/YYYY-MM-DD_*.md`.

Last synthesis:
- `KB/insights/2026-02-08_kb_refactor_maps_and_scans.md`

Open lemmas list:
- `KB/maps/open_lemmas.md`
