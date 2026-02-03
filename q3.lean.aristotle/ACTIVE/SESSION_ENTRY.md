# Session Entry (2026-02-03)

Purpose: quick resume snapshot for current Q3 single-scale work.

Read order:
1) full/q3.lean.aristotle/ACTIVE/KNOWLEDGE_BASE.md
2) full/q3.lean.aristotle/ACTIVE/requests/INDEX.md
3) full/q3.lean.aristotle/ACTIVE/requests/proshka_floor_cert_tcritical_2026_01_25/node.md
4) full/q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md

Current mainline decisions:
- Single-scale only: t_critical = 3/20, tau = 0, BaseAtomCone (B-range) only.
- Avoid two-scale t_sym/t_rkhs bridges.
- T_P^{Ray} vs T_P^{RKHS} separated; C1 uses dictionary compression.

Recent changes (2026-02-03):
- Added `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_BucketDefs.lean` to isolate
  bucket/partition lemmas from the heavy prime-power table.
- Rewired `BrangeHeatCert_2026_01_28_Pilot.lean` to use per-term pilot data
  (prime-power filter + pointwise axiom), replacing sums-only bounds.
- Split pilot buckets 0/99 into 4 parts each (faster Lean builds).
- Generated 20-bucket prime-power tables under `namespace Twenty` and split into
  base + per-bucket part files (`BrangeHeatCert_2026_01_28_PrimePowTwenty*`).
- Generated full 100-bucket prime-power tables under `namespace Full` and split into
  base + per-bucket part files (`BrangeHeatCert_2026_01_28_PrimePowFull*`).
- Verified: `lake build` for BucketDefs + PrimePowPilotSums; `lake env lean` for Pilot.


Open blockers (main chain axioms):
- `Q3.Weil_criterion_tau0`
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_data`
- Standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

Last check (2026-02-03):
- `lake build` for BucketDefs + PrimePowPilotSums; `lake env lean` for Pilot.
- `./scripts/check_axioms.sh` not re-run after the pilot refactor.
- `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowTwenty` succeeds.
- `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFull` succeeds.
- `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBase` succeeds.
- All pilot bucket parts (0/99) build; bucket dispatchers + `PrimePowPilot` build.
- `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Pilot.lean` succeeds.

Next steps:
1) Wire `BrangeHeatCert_2026_01_28_PrimePowFull` into the bucket checker and
   replace bucket-sum axioms with per-term bounds (no `native_decide`).
2) Close `prime_heat_bounds_data` using the full bucket pipeline + tail bound.
3) Re-run `./scripts/check_axioms.sh` and refresh stats.

## Branching discipline (2026-01-29)

- We keep `projekt_2A` as the stable baseline.
- Experimental work happens on `projekt_2A-compact-support` only.
- Goal of this branch: push the PrimeCert closure to the end and verify the math.
- Merge back into `projekt_2A` **only if** the chain checks out; otherwise delete the branch.

Status (compact-support branch):
- Localized heat Lipschitz to `Icc (-B_max, B_max)` (no global Integrable/Summable).
- Heat cert data in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Data.lean` and
  derived `prime_heat_bounds_cert` in `BrangeHeatCert_2026_01_28.lean`.
- Analytic heat tail bound (3e-6) in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Tail.lean`;
  `prime_heat_tail_bound` is a theorem (no axiom).
- `prime_margin_Lipschitz_on_Brange` axiom replaced by theorem in
  `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`.
