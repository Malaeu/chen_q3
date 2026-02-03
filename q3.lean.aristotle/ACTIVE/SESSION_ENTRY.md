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
- Added sums-only pilot data `BrangeHeatCert_2026_01_28_PrimePowPilotSums.lean` and
  proved pilot bounds for buckets 0/99 in `BrangeHeatCert_2026_01_28_Pilot.lean`
  without `native_decide`.
- Extended `scripts/prime_brange_heat_pp_interval_checker.py` with `--buckets` and
  `--subnamespace`; generated full per-term pilot data
  `BrangeHeatCert_2026_01_28_PrimePowPilot.lean` (not compiled yet; heavy).
- Split the pilot per-term table into base + bucket lookup files:
  `BrangeHeatCert_2026_01_28_PrimePowPilotBase.lean`,
  `BrangeHeatCert_2026_01_28_PrimePowPilotBucket0.lean`,
  `BrangeHeatCert_2026_01_28_PrimePowPilotBucket99.lean`,
  with `BrangeHeatCert_2026_01_28_PrimePowPilot.lean` as the small dispatcher.
- Rewired `BrangeHeatCert_2026_01_28_Pilot.lean` to use per-term pilot data
  (prime-power filter + pointwise axiom), replacing sums-only bounds.
- Verified: `lake build` for BucketDefs + PrimePowPilotSums; `lake env lean` for Pilot.

Open blockers (main chain axioms):
- `Q3.Weil_criterion_tau0`
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_data`
- Standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

Last check (2026-02-03):
- `lake build` for BucketDefs + PrimePowPilotSums; `lake env lean` for Pilot.
- `./scripts/check_axioms.sh` not re-run after the pilot refactor.
- `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowPilotBase`
  succeeds; builds for pilot bucket files still time out (>10 min).

Next steps:
1) Decide whether to keep the sums-only pilot or wire the per-term pilot table
   (`BrangeHeatCert_2026_01_28_PrimePowPilot.lean`) with a fast checker.
2) Scale prime-heat buckets from pilot to 20 buckets, then full 100.
3) Prime-grid buckets: close `prime_b_grid_bucket_bounds`
   (see `docs/INSIGHTS.md` 2026-02-01).
4) Re-run `./scripts/check_axioms.sh` and refresh stats/graphs after each closure.

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
