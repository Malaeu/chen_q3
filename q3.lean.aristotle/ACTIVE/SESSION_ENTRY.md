# Session Entry (2026-02-02)

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

Recent changes (2026-02-02):
- Added bucket scaffold lemma `prime_heat_bucket_sum_le_tail_sum` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean` (prep for heat buckets).
- Added INSIGHTS synthesis for prime-heat bucket bounds (no native_decide).
- Refreshed `FORMALIZATION_STATS.md` + `ACTIVE/graphs/DEPS_TREE_MAIN.*` +
  `ACTIVE/graphs/PROOF_GRAPH.*`.
- `./scripts/check_axioms.sh` passes; main-chain axioms unchanged (3 project + 3 standard).

Open blockers (main chain axioms):
- `Q3.Weil_criterion_tau0`
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_data`
- Standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

Last check (2026-02-02):
- `./scripts/check_axioms.sh` passes (includes `lake build Q3.Main`).
- Axiom list matches: Weil_criterion_tau0 + PrimeCert (2) + standard 3.

Next steps:
1) Prime-heat buckets: close `prime_heat_bucket_bounds` / `prime_heat_bucket_sum_ub`
   (see `docs/INSIGHTS.md` 2026-02-02).
2) Prime-grid buckets: close `prime_b_grid_bucket_bounds`
   (see `docs/INSIGHTS.md` 2026-02-01).
3) Re-run `./scripts/check_axioms.sh` and refresh stats/graphs after each closure.

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
