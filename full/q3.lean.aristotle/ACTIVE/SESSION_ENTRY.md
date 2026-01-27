# Session Entry (2026-01-27)

Purpose: quick resume snapshot for current Q3 single-scale work.

Read order:
1) full/q3.lean.aristotle/ACTIVE/KNOWLEDGE_BASE.md
2) full/q3.lean.aristotle/ACTIVE/requests/INDEX.md
3) full/q3.lean.aristotle/ACTIVE/requests/proshka_floor_cert_tcritical_2026_01_25/node.md

Current mainline decisions:
- Single-scale only: t_critical = 3/20, tau = 0, BaseAtomCone (B-range) only.
- Avoid two-scale t_sym/t_rkhs bridges.
- T_P^{Ray} vs T_P^{RKHS} separated; C1 uses dictionary compression.

Recent wiring changes:
- Q3/AxiomsTheorems.lean: Q_nonneg_on_atoms now uses
  QNonnegClosure.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm.
- A1 density wired via A1prime.A1_density_WK_fixed_t0.
- Q_Lipschitz verified (Q_Lipschitz.lean + bridges).
- RKHS cap verified (RKHS_cap_rayleigh.lean).
- FloorCert: `floor_grid_val_ge_min_lb` closed as a lemma in
  `Q3/Proofs/FloorCert/Grid_2219.lean` (native_decide on the 2219 grid).

New files:
- Q3/Proofs/A3_Floor_Critical_Proof.lean (wrapper for FloorGoal; compiles).
- scripts/update_requests_tree.py (auto link outputs to nodes).
- scripts/fill_requests_tree.py (fill TODO nodes).

Active Proshka request:
- Request:
  full/q3.lean.aristotle/aristotle_input/proshka_floor_cert_tcritical_2026_01_25.md
- Strict prompt:
  full/q3.lean.aristotle/aristotle_input/proshka_floor_cert_tcritical_strict_2026_01_25.md
- Bundle:
  full/q3.lean.aristotle/aristotle_output/proshka_floor_cert_tcritical_bundle_2026_01_25.md

Open blockers (sorry in chain):
- No `sorryAx` in the main chain anymore; remaining blockers are *axioms*.
- Current `#print axioms Q3.Main.RH_of_Weil_and_Q3` includes:
  - `Q3.Weil_criterion_tau0`
  - `Q3.Proofs.PrimeCert.prime_b_grid_val_le_margin`
  - `Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange`
  - plus standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- FloorCert (off-chain): remaining axioms in the floor certificate path:
  - `floor_grid_val_le_P_A` (Q3/Proofs/FloorCert/Grid_2219.lean)
  - `P_A_Lipschitz_on_Icc_cert` (Q3/Proofs/FloorCert/Lipschitz_2219.lean)

Last check (2026-01-27):
- `./scripts/check_axioms.sh` passes (includes `lake build Q3.Main`).
- Axiom list matches: Weil_criterion_tau0 + PrimeCert (2) + standard 3.

Next steps:
1) Keep τ=0 mainline and close PrimeCert axioms formally.
2) Keep documentation + `scripts/check_axioms.sh` in sync with the new axiom list.
3) ✅ DONE: eliminated `native_decide` from PrimeCert tables (no `Lean.trustCompiler` / `Lean.ofReduceBool` in the chain).
