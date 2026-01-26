# Session Entry (2026-01-26)

Purpose: quick resume snapshot for current Q3 single-scale work.

Read order:
1) full/q3.lean.aristotle/ACTIVE/KNOWLEDGE_BASE.md
2) full/q3.lean.aristotle/ACTIVE/requests/INDEX.md
3) full/q3.lean.aristotle/ACTIVE/requests/proshka_floor_cert_tcritical_2026_01_25/node.md

Current mainline decisions:
- Single-scale only: t_critical = 3/20, tau = 0, BaseAtomCone only.
- Avoid two-scale t_sym/t_rkhs bridges.
- T_P^{Ray} vs T_P^{RKHS} separated; C1 uses dictionary compression.

Recent wiring changes:
- Q3/AxiomsTheorems.lean: Q_nonneg_on_atoms now uses
  QNonnegClosure.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm.
- A1 density wired via A1prime.A1_density_WK_fixed_t0.
- Q_Lipschitz verified (Q_Lipschitz.lean + bridges).
- RKHS cap verified (RKHS_cap_rayleigh.lean).

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
  - `Q3.prime_term_le_at_t_critical_axiom`
  - `Q3.Proofs.PrimeCert.prime_b_grid_val_le_margin`
  - `Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange`
  - plus compiler axioms `Lean.ofReduceBool`, `Lean.trustCompiler` (from `native_decide`-style table checks)

Last check:
- `lake build Q3.Main` passes.
- `#print axioms Q3.Main.RH_of_Weil_and_Q3` is consistent with the list above.

Next steps:
1) Decide what we want as “final” axioms for the one‑scale numeric certificates
   (keep explicit certificate axioms vs eliminate via a different encoding).
2) If we keep certificate axioms: document them in `PHILOSOPHY_OF_PROOF.md` and update `scripts/check_axioms.sh`.
3) If we want to eliminate `Lean.trustCompiler`: replace `native_decide` table proofs with kernel-safe proofs (case splits + `norm_num`).
