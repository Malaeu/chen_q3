# Chain Status (single-scale t_critical)

This file is the canonical, minimal chain summary for the current mainline.
It is intended to stay aligned with the code after each refactor.

## Mainline parameters

- Use single-scale t_critical = 3/20.
- Avoid the old two-scale chain (t_sym vs t_rkhs_cap) in the mainline.

**Important (numerics vs current Lean chain):**
- Numerically, `τ-transfer` fails at `t = t_critical`:
  `python3 verify_variant_b.py --direct` reports `min Q = -911.2678` at `τ = 1.689`
  (so full `AtomCone_K_fixed` is not safe).
- The current Lean main chain still depends on a placeholder axiom
  `Q3.prime_term_le_at_t_critical_axiom` which *acts like* a “τ-uniform prime-term bound”.
  Treat this as a temporary bridge until we refactor the cone / criterion target.

## Current chain (code-level)

1) A3 floor (archimedean lower bound)
- Target: Rayleigh lower bound at t_critical for P_A_shift (tau = 0).
- Status: wired through the one‑scale `t_critical` development (see `Q3/Proofs/Q_nonneg_t_critical.lean`).

2) RKHS prime cap
- Implemented in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
- Includes C1 compression identity (basisFun and dictionary embedding) and
  RKHS cap wiring at t_rkhs_cap.

3) Prime cap (tau = 0)
- Single-scale numeric cap is now `rho_one ≤ c_star/4`
  (`SingleScale.rho_oneK_tcritical_le_cstar_quarter`, closed).

4) Continuity (A2-style) at t_critical (single-scale)
- Status: **closed** via `ShiftedWindows.P_A_shift_continuous`
  (requires `B > 0`, tau arbitrary).

5) Atom-level nonnegativity and closure
- `Q3/Proofs/Q_nonneg_atoms_closure.lean` closes the fixed-t chain assuming
  the one‑scale certificate inputs from `Q3/Proofs/Q_nonneg_t_critical.lean` / `Q3/Proofs/PrimeCert/*`.

## Current axioms in the main theorem (as of 2026-01-26)

From:
```bash
echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin
```

- Standard/kernel: `propext`, `Classical.choice`, `Quot.sound`
- Classical literature: `Q3.Weil_criterion`, `Q3.Schur_test`
- One‑scale numeric certificates (t_critical):  
  `Q3.prime_term_le_at_t_critical_axiom`,  
  `Q3.Proofs.PrimeCert.prime_b_grid_val_le_margin`,  
  `Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange`

## Related entry points

- `PROJECT_ORCHESTRATOR.md` (status, next steps)
- `PHILOSOPHY_OF_PROOF.md` (axiom policy)
- `docs/INSIGHTS.md` (running synthesis notes)
