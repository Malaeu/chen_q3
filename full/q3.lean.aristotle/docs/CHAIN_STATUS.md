# Chain Status (single-scale t_critical)

This file is the canonical, minimal chain summary for the current mainline.
It is intended to stay aligned with the code after each refactor.

## Mainline parameters

- Use single-scale t_critical = 3/20.
- Use the base-atom cone with tau = 0 (even functions only).
- Avoid the old two-scale chain (t_sym vs t_rkhs_cap) in the mainline.

## Current chain (code-level)

1) A3 floor (archimedean lower bound)
- Target: Rayleigh lower bound at t_critical for P_A_shift (tau = 0).
- Status: axiomatized as
  `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
  in `Q3/Proofs/SingleScale_Assumptions.lean`.

2) RKHS prime cap
- Implemented in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
- Includes C1 compression identity (basisFun and dictionary embedding) and
  RKHS cap wiring at t_rkhs_cap.

3) Prime cap (tau = 0)
- Single-scale numeric cap is now `rho_one ≤ c_star/4`
  (`SingleScale.rho_oneK_tcritical_le_cstar_quarter`, closed).

4) Continuity (A2-style) at t_critical (tau = 0)
- Status: axiomatized as
  `SingleScale.continuous_P_A_shift` in
  `Q3/Proofs/SingleScale_Assumptions.lean`.

5) Atom-level nonnegativity and closure
- `Q3/Proofs/Q_nonneg_atoms_closure.lean` closes the fixed-t chain assuming
  the two SingleScale axioms above.

## Remaining SingleScale axioms (open)

- `SingleScale.continuous_P_A_shift`
- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`

## Related entry points

- `PROJECT_ORCHESTRATOR.md` (status, next steps)
- `PHILOSOPHY_OF_PROOF.md` (axiom policy)
- `docs/INSIGHTS.md` (running synthesis notes)
