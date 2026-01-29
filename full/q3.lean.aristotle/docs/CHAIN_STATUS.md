# Chain Status (single-scale t_critical)

**Purpose:** Canonical, minimal chain summary for the current mainline.  
**Current status:** Use `Q3/CheckAxioms.lean` as the authoritative dependency list.  
**Next action:** Close the two main-chain Q3 data axioms listed in `ACTIVE/MAIN_CHAIN_DEPS.md`.  
**Decision (2026-01-29):** Option A selected — keep cert‑data axioms (hash‑checked) and move on.
**Links:** `ACTIVE/MAIN_CHAIN_DEPS.md` · `Q3/CheckAxioms.lean` · `ACTIVE/orchestrator.md`

---

This file is the canonical, minimal chain summary for the current mainline.
It is intended to stay aligned with the code after each refactor.

## Mainline parameters

- Use single-scale t_critical = 3/20.
- Use the base-atom cone with tau = 0 (even functions only).
- Avoid the old two-scale chain (t_sym vs t_rkhs_cap) in the mainline.

## Current chain (code-level)

1) A3 floor (archimedean lower bound)
- Target: Rayleigh lower bound at t_critical for P_A_shift.
- Status: axiomatized as
  `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
  in `Q3/Proofs/SingleScale_Assumptions.lean`.

2) RKHS prime cap
- Implemented in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
- Includes C1 compression identity (basisFun and dictionary embedding) and
  RKHS cap wiring at t_rkhs_cap.

3) Prime sum cap at t_critical
- Theorem `prime_sum_phi_shift_le_cstar_quarter` (proved) in
  `Q3/Proofs/SingleScale_Assumptions.lean`.
- Uses the t-bridge `exp_tcrit_to_rkhs` from
  `Q3/Proofs/PrimeTerm_t_bridge.lean` and the numeric axiom
  `SingleScale.rho_oneK_tcritical_le_cstar_quarter`.

## Main-chain blockers (authoritative)

These are the only Q3-specific axioms blocking the **current** main chain:

- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_data`

Authoritative check:
```bash
lake env lean Q3/CheckAxioms.lean
```

Off-chain / legacy (not in `#print axioms Q3.Main.RH_of_Weil_and_Q3`):
- `Q3.prime_term_le_at_t_critical_axiom` (τ ≠ 0 path placeholder)

## Note on Tier-1 axioms

The authoritative `#print axioms Q3.Main.RH_of_Weil_and_Q3` output currently includes
`Q3.Weil_criterion_tau0` (τ = 0 mainline). It does **not** include `Q3.Schur_test`,
even though `Q3/CheckAxioms.lean` still `#check`s that constant exists.

## Legacy (not in the current main chain)

The older SingleScale axioms list is **legacy** and no longer load-bearing in
`Q3/Main.lean`. Keep it only for reference/archival:

- `SingleScale.continuous_P_A_shift`
- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
- `SingleScale.rho_oneK_tcritical_le_cstar_quarter`

See `ACTIVE/refs/legacy_two_scale_index.md` for legacy context.

## Related entry points

- `ACTIVE/orchestrator.md` (status, next steps)
- `ACTIVE/MAIN_CHAIN_DEPS.md` (authoritative deps)
- `ACTIVE/insights.md` (running synthesis notes)
