# Chain Status (single-scale t_critical)

**Purpose:** Canonical, minimal chain summary for the current mainline.  
**Current status:** Use `Q3/CheckAxioms.lean` as the authoritative dependency list.  
**Next action:** Close the two main-chain Q3 axioms listed in `ACTIVE/MAIN_CHAIN_DEPS.md`.  
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

- `Q3.Proofs.PrimeCert.prime_cert_margin_on_Brange_axiom`
- `Q3.prime_term_le_at_t_critical_axiom`

Authoritative check:
```bash
lake env lean Q3/CheckAxioms.lean
```

## Legacy (not in the current main chain)

The older SingleScale axioms list is **legacy** and no longer load-bearing in
`Q3/Main.lean`. Keep it only for reference/archival:

- `SingleScale.continuous_P_A_shift`
- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
- `SingleScale.rho_oneK_tcritical_le_cstar_quarter`

See `ACTIVE/legacy_two_scale_index.md` for legacy context.

## Related entry points

- `ACTIVE/orchestrator.md` (status, next steps)
- `ACTIVE/MAIN_CHAIN_DEPS.md` (authoritative deps)
- `ACTIVE/insights.md` (running synthesis notes)
