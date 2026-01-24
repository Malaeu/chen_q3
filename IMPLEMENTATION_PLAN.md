# Implementation Plan

Status: in progress

## Tasks (single-scale mainline)

### A) `SingleScale.continuous_P_A_shift`

- [ ] Prove continuity lemma for `P_A_shift` at single scale
  - Target files: `full/q3.lean.aristotle/Q3/Proofs/ShiftedWindows.lean`,
    `full/q3.lean.aristotle/Q3/Proofs/P_A_Properties.lean`
  - Notes: derive from continuity of `fejer_heat_window` and shift; reuse
    any existing `P_A_continuous_of_t` or related lemmas.
  - Verification: `lake env lean Q3/Proofs/ShiftedWindows.lean`

- [ ] Wire `SingleScale.continuous_P_A_shift` by replacing axiom
  - Target file: `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`
  - Verification: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`

### B) `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`

- [ ] Create single-scale Rayleigh basis0 lemma at `t_critical`
  - Target files: `full/q3.lean.aristotle/Q3/Proofs/Rayleigh_basis0_of_A3.lean`,
    `full/q3.lean.aristotle/Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`
  - Notes: use `P_A_shift_tau_zero` and single-scale `P_A` floor at `t_critical`.
  - Verification: `lake env lean Q3/Proofs/Rayleigh_basis0_of_A3.lean`

- [ ] Wire `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` by replacing axiom
  - Target file: `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`
  - Verification: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`

### C) `SingleScale.rho_oneK_tcritical_le_cstar_quarter`

- [ ] Prove/bridge RKHS cap at `t_critical` (single-scale)
  - Target files: `full/q3.lean.aristotle/Q3/Proofs/RKHS_cap_rayleigh.lean`,
    `full/q3.lean.aristotle/Q3/Proofs/PrimeTerm_t_bridge.lean`
  - Notes: reuse the t-bridge `exp_tcrit_to_rkhs` or add a lemma to show
    `rho_oneK` bound at `t_critical`.
  - Verification: `lake env lean Q3/Proofs/RKHS_cap_rayleigh.lean`

- [ ] Wire `SingleScale.rho_oneK_tcritical_le_cstar_quarter` by replacing axiom
  - Target file: `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`
  - Verification: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`

## Notes

- One task per run (Ralph loop build mode).
- Update this plan after each task, then commit.
