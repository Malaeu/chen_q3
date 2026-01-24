# Implementation Plan

Status: in progress

## Tasks (single-scale mainline)

### A) `SingleScale.continuous_P_A_shift` (tau = 0)

- [ ] Prove continuity lemma for `P_A_shift` at single scale
  - Target files: `full/q3.lean.aristotle/Q3/Proofs/ShiftedWindows.lean`,
    `full/q3.lean.aristotle/Q3/Proofs/P_A_Properties.lean`
  - Notes: derive from continuity of `fejer_heat_window` and shift; reuse
    any existing `P_A_continuous_of_t` or related lemmas.
  - Verification: `lake env lean Q3/Proofs/ShiftedWindows.lean`

- [ ] Wire `SingleScale.continuous_P_A_shift` by replacing axiom
  - Target file: `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`
  - Verification: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`

### B) `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` (tau = 0)

- [ ] Create single-scale Rayleigh basis0 lemma at `t_critical`
  - Target files: `full/q3.lean.aristotle/Q3/Proofs/Rayleigh_basis0_of_A3.lean`,
    `full/q3.lean.aristotle/Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`
  - Notes: use single-scale `P_A` floor at `t_critical` with tau = 0.
  - Verification: `lake env lean Q3/Proofs/Rayleigh_basis0_of_A3.lean`

- [ ] Wire `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` by replacing axiom
  - Target file: `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`
  - Verification: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`

### C) `SingleScale.rho_oneK_tcritical_le_cstar_quarter` (closed)

- [x] Replace with direct numeric bound `rho_one ≤ c_star/4` (tau = 0 mainline)
  - Target file: `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`

## Notes

- One task per run (Ralph loop build mode).
- Update this plan after each task, then commit.
