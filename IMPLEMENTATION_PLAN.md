# Implementation Plan

Status: in progress

## Tasks (single-scale mainline)

- [ ] Close `SingleScale.continuous_P_A_shift` (continuity of `P_A_shift` at t_critical)
  - Target files: `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`,
    `full/q3.lean.aristotle/Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`
  - Verification: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`

- [ ] Close `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` (A3 Rayleigh lower bound at t_critical)
  - Target files: `full/q3.lean.aristotle/Q3/Proofs/Rayleigh_basis0_of_A3.lean`,
    `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`
  - Verification: `lake env lean Q3/Proofs/Rayleigh_basis0_of_A3.lean`

- [ ] Close `SingleScale.rho_oneK_tcritical_le_cstar_quarter` (RKHS cap at t_critical)
  - Target files: `full/q3.lean.aristotle/Q3/Proofs/RKHS_cap_rayleigh.lean`,
    `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`
  - Verification: `lake env lean Q3/Proofs/RKHS_cap_rayleigh.lean`

## Notes

- One task per run (Ralph loop build mode).
- Update this plan after each task, then commit.
