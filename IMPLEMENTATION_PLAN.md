# Implementation Plan

Status: in progress

## Tasks (single-scale mainline)

### Current critical TODO (single-scale t_critical)

- [ ] **Grid certificate (2 axioms)**  
  - `floor_grid_val_ge_min_lb`  
  - `floor_grid_val_le_P_A`  
  - File: `full/q3.lean.aristotle/Q3/Proofs/FloorCert/Grid_2219.lean`

- [ ] **Lipschitz certificate (1 axiom)**  
  - `P_A_Lipschitz_on_Icc_cert`  
  - File: `full/q3.lean.aristotle/Q3/Proofs/FloorCert/Lipschitz_2219.lean`

- [ ] **Prime certificate (3 axioms)**  
  - `prime_term_cert_on_Bmin_tau0`  
  - `arch_term_cert_on_Bmin_tau0`  
  - `prime_cert_margin_on_Brange_axiom`  
  - Files:  
    `full/q3.lean.aristotle/Q3/Proofs/PrimeCert/Bmin_1826.lean`  
    `full/q3.lean.aristotle/Q3/Proofs/PrimeCert/Brange_2046.lean`

- [ ] **RKHS single-scale contraction (1 axiom)**  
  - `rkhs_contraction_tcritical`  
  - File: `full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean`

### Single-scale bridge targets (dependent on the above)

- [ ] `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
- [ ] `Q_phi_shift_nonneg_t_critical` (from prime + floor cert)

## Notes

- One task per run (Ralph loop build mode).
- Update this plan after each task, then commit.
