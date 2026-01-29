# Taint Sources Report (auto) — 2026-01-29 13:21 UTC

**Purpose:** Explain which files are dirty (direct sorries) and which files are tainted via imports.

**Source:** ACTIVE/graphs/TAINT_GRAPH.json + SORRY_FRONTIER.json

## Root dirty files (direct SORRY/BROKEN)

- `Q3/AxiomClosureTheorems.lean` — direct SORRY, sorries: 3 (L190, L192, L198)
- `Q3/Proofs/A1_density_integrated.lean` — direct SORRY, sorries: 2 (L114, L117)
- `Q3/Proofs/A3_Floor_Critical_Goal.lean` — direct SORRY, sorries: 1 (L14)
- `Q3/Proofs/A3_bridge_integrated.lean` — direct SORRY, sorries: 1 (L115)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min.lean` — direct SORRY, sorries: 3 (L202, L223, L245)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min_arch.lean` — direct SORRY, sorries: 1 (L202)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min_arch_step1.lean` — direct SORRY, sorries: 1 (L217)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min_margin.lean` — direct SORRY, sorries: 1 (L245)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min_prime.lean` — direct SORRY, sorries: 1 (L223)
- `Q3/Proofs/Q_nonneg_base_atoms_proof.lean` — direct SORRY, sorries: 4 (L168, L200, L209, L227)
- `Q3/Proofs/RKHS_Contraction_Bridge.lean` — direct SORRY, sorries: 3 (L18, L276, L289)
- `Q3/Proofs/S_K_small_integrated.lean` — direct SORRY, sorries: 2 (L90, L93)
- `Q3/Proofs/off_diag_exp_sum_integrated.lean` — direct SORRY, sorries: 1 (L156)

## DOOMED files (critical propagation)

- `Q3/AxiomClosureTheorems.lean` — direct `SORRY`, prop `SORRY`, roots: `Q3/AxiomClosureTheorems.lean`
- `Q3/CheckAxioms.lean` — direct `VERIFIED`, prop `TAINTED`, roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/Main.lean` — direct `VERIFIED`, prop `TAINTED`, roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/MainTheorems.lean` — direct `VERIFIED`, prop `TAINTED`, roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min.lean` — direct `SORRY`, prop `SORRY`, roots: `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min.lean`
- `Q3/Proofs/Q_nonneg_base_atoms_proof.lean` — direct `SORRY`, prop `SORRY`, roots: `Q3/Proofs/Q_nonneg_base_atoms_proof.lean`
- `Q3/Proofs/RKHS_Contraction_Bridge.lean` — direct `SORRY`, prop `SORRY`, roots: `Q3/Proofs/RKHS_Contraction_Bridge.lean`
- `Q3/ProofsIntegrated.lean` — direct `VERIFIED`, prop `TAINTED`, roots: `Q3/Proofs/A1_density_integrated.lean`, `Q3/Proofs/A3_bridge_integrated.lean`, `Q3/Proofs/S_K_small_integrated.lean`, `Q3/Proofs/off_diag_exp_sum_integrated.lean`
- `Q3/T5_Transfer.lean` — direct `VERIFIED`, prop `TAINTED`, roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`

## TAINTED files (no direct sorries, but import dirty deps)

- `Q3/Atoms_Positive.lean` — roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/AxiomsTheorems.lean` — roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/Proofs/A3_Floor_Critical_Proof.lean` — roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/Proofs/Q_nonneg_atoms_closure.lean` — roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean` — roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/Proofs/SingleScale_Assumptions.lean` — roots: `Q3/Proofs/A3_Floor_Critical_Goal.lean`

