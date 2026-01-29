# Taint Sources Report (auto) — 2026-01-29 13:45 UTC

**Purpose:** Explain which files are dirty (direct sorries) and which files are tainted via imports.

**Source:** ACTIVE/graphs/TAINT_GRAPH.json + SORRY_FRONTIER.json

## Root dirty files (direct SORRY/BROKEN)

- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min.lean` — direct SORRY, sorries: 3 (L202, L223, L245)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min_arch.lean` — direct SORRY, sorries: 1 (L202)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min_arch_step1.lean` — direct SORRY, sorries: 1 (L217)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min_margin.lean` — direct SORRY, sorries: 1 (L245)
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min_prime.lean` — direct SORRY, sorries: 1 (L223)
- `Q3/Proofs/Q_nonneg_base_atoms_proof.lean` — direct SORRY, sorries: 4 (L168, L200, L209, L227)

## DOOMED files (critical propagation)

- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min.lean` — direct `SORRY`, prop `SORRY`, roots: `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof_min.lean`
- `Q3/Proofs/Q_nonneg_base_atoms_proof.lean` — direct `SORRY`, prop `SORRY`, roots: `Q3/Proofs/Q_nonneg_base_atoms_proof.lean`

## TAINTED files (no direct sorries, but import dirty deps)

_None_

