# Q3 Block Map (Lean ↔ Paper blocks)

Short mapping from paper blocks to Lean files/theorems/axioms.
Use this to answer: “Which block is this in Lean?”

## T0 — Normalization (Weil/Q)

- Paper: T0 (Guinand–Weil normalization)
- Lean entry: handled as external/classical pieces; see `Q3/Axioms.lean`
  (`Weil_criterion`, `explicit_formula`) and `ACTIVE/refs/proof_map.md`.
- Status: external; not in the single-scale axiom list

## A1' — Density (atoms in W_K)

- Lean theorem: `Q3.Theorems.A1_density_WK` in `Q3/AxiomsTheorems.lean`
- Source proof: `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`
- Status: wired theorem (not an axiom)

## A2 — Continuity / Lipschitz of Q on W_K

- Lean theorem: `Q3.Theorems.Q_Lipschitz` in `Q3/AxiomsTheorems.lean`
- Source proof: `Q3/Proofs/Q_Lipschitz.lean`
- Status: wired theorem (not an axiom)

## A3 — Archimedean floor + Toeplitz/Rayleigh bridge

Mainline (single-scale, tau = 0):
- **Axiom (open):** `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
  in `Q3/Proofs/SingleScale_Assumptions.lean`
- Context: `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`

Legacy (two-scale / uniform):
- `Q3/Proofs/A3_Floor_Main.lean` (t_sym)
- `Q3/Proofs/P_A_Toeplitz_bridge.lean` (t_sym + t_rkhs_cap)

## RKHS prime cap

- Core cap at t_rkhs_cap:
  - `Q3/Proofs/RKHS_cap_rayleigh.lean`
  - `rho_one = 1/25`, `t_rkhs_cap = 40`

- **Single-scale cap (closed):**
  - `SingleScale.rho_oneK_tcritical_le_cstar_quarter`
  - `Q3/Proofs/SingleScale_Assumptions.lean`

## C1 — Compression identity (Rayleigh ↔ RKHS)

- Implemented in `Q3/Proofs/RKHS_cap_rayleigh.lean`
  - basisFun identity
  - dictionary embedding identity
- Status: proven (no axiom); used as a bridge for opNorm bounds

## Atom-level nonnegativity / closure

- `Q3/Proofs/Q_nonneg_atoms_closure.lean`
  - closes the fixed-t chain assuming the two SingleScale axioms

## Main theorem (RH via Weil criterion)

- Entry: `Q3/Main.lean` (theorem `RH_of_Weil_and_Q3`)
- Axioms left: see `ACTIVE/chain_status.md` or `ACTIVE/orchestrator.md`
