---
tags: [proof, pipeline]
priority: high
last_updated: 2026-02-08
---

# LaTeX → Lean Map (Primary)

Purpose: fast routing from LaTeX sections to Lean files (status + proofs).
This map is optimized for “find the right lemma fast”, not for completeness.

## Root entry
- LaTeX root: `full/RH_Q3.tex`
- Lean root: `q3.lean.aristotle/Q3/`

## Key Labels → Lean (τ=0 mainline)

- `sections/Weil_linkage.tex#thm:Weil-criterion` → `Q3.Weil_criterion_tau0` (accepted axiom) in `q3.lean.aristotle/Q3/Axioms.lean`
- `sections/Weil_linkage.tex#thm:RH` → `Q3.Main.RH_of_Weil_and_Q3` in `q3.lean.aristotle/Q3/Main.lean`
- `sections/Main_closure.tex#thm:Main-positivity` → `Q3.Main.Q_nonneg_on_Weil_cone_tau0` in `q3.lean.aristotle/Q3/Main.lean`
- `sections/T5/lemmas.tex#t5:thm:T5-transfer` → `Q3.T5.T5_transfer` / `Q3.T5.T5_transfer_tau0` in `q3.lean.aristotle/Q3/T5_Transfer.lean`
- `sections/A2.tex#cor:A2-Lip` (also `a2:cor:explicit-lip`) → `Q3.Proofs.Q_Lipschitz_on_W_K_thm` in `q3.lean.aristotle/Q3/Proofs/Q_Lipschitz.lean`
- `sections/A2.tex#lem:Q-local-finite` → `Q3.Proofs.W_sum_BridgeV3.W_sum_finite_Q3` in `q3.lean.aristotle/Q3/Proofs/W_Sum_Finite_Bridge.lean`
- `sections/A1prime.tex#a1:thm:A1-local-density` → `Q3.Theorems.A1_density_WK` in `q3.lean.aristotle/Q3/AxiomsTheorems.lean`
- `sections/A1prime.tex#a1:thm:A1-local-density` (proof) → `Q3.Proofs.A1prime.A1_density_WK_fixed_t0` in `q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean`
- `sections/A3/symbol_floor.tex#lem:uniform-arch-floor` → `Q3.P_A_ge_c_star_at_t_critical` in `q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean`
- `sections/A3/rayleigh_bridge.tex#thm:a3-rayleigh-identification` → `Q3.Theorems.A3_bridge_rayleigh_Fourier` in `q3.lean.aristotle/Q3/AxiomsTheorems.lean`
- `sections/RKHS/main.tex#rkhs:thm:rkhs-contraction` → `Q3.Proofs.SingleScale.rkhs_contraction_data_of_tcritical` in `q3.lean.aristotle/Q3/AxiomsTheorems.lean`

## Sections (ordered as in RH_Q3.tex)

### `sections/abstract.tex`, `sections/introduction.tex`, `sections/scope_notation.tex`
- Lean: overview only; no direct proof artifacts.

### `sections/Notation/qstar_contract.tex`
- Lean: `q3.lean.aristotle/Q3/Basic/Defs.lean`
- Notes: Q, Weil cone, core definitions; see also `Q_STAR_DEFINITIONS.md`.

### `sections/T0.tex`, `sections/T0_AD_fix.tex`
- Lean: `q3.lean.aristotle/Q3/Main.lean` (T0 normalization), `q3.lean.aristotle/Q3/Basic/Defs.lean`
- Key Lean: `Q3.Main.T0_normalization`
- Legacy proof scaffolds: `q3.lean.aristotle/Q3/Archive/01_T0_aristotle.lean`

### `sections/A1prime.tex`
- Lean: `q3.lean.aristotle/Q3/Proofs/A1prime/A1_density_fixed_t0.lean`
- Support: `q3.lean.aristotle/Q3/Proofs/A1prime/HeatError.lean`, `HatInterpBounded.lean`
- Main density wrapper: `q3.lean.aristotle/Q3/Proofs/A1_density.lean`
- Key Lean: `Q3.Theorems.A1_density_WK` (wired theorem) / `Q3.Proofs.A1prime.A1_density_WK_fixed_t0` (proof)

### `sections/A2.tex`
- Lean: `q3.lean.aristotle/Q3/A2_Lipschitz.lean`, `q3.lean.aristotle/Q3/Proofs/Q_Lipschitz.lean`
- Bridge: `q3.lean.aristotle/Q3/Proofs/Q_Lipschitz_arch_bridge.lean`
- Key Lean: `Q3.Proofs.Q_Lipschitz_on_W_K_thm` (used by `Q3.Main.A2_Lipschitz`)

### `sections/A3/*`
- Calibration/arch/bridges: `q3.lean.aristotle/Q3/Proofs/A3_bridge*.lean`
- Floor structure: `q3.lean.aristotle/Q3/Proofs/A3_Floor_Main.lean`, `A3_Floor_Bounds.lean`, `A3_Floor_Critical_Proof.lean`
- Rayleigh bridge: `q3.lean.aristotle/Q3/Proofs/A3_bridge_rayleigh_first.lean`, `Rayleigh_basis0_of_A3.lean`
- Base atom positivity: `q3.lean.aristotle/Q3/Proofs/Q_nonneg_base_atoms.lean`
- Key Lean: `Q3.P_A_ge_c_star_at_t_critical` (arch floor), `Q3.Theorems.A3_bridge_rayleigh_Fourier` (Rayleigh identification)

### `sections/RKHS/*`
- Lean: `q3.lean.aristotle/Q3/Proofs/RKHS_contraction.lean`, `RKHS_Contraction_Bridge.lean`
- Auxiliary: `RKHS_cap_generic.lean`, `RKHS_cap_rayleigh.lean`, `RKHS_hA_prime.lean`, `RKHS_rescaling.lean`
- Key Lean: `Q3.Proofs.SingleScale.rkhs_contraction_data_of_tcritical` (mainline wiring)

### `sections/D3/*`
- Lean: `q3.lean.aristotle/Q3/Proofs/Bridge.lean` (operator/Toeplitz bridges)
- Related: `q3.lean.aristotle/Q3/Proofs/A3_Bridge_Uniform.lean`

### `sections/Weil_linkage.tex`, `sections/Weil_pack.tex`
- Lean: `q3.lean.aristotle/Q3/Main.lean`, `q3.lean.aristotle/Q3/MainTheorems.lean`
- Core axiom: `q3.lean.aristotle/Q3/Axioms.lean` (`Weil_criterion_tau0`)
- Key Lean: `Q3.Main.RH_of_Weil_and_Q3`

### `sections/Main_closure.tex`
- Lean: `q3.lean.aristotle/Q3/Main.lean`, `q3.lean.aristotle/Q3/T5_Transfer.lean`
- Key Lean: `Q3.Main.Q_nonneg_on_Weil_cone_tau0`

### `sections/T5/*`
- Lean: `q3.lean.aristotle/Q3/T5_Transfer.lean`
- Support: `q3.lean.aristotle/Q3/Proofs/T5_*` (if added later)
- Key Lean: `Q3.T5.T5_transfer_tau0` (τ=0 transfer used in main chain)

### `sections/IND_AB/*`
- Lean: PrimeCert data + bounds
  - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean`
  - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28*.lean`
  - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`
- Key Lean (remaining axioms): `prime_b_grid_bounds_data`, `prime_heat_bounds_arch_data`, `prime_heat_bucket_data` (see `KB/maps/open_lemmas.md`)

### Appendices (`full/appendix/*`)
- Lean: diagnostics + computations in `q3.lean.aristotle/Q3/Proofs/*` and `q3.lean.aristotle/Q3/DigammaRemainder.lean`.

## TODO
- Extend label → lemma mapping for PrimeCert (grid + heat) once the last 3 axioms are closed.
