# Q3 holes audit (2026-02-22)

## Scope
- Repo slice: `q3.lean.aristotle/Q3`
- Excluded from active audit:
  - `q3.lean.aristotle/Q3/Archive/**`
  - `q3.lean.aristotle/Q3/Clean/**`
  - `*_debug.lean`
  - `q3.lean.aristotle/Q3/ProofsIntegrated.lean`
  - `q3.lean.aristotle/Q3/Proofs/node_spacing*`
  - `q3.lean.aristotle/Q3/Proofs/off_diag_exp_sum*`
  - `q3.lean.aristotle/Q3/Proofs/PrimeCert/**` (re-included only: `Bmin_1826`, `PrimeCert_Margin_Gate`, `PrimeCert_Margin_PathB`)

## Counts
- Raw marker hits (includes comments/docs lines with words `sorry`/`exact?`/`admit`): 13
- Strict executable holes in active scope (code-level `sorry`/`admit`/`exact?`): 0
- Main critical path strict holes: 0

## Main critical path checked
- `q3.lean.aristotle/Q3/Main.lean`
- `q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean`
- `q3.lean.aristotle/Q3/T5_Transfer.lean`
- `q3.lean.aristotle/Q3/Proofs/RKHS_PrimeCap_Analytic.lean`
- `q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeCert_Margin_PathB.lean`

## Active no-sorry audit run (`-EhasSorry`)
- Script: `q3.lean.aristotle/scripts/audit_nosorry_active_q3.sh`
- Final result: `PASS`
- Files checked: `104`
- Validation mode: each file is checked by
  1. `lake build <Module>`
  2. `lake env lean -EhasSorry <file>`

## Strict executable holes (full list)
None in active scope (`Q3`, excluding `Archive` and `Clean`).

## Raw non-executable marker lines (for cleanup only)
- `q3.lean.aristotle/Q3/AxiomsTheorems.lean:44` (comment with `exact?`)
- `q3.lean.aristotle/Q3/AxiomClosureTheorems.lean:190`
- `q3.lean.aristotle/Q3/AxiomClosureTheorems.lean:192`
- `q3.lean.aristotle/Q3/AxiomClosureTheorems.lean:198`
- `q3.lean.aristotle/Q3/Proofs/A1_density_integrated.lean:114`
- `q3.lean.aristotle/Q3/Proofs/A1_density_integrated.lean:117`
- `q3.lean.aristotle/Q3/Proofs/S_K_small_integrated.lean:90`
- `q3.lean.aristotle/Q3/Proofs/S_K_small_integrated.lean:93`
- `q3.lean.aristotle/Q3/Proofs/RKHS_Contraction_Bridge.lean:18`
- `q3.lean.aristotle/Q3/Proofs/RKHS_Contraction_Bridge.lean:276`
- `q3.lean.aristotle/Q3/Proofs/RKHS_Contraction_Bridge.lean:289`
- `q3.lean.aristotle/Q3/Proofs/A3_Floor_Critical_Goal.lean:14`
- `q3.lean.aristotle/Q3/Proofs/A3_bridge_integrated.lean:115`
- `q3.lean.aristotle/Q3/Proofs/off_diag_exp_sum_integrated.lean:156`

## Axiom note (current main theorem)
- `Q3.Weil_criterion_tau0`: tau=0 specialization of Weil criterion on `Weil_cone_tau0`.
- `Q3.prime_term_le_at_t_critical_axiom`: single-scale placeholder bound for prime_term at t_critical.
- Current `Q3.Main.RH_of_Weil_and_Q3` axioms: `propext`, `Classical.choice`, `Quot.sound`, `Q3.Weil_criterion_tau0`, `Q3.prime_term_le_at_t_critical_axiom`.
- `sorryAx` absent in `#print axioms Q3.Main.RH_of_Weil_and_Q3`.
