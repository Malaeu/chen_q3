---
tags: [proof, axiom]
priority: high
last_updated: 2026-02-08
---

# Open Lemmas / Axioms (Mainline)

Source of truth for what remains to close in the **current τ=0 main chain**.
Lean is primary for status; LaTeX is primary for meaning.

## Core accepted axioms (do NOT close)
- `Q3.Weil_criterion_tau0` — `q3.lean.aristotle/Q3/Axioms.lean`
- Standard: `propext`, `Classical.choice`, `Quot.sound`

## Mainline blockers (must close)
| Item | Lean file | LaTeX section | Status | Notes |
| --- | --- | --- | --- | --- |
| `prime_b_grid_bounds_data` | `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean` | `sections/IND_AB/*` | **axiom** | Certificate data for grid bounds (PrimeCert) |
| `prime_heat_bounds_arch_data` | `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean` | `sections/IND_AB/*` | **axiom** | Arch integral bound (split from heat bundle) |
| `prime_heat_bucket_data` | `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean` | `sections/IND_AB/*` | **axiom** | Bucketed prime‑heat partial sums |

## Recently closed (keep track)
| Item | Lean file | Status | Notes |
| --- | --- | --- | --- |
| `prime_margin_Lipschitz_on_Brange` | `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean` | **theorem** | Replaced axiom in Feb 2026 |

## Off‑chain / legacy (not in τ=0 main chain)
| Item | Lean file | Notes |
| --- | --- | --- |
| `prime_term_le_at_t_critical_axiom` | `q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean` | Off‑chain (τ ≠ 0), keep for future |
| `Q_nonneg_on_BaseAtomCone_axiom` | `q3.lean.aristotle/Q3/Proofs/Q_nonneg_base_atoms.lean` | Legacy bridge for τ=0 base‑atom cone |

## Update rule
Refresh after any axiom change or when `Q3/CheckAxioms.lean` changes.
Run: `python3 q3.lean.aristotle/scripts/kb_refresh.py`

<!-- AUTO:SCAN_START -->
## Auto scan (raw)
Generated: 2026-02-08

Format: `<file>` — `axioms=<n>` `holes=<m>` (names/line hints).

- Q3/A2_Lipschitz.lean — axioms=1 holes=0 (axioms: a_star_continuous)
- Q3/Aristotle_Integration.lean — axioms=1 holes=0 (axioms: aristotle_all_proofs_compile)
- Q3/AxiomClosureTheorems.lean — axioms=0 holes=3 (holes at: 190, 192, 198)
- Q3/Proofs/A1_density_integrated.lean — axioms=0 holes=2 (holes at: 114, 117)
- Q3/Proofs/A1_density_main.lean — axioms=0 holes=13 (holes at: 226, 674, 682, 699, 711…)
- Q3/Proofs/A3_Floor_Critical_Goal.lean — axioms=0 holes=1 (holes at: 14)
- Q3/Proofs/A3_bridge_integrated.lean — axioms=0 holes=1 (holes at: 115)
- Q3/Proofs/FloorCert/Grid_2219.lean — axioms=1 holes=0 (axioms: floor_grid_val_le_P_A)
- Q3/Proofs/FloorCert/Lipschitz_2219.lean — axioms=1 holes=0 (axioms: P_A_Lipschitz_on_Icc_cert)
- Q3/Proofs/PrimeCert/Bmin_1826.lean — axioms=2 holes=0 (axioms: arch_term_cert_on_Bmin_tau0, prime_term_cert_on_Bmin_tau0)
- Q3/Proofs/PrimeCert/BrangeCert_2046.lean — axioms=1 holes=0 (axioms: prime_b_grid_bounds_data)
- Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30_Data.lean — axioms=2 holes=0 (axioms: prime_b_grid_pilot_bucket_data_0, prime_b_grid_pilot_bucket_data_19)
- Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean — axioms=2 holes=0 (axioms: prime_b_grid_bucket_bounds, prime_b_grid_bucket_sum_ub)
- Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean — axioms=1 holes=0 (axioms: prime_heat_bounds_arch_data)
- Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean — axioms=1 holes=0 (axioms: prime_heat_weight_term_le_pp_ub_of_prime_pow)
- Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Pilot.lean — axioms=3 holes=0 (axioms: prime_heat_bucket_pp_sum_ub_le_bucket_pilot_0, prime_heat_bucket_pp_sum_ub_le_bucket_pilot_99, prime_heat_weight_term_le_pp_ub_of_prime_pow_pilot)
- Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean — axioms=1 holes=0 (axioms: prime_heat_bucket_data)
- Q3/Proofs/QSpec.lean — axioms=2 holes=0 (axioms: Q_criticalSpec_nonneg, Q_testSpec_negative)
- Q3/Proofs/Q_nonneg_base_atoms.lean — axioms=1 holes=0 (axioms: Q_nonneg_on_BaseAtomCone_axiom)
- Q3/Proofs/Q_nonneg_t_critical.lean — axioms=1 holes=0 (axioms: prime_term_le_at_t_critical_axiom)
- Q3/Proofs/RKHS_Contraction_Bridge.lean — axioms=0 holes=3 (holes at: 18, 276, 289)
- Q3/Proofs/S_K_small_integrated.lean — axioms=0 holes=2 (holes at: 90, 93)
- Q3/Proofs/SingleScale_Assumptions.lean — axioms=1 holes=0 (axioms: rkhs_contraction_tcritical)
- Q3/Proofs/W_sum_finite.lean — axioms=0 holes=3 (holes at: 69, 82, 111)
- Q3/Proofs/off_diag_exp_sum_integrated.lean — axioms=0 holes=1 (holes at: 156)
<!-- AUTO:SCAN_END -->
