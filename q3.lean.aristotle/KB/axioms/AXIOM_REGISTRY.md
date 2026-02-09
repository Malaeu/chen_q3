---
tags: [axiom, proof]
priority: high
last_updated: 2026-02-09
---

# Axiom Registry (Mainline)

This is the authoritative list of axioms relevant to the current tau=0 main chain.
LaTeX is primary for meaning; Lean is primary for status.

## Core accepted (do NOT close)
| Axiom | Category | Lean file | Status | Notes |
| --- | --- | --- | --- | --- |
| `propext` | standard | Lean core | accepted | Foundational |
| `Classical.choice` | standard | Lean core | accepted | Foundational |
| `Quot.sound` | standard | Lean core | accepted | Foundational |
| `Q3.Weil_criterion_tau0` | Weil | `q3.lean.aristotle/Q3/Axioms.lean` | accepted | Community-standard (Weil 1952) |

## Mainline (must close)
| Axiom | Category | Lean file | Status | Closure path |
| --- | --- | --- | --- | --- |
| `Q3.Proofs.PrimeCert.prime_b_grid_arch_bounds_data` | cert | `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean` | open | Formalize arch-term lower bound at grid nodes |
| `Q3.Proofs.PrimeCert.prime_b_grid_bucket_bounds` | cert | `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean` | open | Formalize bucketed prime-term upper bounds on grid |
| `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` | cert | `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean` | open | Formalize arch integral bound |

## Off-chain / legacy (not in tau=0 main chain)
| Axiom | Lean file | Notes |
| --- | --- | --- |
| `prime_term_le_at_t_critical_axiom` | `q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean` | off-chain (tau != 0) |
| `Q_nonneg_on_BaseAtomCone_axiom` | `q3.lean.aristotle/Q3/Proofs/Q_nonneg_base_atoms.lean` | legacy bridge |

## Update rule
Refresh after `Q3/CheckAxioms.lean` or any PrimeCert certificate update.
