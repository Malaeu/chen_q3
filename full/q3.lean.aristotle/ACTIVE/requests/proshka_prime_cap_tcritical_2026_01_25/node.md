# Node: proshka_prime_cap_tcritical_2026_01_25

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/proshka_prime_cap_tcritical_2026_01_25.md`

## Why we are here
- `prime_term_le_at_t_critical` is still `sorry` in `Q3/Proofs/Q_nonneg_t_critical.lean`.
- This is the remaining **prime cap** piece for the single-scale chain.

## Evidence / checks
- `Q_phi_shift_nonneg_t_critical` depends directly on this lemma.
- We already closed `Fejer_heat_atom_eq_phi_shifts` and `Q_nonneg_on_base_atoms_at_t_critical`.

## Decision
- Ask Proshka for a Lean-ready proof or minimal lemma decomposition.
- Single-scale only, no two-scale bridge.
