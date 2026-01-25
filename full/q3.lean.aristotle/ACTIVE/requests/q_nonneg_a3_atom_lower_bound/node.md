# Node: Q_nonneg_A3_atom_lower_bound

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/Q_nonneg_A3_atom_lower_bound.md`
- related outputs: (none linked)

## Why we are here
- This is the A3 lower-bound step for atoms: combine arch floor and prime cap to show Q* >= 0 on base atoms.
- It is the first place where the single-scale chain actually yields a sign result.

## Evidence / checks
- Request file exists; check `Q3/Proofs/Q_nonneg_atoms_helpers.lean` and `Q3/Proofs/Q_nonneg_atoms_closure.lean` for the current wiring.
- Depends on `rayleigh_basis0_shift_ge_cstar_quarter` and `rho_oneK_tcritical_le_cstar_quarter`.

## Decision
- After floor + Rayleigh + rho are closed, wire this lemma with tau = 0 only.
- Keep it as a short glue lemma (no new analysis).
