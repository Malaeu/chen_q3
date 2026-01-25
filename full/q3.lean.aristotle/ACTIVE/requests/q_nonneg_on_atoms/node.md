# Node: Q_nonneg_on_atoms

## Status
- state: verified
- updated: 2026-01-25

## Source
- request: `../../input/Q_nonneg_on_atoms.md`
- related outputs:
  - `../../output/Q_nonneg_on_atoms_aristotle.lean`
  - `../../output/Q_nonneg_on_atoms_aristotle.lean`
  - `../../output/Q_nonneg_on_atoms_aristotle.lean`
  - `../../output/Q_nonneg_on_atoms_aristotle.lean`

## Why we are here
- This is the mainline statement: Q* >= 0 on base atoms (tau = 0) at t_critical.
- It is the handoff into A1/A2 density/continuity for W_K.

## Evidence / checks
- Main theorem exists in `Q3/Proofs/Q_nonneg_atoms_closure.lean`:
  `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm` (tau = 0, t0_main = t0_critical).
- `Q3/AxiomsTheorems.lean` now wires the theorem:
  `Q_nonneg_on_atoms := QNonnegClosure.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm`.

## Decision
- Wiring is resolved; keep scope strictly BaseAtomCone (tau = 0) and t = t_critical.
