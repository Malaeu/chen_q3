# Node: A1_density_ASSEMBLY_ONLY

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/A1_density_ASSEMBLY_ONLY.md`
- related outputs:
  - `../../output/A1_density_ASSEMBLY_ONLY_aristotle.lean`
  - `../../output/A1_density_ASSEMBLY_ONLY_aristotle.lean`
  - `../../output/A1_density_ASSEMBLY_ONLY_aristotle.lean`
  - `../../output/A1_density_ASSEMBLY_ONLY_aristotle.lean`

## Why we are here
- Assembly-only variant for A1 density; intended as glue once component lemmas are proven.
- We keep it only if it does not introduce new assumptions beyond BaseAtomCone (tau = 0).

## Evidence / checks
- Request file exists; Aristotle output is draft and must be scanned for holes.
- Compare against mainline density statements in `Q3/Proofs/Q_nonneg_atoms_helpers.lean`.

## Decision
- Treat as optional glue; prefer mainline proof if it is already complete.
- If it adds assumptions or tau-shift, mark as legacy and drop.
