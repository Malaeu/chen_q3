# Node: A1_density_bridge_v3

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/A1_density_bridge_v3.md`
- related outputs:
  - `../../output/A1_density_bridge_v3.lean`
  - `../../output/A1_density_bridge_v3.lean`
  - `../../output/A1_density_bridge_v3.lean`
  - `../../output/A1_density_bridge_v3.lean`

## Why we are here
- Bridge lemma version (v3) for A1 density; intended to connect hat-approximation to BaseAtomCone.
- Keep only if it preserves tau = 0 and the W_K target topology.

## Evidence / checks
- Request file exists; output `A1_density_bridge_v3.lean` must be scanned for holes.
- Compare against `Q3/Proofs/Q_nonneg_atoms_helpers.lean` for current lemma naming.

## Decision
- Prefer mainline A1 proof; use v3 bridge only if it is hole-free and minimal.
- If it introduces shifted atoms or extra parameters, mark legacy.
