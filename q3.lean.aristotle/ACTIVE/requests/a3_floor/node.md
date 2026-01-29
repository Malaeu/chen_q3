# Node: A3_FLOOR

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/A3_FLOOR.md`
- related outputs:
  - `../../output/A3_03_k1_floor_aristotle.lean`
  - `../../output/A3_04_global_arch_floor_aristotle.lean`
  - `../../output/A3_FLOOR_aristotle.lean`
  - `../../output/A3_FLOOR_v18_aristotle.lean`
  - `../../output/A3_03_k1_floor_aristotle.lean`
  - `../../output/A3_04_global_arch_floor_aristotle.lean`
  - `../../output/A3_FLOOR_aristotle.lean`
  - `../../output/A3_FLOOR_v18_aristotle.lean`
  - `../../output/A3_FLOOR_aristotle.lean`
  - `../../output/A3_FLOOR_v18_aristotle.lean`
  - `../../output/A3_FLOOR_aristotle.lean`
  - `../../output/A3_FLOOR_v18_aristotle.lean`

## Why we are here
- A3 floor at t_critical is the last analytic input needed to close the single-scale Rayleigh bound.
- This node is the canonical landing zone for the floor proof (or its micro-lemmas).

## Evidence / checks
- Request file exists; multiple Aristotle outputs are linked but must be scanned for holes (treat as draft).
- Single-scale chain currently assumes a floor input in `Q3/Proofs/A3_Floor_Critical_Goal.lean`.

## Decision
- Use Proshka floor_tcritical request as the main proof path; ignore two-scale variants.
- Keep tau = 0 and t = t_critical in all statements; no legacy detours.
