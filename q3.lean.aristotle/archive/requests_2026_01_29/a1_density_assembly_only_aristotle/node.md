# Node: A1_density_ASSEMBLY_ONLY_aristotle

## Status
- state: draft
- updated: 2026-01-25

## Source
- request: `../../input/A1_density_ASSEMBLY_ONLY_aristotle.md`
- related outputs:
  - `../../output/A1_density_ASSEMBLY_ONLY_aristotle.lean`
  - `../../output/A1_density_ASSEMBLY_ONLY_aristotle.lean`
  - `../../output/A1_density_ASSEMBLY_ONLY_aristotle.lean`
  - `../../output/A1_density_ASSEMBLY_ONLY_aristotle.lean`

## Why we are here
- Aristotle-generated assembly-only draft for A1 density; potentially reusable as glue.
- Must be treated as a draft until scanned for holes.

## Evidence / checks
- Request file exists; output is in `ACTIVE/output/A1_density_ASSEMBLY_ONLY_aristotle.lean`.
- Run hole scan before reuse: `rg -n \"sorry|exact\\?\" <file>`.

## Decision
- Use only if hole-free and matches BaseAtomCone (tau = 0).
- Otherwise extract any clean lemmas and discard the rest.
