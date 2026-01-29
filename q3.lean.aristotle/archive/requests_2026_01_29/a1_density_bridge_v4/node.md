# Node: A1_density_bridge_v4

## Status
- state: draft
- updated: 2026-01-25

## Source
- request: `../../input/A1_density_bridge_v4.md`
- related outputs:
  - `../../output/A1_density_bridge_v4_aristotle.lean`
  - `../../output/A1_density_bridge_v4_aristotle.lean`
  - `../../output/A1_density_bridge_v4_aristotle.lean`
  - `../../output/A1_density_bridge_v4_aristotle.lean`

## Why we are here
- Bridge lemma version (v4), likely Aristotle-generated; may be useful but not trusted.
- Use only as a source of sub-lemmas if hole-free.

## Evidence / checks
- Request file exists; output `A1_density_bridge_v4_aristotle.lean` is a draft.
- Must scan for holes before reuse.

## Decision
- Treat as draft only; prefer v3 or mainline proof.
- Discard if it introduces tau-shift or two-scale assumptions.
