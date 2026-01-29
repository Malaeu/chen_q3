# Node: A1_ULTRA_MINIMAL

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/A1_ULTRA_MINIMAL.md`
- related outputs:
  - `../../output/A1_density_ULTRA_MINIMAL_aristotle.lean`
  - `../../output/A1_density_ULTRA_MINIMAL_aristotle.lean`

## Why we are here
- Ultra-minimal A1 density is a fallback path if the full density proof is too heavy.
- Tracks the smallest lemma set needed to carry the A1 step in single-scale mainline.

## Evidence / checks
- Request file exists; validate any candidate proof against BaseAtomCone (tau = 0).
- Use only if it preserves the same W_K target as the mainline A1.

## Decision
- Keep as fallback only; prefer `A1_density_main` / `A1_density_final` when viable.
- Do not relax the target cone or topology in order to “simplify”.
