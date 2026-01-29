# Node: A1_density_main

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/A1_density_main.md`
- related outputs:
  - `../../output/A1_density_main_aristotle.lean`
  - `../../output/A1_density_main_aristotle.lean`
  - `../../output/A1_density_main_aristotle.lean`
  - `../../output/A1_density_main_aristotle.lean`

## Why we are here
- A1 density is required to lift Q >= 0 from atoms to all of W_K (single-scale, tau = 0).
- This node tracks the mainline (non-assembly) proof path for density.

## Evidence / checks
- Request file exists; linked Aristotle outputs must be scanned for holes (treat as draft).
- A1 density is already wired in `Q3/AxiomsTheorems.lean` via `A1prime.A1_density_WK_fixed_t0` (tau = 0).

## Decision
- Treat A1 density as mainline-complete (single-scale, fixed t0).
- Keep assembly/bridge drafts as optional references only.
