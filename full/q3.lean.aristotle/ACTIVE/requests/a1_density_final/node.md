# Node: A1_density_final

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/A1_density_final.md`
- related outputs:
  - `../../output/A1_density_FINAL_assembly_aristotle.lean`
  - `../../output/A1_density_FINAL_v3_aristotle.lean`
  - `../../output/A1_density_FINAL_with_bridge_aristotle.lean`
  - `../../output/A1_density_final_aristotle.lean`
  - `../../output/A1_density_FINAL_assembly_aristotle.lean`
  - `../../output/A1_density_FINAL_v3_aristotle.lean`
  - `../../output/A1_density_FINAL_with_bridge_aristotle.lean`
  - `../../output/A1_density_final_aristotle.lean`
  - `../../output/A1_density_FINAL_assembly_aristotle.lean`
  - `../../output/A1_density_FINAL_v3_aristotle.lean`
  - `../../output/A1_density_FINAL_with_bridge_aristotle.lean`
  - `../../output/A1_density_final_aristotle.lean`
  - `../../output/A1_density_final_aristotle.lean`

## Why we are here
- Final A1 density statement: BaseAtomCone (tau = 0) dense in the even cone on W_K.
- Needed to close the A1/A2 step after atom positivity.

## Evidence / checks
- Request file exists; drafts are linked but not needed for mainline.
- A1 density is already wired in `Q3/AxiomsTheorems.lean` as `A1_density_WK`.

## Decision
- Mark final A1 density as mainline-complete; tau = 0 only.
- Treat remaining drafts as legacy unless they provide missing sub-lemmas.
