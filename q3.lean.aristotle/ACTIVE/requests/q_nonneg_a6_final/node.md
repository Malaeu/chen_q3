# Node: Q_nonneg_A6_final

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/Q_nonneg_A6_final.md`
- related outputs: (none linked)

## Why we are here
- Final assembly: Q >= 0 on W_K (and hence W) after A1/A2 + atom positivity.
- This is the last glue step before Weil positivity -> RH in the project chain.

## Evidence / checks
- Request file exists; check `Q3/Proofs/Q_nonneg_atoms_closure.lean` and `Q3/Proofs/Q_nonneg_atoms_helpers.lean` for assembly points.
- Depends on A1 density and A2 continuity plus `Q_nonneg_on_atoms`.

## Decision
- Treat as pure wiring once upstream lemmas are closed; avoid touching analysis here.
- Keep the final statement consistent with BaseAtomCone (tau = 0) and single-scale.
