# Node: rho_oneK_tcritical_le_cstar_quarter

## Status
- state: in_progress
- updated: 2026-01-25

## Source
- request: `../../input/rho_oneK_tcritical_le_cstar_quarter.md`
- related outputs: (none linked)

## Why we are here
- Single-scale chain needs the prime cap bound at t_critical; this node tracks `rho_one <= c_star/4`.
- The intent is to eliminate K-dependence in the cap for the single-scale mainline.

## Evidence / checks
- Request file exists and defines the target inequality.
- Expect this to be a pure constant comparison in `Q3/Proofs/SingleScale_Assumptions.lean` using `simp`/`norm_num` on `rho_one` and `c_star`.

## Decision
- Prove directly by unfolding constants (no Aristotle; no Proshka needed).
- If `rho_oneK` still carries an exponential K-factor, move to the single-scale `rho_one` definition first, then close.
