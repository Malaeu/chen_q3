# Node: RKHS_cap_rayleigh

## Status
- state: verified
- updated: 2026-01-25

## Source
- request: `../../input/RKHS_cap_rayleigh.md`
- related outputs:
  - `../../output/RKHS_cap_rayleigh_aristotle.lean`
  - `../../output/RKHS_cap_rayleigh_aristotle.lean`
  - `../../output/RKHS_cap_rayleigh_aristotle.lean`
  - `../../output/RKHS_cap_rayleigh_aristotle.lean`

## Why we are here
- Prime-term control depends on the RKHS cap; this node tracks the bound used in the single-scale chain.
- Needed to show the prime contribution is <= c_star/4 at t_critical.

## Evidence / checks
- Request file exists; ignore Aristotle drafts unless hole-free.
- `Q3/Proofs/RKHS_cap_rayleigh.lean` defines:
  - `weight_sum_le_rho_one` (core cap on weights)
  - `rkhs_cap_rayleigh_tcap` (Rayleigh bound from cap)
  - `rho_oneK` (K-dependent variant; avoid for single-scale)

## Decision
- Use `weight_sum_le_rho_one` + `rkhs_cap_rayleigh_tcap` as the mainline cap.
- Enforce single-scale (t_critical) and avoid `rho_oneK` unless explicitly needed.
