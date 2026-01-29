# Node: A1_density_hat_chain

## Status
- state: legacy
- updated: 2026-01-25

## Source
- request: `../../input/A1_density_hat_chain.md`
- related outputs:
  - `../../output/A1_density_hat_chain.lean`
  - `../../output/A1_density_hat_chain_v2.lean`
  - `../../output/A1_density_hat_chain_v3.lean`
  - `../../output/A1_density_hat_chain.lean`
  - `../../output/A1_density_hat_chain_v2.lean`
  - `../../output/A1_density_hat_chain_v3.lean`
  - `../../output/A1_density_hat_chain.lean`
  - `../../output/A1_density_hat_chain_v2.lean`
  - `../../output/A1_density_hat_chain_v3.lean`
  - `../../output/A1_density_hat_chain_v3.lean`
  - `../../output/A1_density_hat_chain_v2.lean`
  - `../../output/A1_density_hat_chain.lean`

## Why we are here
- Hat-chain density variants were explored as alternative approximations.
- Keep for historical context; mainline uses BaseAtomCone (tau = 0) instead.

## Evidence / checks
- Request file exists; outputs exist but are not part of the single-scale mainline.

## Decision
- Do not use unless mainline density fails; treat as fallback only.
