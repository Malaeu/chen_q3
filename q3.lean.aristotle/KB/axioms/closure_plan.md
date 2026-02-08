---
tags: [axiom, proof, pipeline]
priority: high
last_updated: 2026-02-08
---

# Axiom Closure Plan (τ=0 Mainline)

Goal: close all non‑core axioms except Weil + standard.

## Priority order
1) `prime_heat_bucket_data`
2) `prime_heat_bounds_arch_data`
3) `prime_b_grid_bounds_data`

## Rationale
- Heat bucket data is the tightest dependency in the PrimeCert chain and blocks downstream simplifications.
- Arch integral bound is local and can be formalized via monotonicity + integral estimates.
- Grid bounds can be certified with either analytic bounds or formal certificate tables.

## Success checks
- `lake env lean Q3/CheckAxioms.lean` shows only standard + Weil axioms.
- `./scripts/check_axioms.sh` clean.
