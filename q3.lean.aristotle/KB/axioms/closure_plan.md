---
tags: [axiom, proof, pipeline]
priority: high
last_updated: 2026-02-09
---

# Axiom Closure Plan (τ=0 Mainline)

Goal: close all non‑core axioms except Weil + standard.

## Priority order
1) `prime_heat_bounds_arch_data`
2) `prime_b_grid_bucket_bounds`
3) `prime_b_grid_arch_bounds_data`

## Rationale
- Arch integral bound is local and can be formalized via monotonicity + integral estimates.
- Grid bucket/arch bounds are the remaining PrimeCert data certificates.

## Success checks
- `lake env lean Q3/CheckAxioms.lean` shows only standard + Weil axioms.
- `./scripts/check_axioms.sh` clean.
