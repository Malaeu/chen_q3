---
tags: [axiom, proof, pipeline]
priority: high
last_updated: 2026-02-09
---

# Axiom Closure Plan (τ=0 Mainline)

Goal: close all non‑core axioms except Weil + standard.

## Priority order
1) `prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all`
2) `prime_heat_bounds_arch_data`
3) `prime_b_grid_bucket_bounds`
4) `prime_b_grid_arch_bounds_data`

## Rationale
- GT10000 pointwise bound is currently a fallback axiom and dominates the heat chain.
- Arch integral bound is local and can be formalized via monotonicity + integral estimates.
- Grid bucket/arch bounds are the remaining PrimeCert data certificates.

## Success checks
- `lake env lean Q3/CheckAxioms.lean` shows only standard + Weil axioms.
- `./scripts/check_axioms.sh` clean.
