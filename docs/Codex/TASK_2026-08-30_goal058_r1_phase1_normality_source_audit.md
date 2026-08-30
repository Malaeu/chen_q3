# Codex task — Goal 058 R1 Phase 1 same-ground-family normality source audit

Date: 2026-08-30
Status: `ACTIVE_SOURCE_AUDIT`
Parent: Goal 058 / `GOAL058_GROUND_TO_TRIAL_SAME_FAMILY_BRIDGE`

## Exact desired conclusion

For the literal selected ground-family Proposition-5.9 transforms, use one
precommitted positive scalar gauge defined by a fixed compact `K₀` with
nonempty interior,

```text
Fhat_k(z) = T_k(xi_k)(z) / ||T_k(xi_k)||_{L²(K₀)},
```

and obtain both:

1. local boundedness on every compact of the centered critical strip;
2. identification of every locally-uniform cluster with the required
   `centeredXi` target, while preserving the same ground family and its
   real-zero property.

## Missing implication

The gauge gives unit `L²(K₀)` mass and hence compact bounds strictly inside
`K₀`. It does not by itself propagate bounds to the whole strip. Real zeros and
a single compact normalization also do not imply normality when exponential
type grows with `k` (`cos(k z)` is the guard).

## Forbidden shortcuts

- no residual/complement-floor/tracking-rate hypothesis under a new name;
- no trial-family or centered-Pstar normality spliced onto the ground family;
- no generic Montel wrapper before a uniform whole-strip bound;
- no anchor, rank, compact, or subsequence selected after inspecting cells;
- no transfer of a fixed-type Cartwright/de Branges theorem across growing type
  without an exact uniform adapter;
- no finite-cell or numeric evidence occupying a cofinal quantifier.

## Bounded candidates and cheapest killers

### R1A — source-matched de Branges embedding

Find an exact de Branges-space theorem whose evaluation/reproducing-kernel
bound is uniform for the source-defined family after the fixed `L²(K₀)` gauge.
Kill if the space, Hermite-Biehler generator, or kernel constant varies with
`k` without a proved uniform comparison.

### R1B — Cartwright/Levin real-zero compactness

Find an exact primary theorem turning real zeros plus one fixed compact norm
into whole-strip normality with the actual growing exponential type. Kill if a
uniform type/indicator bound is required and is exactly the missing tracking
information.

### R1C — Herglotz logarithmic-derivative compactness

Pass to the logarithmic derivative or zero measure only if normalization,
additive constants, and recovery of the original entire functions are fixed
uniformly on the same family. Kill if measure tightness or recovery again needs
the absent type/rate bound.

## Required output

Return exactly one local discriminator result:

- `TRY_R1_SAME_GROUND_FAMILY_NORMALITY_SOURCE` with an exact primary theorem,
  bibliographic pin, parameter crosswalk, assumptions, topology, consumer, and
  two falsifying plants; or
- `KILL_R1_SAME_GROUND_FAMILY_NORMALITY_SOURCE` with a source-backed reason all
  three candidates require the same missing uniform type/rate input.

This transaction is paper/source read-only. It authorizes no Lean, Aristotle,
phase-key change, Route promotion, or RH claim.
