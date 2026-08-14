# Goal 058 mode-four Ferrers/prolate ODE closeout

Date: 2026-08-14

Lane: `CHALLENGER / NOT_RH`

Verdict:

```text
MODE4_FERRERS_ODE_PROVED_MODE0_SELECTION_FOURIER_AND_LEMMA72_MISSING
```

## Closed source seam

The existing backend ended at a normalized exact mode-four Legendre
coefficient recurrence.  This batch proves the missing implication

```text
exact matching root
  -> normalized recurrence row with geometric tail
  -> absolute and polynomially weighted summability
  -> uniformly convergent even Ferrers series on [-1,1]
  -> two legal termwise derivatives on (-1,1)
  -> exact source prolate ODE on (-1,1).
```

The infinite three-band calculation is not a formal rearrangement.  Each
outgoing band is proved summable, the exceptional zero row is handled
separately, and the two index shifts use the one-step `tsum` decomposition.

## Public suppliers

- `mode4OrdinaryLegendre_differentialEquation`
- `mode4OrdinaryLegendre_abs_le_one`
- `mode4RecurrenceRow_abs_summable_of_tail_splice`
- `mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice`
- `mode4FerrersSeries_contDiffOn_two_of_tail_splice`
- `mode4FerrersSeries_prolateDifferentialEquation`
- `mode4FerrersSeries_prolateDifferentialEquation_of_tail_splice`
- `exists_mode4MatchedNormalizedProlateFerrersRow_of_root`

The last theorem preserves the exact recurrence normalization and tail splice,
and adds interior `C2` regularity plus the exact prolate ODE.  It is conditional
on an exact `mode4RootFunction = 0`; it does not manufacture that root.

## Validation

- direct `lake env lean` on all four new files: PASS;
- target `lake build Q3.Proofs.RouteB.D0Mode4FerrersProlateDifferentialEquation`:
  PASS (`7768` jobs);
- full `lake build`: PASS (`7817` jobs);
- `bash scripts/q3_check.sh`: PASS (`q3_check ok`);
- forbidden `sorry`/new `axiom` scan: PASS;
- public axiom audit: `[propext, Classical.choice, Quot.sound]` only;
- `git diff --check`: PASS.

The recurring `UnicodeBasic` dependency-local-change warning predates this
batch and was not modified.

## Remaining G3 boundary

This is not yet an actual production `ProlatePair`.  Still missing:

1. unconditional root brackets on the required family;
2. endpoint realization/zero flux and exact physical-window scaling;
3. Sturm zero-count/order selection identifying the third even mode;
4. the corresponding mode-zero constructor;
5. restricted plus-phase finite-Fourier eigenrelations;
6. construction of `IsActualProlateModePair` on the unchanged production type;
7. CCM Lemma 7.2, the central overlap/floor, and one coupled cofinal schedule.

G1 remains independently stopped at literal quantitative simple-even ground,
sector ordering/gap, and same-trial cofinal tracking.

## Nonclaims

```text
NO_G1
NO_G3
NO_ROUTE_B_PROMOTION
NO_RH
```
