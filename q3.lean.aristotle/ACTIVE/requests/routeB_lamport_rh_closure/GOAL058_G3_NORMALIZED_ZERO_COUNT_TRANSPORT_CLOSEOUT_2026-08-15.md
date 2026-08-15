# Goal 058 G3 — normalized zero-count transport closeout

Date: 2026-08-15

Status: `SOURCE_FREE_TRANSPORT_PROVED_G1_OPEN_G3_OPEN_CHALLENGER_NOT_RH`

## Scope

This leaf closes only the local transport question K3 from
`GOAL058_G3_ACTUAL_MODE_FINAL_SOURCE_MYTHOS_REQUEST_2026-08-15.txt`.
It does not import a dimensionless Ferrers nodal count and does not prove the
positive-phase Fourier scalar order.

## New kernel-checked surface

File:

`Q3/Proofs/RouteB/D0Mode4FerrersNormalizedZeroCountTransport.lean`

SHA-256:

`721bbf3ebe92bf0fed7afdd42a06f229cc001d5506d87b313dafe85fd788a8ba`

Public theorems:

1. `normalizedPhysicalMode_interiorZeros_eq_image` identifies the exact
   physical interior zero set with the injective scaled image of the
   dimensionless Ferrers zero set in `(-1,1)`.
2. `normalizedPhysicalMode_interiorZeros_ncard_eq` transfers `Set.ncard`
   exactly across the positive scale `sqrt mProject`.
3. `normalizedPhysicalMode_zero_ne` proves that the normalized physical mode
   is nonzero at the center.
4. `finiteFourier_real_scalar_unique_at` proves uniqueness of a real
   restricted finite-Fourier scalar from one nonzero value of the common
   eigenfunction.

Thus neither the positive normalization nor the zero extension can create
endpoint or exterior zeros inside `prolateInteriorZeros`.  Once an exact
dimensionless count is imported for the already selected Ferrers witnesses,
the project counts `0` and `4` are local consequences.  Likewise, a canonical
source scalar can be identified with the existing existential production
scalar without replacing the production witness.

## Verification

- strict startup before write: `P9_STRICT_PASS`, clean worktree, HEAD
  `c8c31368`;
- exact KB preflight query: `no hits`;
- direct Lean: exit `0`;
- named build: `7785` jobs, exit `0`;
- `q3_check`: `ok`;
- forbidden/hole and diff scans: clean;
- public axioms: exactly `[propext, Classical.choice, Quot.sound]`;
- cartographer: `265` RouteB files, `2474` declarations, `0` missing
  declaration rows after catalog sync, `2858` external atoms.

## Honest boundary

Still missing from the exact production `IsActualProlateModePair`:

- source-locked dimensionless Ferrers nodal counts for the selected degree
  `0` and degree `4` witnesses;
- source-locked positive-phase Fourier facts yielding
  `0 < chi2 ∧ chi2 < chi0`.

G1 remains independently open at the cofinal full-complement-floor source
wall.  No G3 closure, Route B promotion, or RH claim is made.

Stop code:

`G3_NORMALIZED_ZERO_COUNT_TRANSPORT_PROVED_DIMENSIONLESS_COUNTS_AND_POSITIVE_PHASE_FOURIER_ORDER_SOURCE_LOCKS_MISSING`
