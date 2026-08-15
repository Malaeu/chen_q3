# Goal 058 G3 — dimensionless finite-Fourier scaling closeout

Date: 2026-08-15

Status: `SOURCE_FREE_DIMENSIONLESS_FOURIER_SCALING_PROVED_G1_OPEN_G3_OPEN_CHALLENGER_NOT_RH`

## Scope

This leaf closes the exact change-of-variables bridge from the dimensionless
Slepian plus-phase kernel on `[-1,1]` to the existing physical Ferrers
production window.  It adds no dimensionless eigenrelation or classical
source assertion.

## New kernel-checked surface

File:

`Q3/Proofs/RouteB/D0Mode4FerrersDimensionlessFourierScaling.lean`

SHA-256:

`e32f910694c0b6a8bc3f86b8384bd0ee23b60443a657909f2cb59e5c6099498b`

Public definitions:

1. `mode4SlepianC` — exact dimensionless bandwidth
   `c = 2 * pi * mProject`.
2. `selectedFerrersDimensionlessFourierAction` — literal plus-phase action
   on `[-1,1]` for the already selected coefficient carrier.

Public theorems:

1. `physicalFerrers_finiteFourierAction_eq_scale_dimensionless` — exact
   physical/dimensionless integral change of variables.
2. `normalizedPhysicalMode_finiteFourierAction_eq_scale_dimensionless` —
   the same identity after the existing positive physical `L²`
   normalization.
3. `normalizedPhysicalMode_finiteFourier_eq_lambda_mul_of_dimensionless` —
   any source-supplied dimensionless scalar `mu` becomes the physical scalar
   `sqrt mProject * mu` on the corresponding point.

## Verification

- strict startup before write: `P9_STRICT_PASS`, clean worktree, HEAD
  `370a9e34`;
- exact KB query: `no hits`;
- direct Lean: exit `0`;
- named build: `7787` jobs, exit `0`;
- `q3_check`: `ok`;
- diff scan: clean;
- public axioms: exactly `[propext, Classical.choice, Quot.sound]`;
- cartographer/catalog: `267` RouteB files, `2484` declarations, `0`
  missing declaration rows, `2865` external atoms.

## Honest boundary

This removes scale and kernel-sign transport from the external source wall.
It does not provide the dimensionless Slepian eigenrelations themselves or
prove their positive strict scalar order.  The exact selected dimensionless
zero counts `0/4` and the exact plus-phase source identities/order remain
under Proshka adjudication for the same `S0/S4` witnesses.

G1 remains independently open.  No `IsActualProlateModePair`, G3 closure,
Route B promotion, or RH claim is made.

Stop code:

`G3_DIMENSIONLESS_TO_PHYSICAL_FOURIER_SCALING_PROVED_CLASSICAL_ZEROCOUNT_AND_PHASE_ORDER_SOURCE_CARRIERS_PENDING`
