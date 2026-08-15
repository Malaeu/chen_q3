# Goal 058 G3 — normalized actual-mode local fields closeout

Date: 2026-08-15

Status: `SOURCE_FREE_LOCAL_FIELDS_PROVED_G1_OPEN_G3_OPEN_CHALLENGER_NOT_RH`

## Scope

This leaf audits and closes the source-free analytic plumbing between the
already accepted normalized Ferrers witnesses and the unchanged
`D0Pstar.IsActualProlateModePair` predicate.  It adds no classical nodal or
Fourier phase/order assertion.

## New kernel-checked surface

File:

`Q3/Proofs/RouteB/D0Mode4FerrersNormalizedActualModeLocalFields.lean`

SHA-256:

`fe4aab59c205a5d09a0c1f8ee08d40e473abac8408c5c2bd1b1ab4bfb91384e9`

Public theorems:

1. `normalizedPhysicalMode_im_eq_zero` — the whole-line normalized zero
   extension is real-valued.
2. `normalizedPhysicalMode_contDiffOn_two_open` — exact interior `C²`
   regularity after complex coercion and positive normalization.
3. `physicalComplex_prolateWaveExpression_eigenrelation` — the accepted raw
   physical Ferrers source satisfies the literal production differential
   expression.
4. `normalizedPhysicalMode_hasDerivAt` — exact interior derivative after
   normalization.
5. `normalizedPhysicalMode_prolateWaveExpression_eigenrelation` — the
   normalized production witness satisfies the exact literal
   `prolateWaveExpression` eigenrelation on the open physical window.

The proof uses the already accepted raw derivative and weighted-flux
derivative theorems, local equality inside the open window, and
`Filter.EventuallyEq.fderiv_eq`.  It does not infer any source index, nodal
count, or finite-Fourier scalar sign.

## Verification

- strict startup before write: `P9_STRICT_PASS`, clean worktree, HEAD
  `c4e37dce`;
- exact KB query: `no hits`;
- direct Lean: exit `0`;
- named build: `7786` jobs, exit `0`;
- `q3_check`: `ok`;
- forbidden/hole and diff scans: clean;
- public axioms: exactly `[propext, Classical.choice, Quot.sound]`;
- cartographer: `266` RouteB files, `2479` declarations, `0` missing
  declaration rows after catalog sync, `2865` external atoms.

## Honest boundary

The remaining actual-mode wall is now purely the exact classical source lock
for the already selected degree-0/degree-4 Ferrers witnesses:

- dimensionless nodal counts `0` and `4`;
- positive plus-phase Fourier scalar order `0 < chi2 ∧ chi2 < chi0`.

After those source facts are accepted, the previously proved zero-count
transport, the fields in this leaf, the exact production identities, and the
orthogonality theorem supply local record assembly.  That assembly has not
yet been claimed.  G1 remains independently open; no G3 closure, Route B
promotion, or RH claim is made.

Stop code:

`G3_NORMALIZED_ACTUAL_MODE_LOCAL_FIELDS_PROVED_ONLY_CLASSICAL_NODAL_AND_FOURIER_ORDER_SOURCE_LOCKS_MISSING`
