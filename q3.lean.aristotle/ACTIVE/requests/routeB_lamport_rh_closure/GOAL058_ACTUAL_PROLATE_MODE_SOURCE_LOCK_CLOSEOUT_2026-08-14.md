# Goal 058 actual prolate-mode source lock closeout

Date: 2026-08-14
Classification: `PASS_SOURCE_OBJECT_LOCK_AND_WEAK_RECORD_PLANT`
Promotion: none

## Result

`Q3/Proofs/RouteB/ProlateActualModeSourceLock.lean` adds the external predicate
`IsActualProlateModePair` over the unchanged production `ProlatePair`.

The predicate source-locks:

- positive bandwidth and the positive integral phase convention;
- literal restricted finite-Fourier eigenrelations with the exact
  `h0 <-> chi0` and `h4 <-> chi2` index dictionary;
- literal prolate differential eigenrelations;
- real-valuedness on the whole line and `C^2` regularity on the open source
  interval (the stored modes are zero-extended outside it);
- orthogonality and eigenvalue ordering;
- Sturm zero-count selection `0` and `4` on the interior window.

It is a proposition only.  It does not assert that an actual pair exists and
does not add stronger fields to the production record.

## Permanent discriminator

`looseProlatePairPlant` is an explicit production `ProlatePair`: both stored
functions are the same normalized even interval indicator.  Every old record
field is kernel checked, including support, integrability, normalization,
integrals, and centre identities.

`looseProlatePairPlant_not_actual` proves that the plant is rejected by the
new source predicate.  Therefore future constructor work cannot cite bare
`ProlatePair` inhabitation as construction of the actual source modes.

## Validation

- direct Lean: PASS;
- target build: PASS, 7745 jobs;
- `q3_check`: PASS;
- forbidden-token scan: PASS;
- public axiom audit:
  `[propext, Classical.choice, Quot.sound]` only.

## Remaining wall

The next genuine G3 theorem is existence and selection of a production pair
satisfying `IsActualProlateModePair`, followed by the source-locked CCM Lemma
7.2 uniform comparison to `explicitCCMLimitH`.  The predicate and plant alone
do not close G3.  G1 remains independently open.
