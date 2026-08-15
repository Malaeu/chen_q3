# Goal 058 G3 — normalized Ferrers production ProlatePair closeout

Date: 2026-08-15

Verdict: `G3_FERRERS_PRODUCTION_PROLATEPAIR_PASS`

## Exact Lean result

`D0Mode4FerrersPhysicalNormalizedZeroExtension.lean` defines the canonical
whole-line zero extension of an accepted physical Ferrers witness, proves its
compact support and integrability, constructs its positive `L2` mass and unit
normalization, and proves that the normalized mode has positive whole-line
integral.  The already-proved real nonzero restricted Fourier scalar and its
eigenrelation survive both zero extension and normalization.

`D0ModeZeroFourFerrersProductionProlatePair.lean` then selects the exact
zero-based even carrier indices `0` and `2` and constructs the unchanged
production `D0Pstar.ProlatePair`.  The resulting record contains the actual
normalized zero-extended Ferrers witnesses, positive `I0/I4`, nonzero real
`chi0/chi2`, and both exact restricted finite-Fourier eigenrelations.  The
strict differential spectral order `Lambda_0 < Lambda_2` is retained.

No new source assumption or parallel family is introduced.

## Search and validation

The exact preflight query

```text
physical Ferrers zero extension L2 normalization compact support production
ProlatePair constructor mode zero mode four restricted Fourier real nonzero
scalar
```

returned `no hits` at clean HEAD `cd5504a0`.

Checks:

- direct Lean for both files: PASS;
- named builds: PASS (`7783` and `7807` jobs);
- `q3_check` for both files: PASS;
- `git diff --check`: PASS;
- public axiom surface: exactly
  `[propext, Classical.choice, Quot.sound]`.

## Exact remaining source wall

This is real production-object construction, but not yet
`IsActualProlateModePair`.  The remaining source facts are:

1. exact Sturm interior zero counts `0` and `4` for the selected witnesses;
2. orthogonality of the two normalized modes;
3. positive-phase scalar identification and order `0 < chi2 < chi0`.

Only after those fields are proved can the existing actual-mode consequences
and CCM Lemma 7.2 chain be invoked.  G1 remains independently open.

Stop code:

`G3_PRODUCTION_PROLATEPAIR_CONSTRUCTED_ACTUAL_MODE_ZERO_COUNTS_ORTHOGONALITY_AND_FOURIER_SIGN_ORDER_MISSING`

Route status: `CHALLENGER_NOT_RH`.  No G1/G3 closure, Route B promotion, or RH
claim is made.
