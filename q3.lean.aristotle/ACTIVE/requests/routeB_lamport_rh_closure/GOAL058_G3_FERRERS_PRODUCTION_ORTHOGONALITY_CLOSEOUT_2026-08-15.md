# Goal 058 G3 — Ferrers production orthogonality closeout

Date: 2026-08-15

Verdict: `G3_FERRERS_PRODUCTION_ORTHOGONALITY_PASS`

## Exact Lean result

`D0ModeZeroFourFerrersProductionOrthogonality.lean` proves a generic
Lagrange-identity receiver for two continuous complex prolate eigenfunctions
on a closed physical window.  If their differential eigenvalues are distinct
and both endpoint fluxes vanish, the bilinear product integral is exactly
zero.  The proof works directly at the singular endpoints: it extends each
flux continuously by its one-sided zero limit, differentiates the Wronskian
on the open interval, and applies the interval fundamental theorem of
calculus.

The production theorem instantiates that receiver with the already-selected
Ferrers indices `0` and `2`.  Their strict differential spectral order and
accepted endpoint zero-flux theorems discharge the generic hypotheses.  The
result is transported through the canonical whole-line zero extension and
positive real `L2` normalization, yielding the exact production inner product

```text
integral (star h0 * h4) = 0.
```

No orthogonality binder, new family, numerical approximation, or external
source assumption is introduced.

## Search and validation

The exact preflight query

```text
prolate endpoint zero flux distinct eigenvalues orthogonality closed interval
production Ferrers modes
```

returned `no hits` at clean HEAD `6fb660f6`.

Checks:

- direct Lean: PASS;
- named build: PASS (`7808` jobs);
- `q3_check`: PASS;
- `git diff --check` and forbidden-token scan: PASS;
- both public theorem axiom surfaces: exactly
  `[propext, Classical.choice, Quot.sound]`.

## Exact remaining source wall

The production `ProlatePair` now satisfies orthogonality, but it is still not
an `IsActualProlateModePair`.  The remaining exact fields are:

1. Sturm interior zero counts `0` and `4` for the selected witnesses;
2. positive-phase Fourier scalar identification and order
   `0 < chi2 < chi0`.

Only after those fields are proved can the existing actual-mode consequences
and CCM Lemma 7.2 chain be invoked.  G1 remains independently open.

Stop code:

`G3_PRODUCTION_PROLATEPAIR_ORTHOGONAL_ZERO_COUNTS_AND_FOURIER_SIGN_ORDER_MISSING`

Route status: `CHALLENGER_NOT_RH`.  No G1/G3 closure, Route B promotion, or RH
claim is made.
