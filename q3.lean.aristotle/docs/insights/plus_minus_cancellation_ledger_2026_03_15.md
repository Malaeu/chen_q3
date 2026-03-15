# `(+,-)` cancellation ledger (2026-03-15)

## Status

Day 2 active artifact for the `Q_\zeta`-core short-circuit sprint.

This note refines the Day 1 adapter ledger by splitting the cross-sign defect
into named channels and recording the expected cancellations.

## Frozen theorem target

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_a^{+-}.
```

Current sprint question:

- is `E_a^{+-}=0`?
- if not, which part of `E_a^{+-}` is genuine and which part is just
  bookkeeping?

## Working decomposition

Write

```tex
E_a^{+-}
=
E_{a,\mathrm{bulk}}^{+-}
+ E_{a,\partial}^{+-}
+ E_{a,\mathrm{cap}}^{+-}
+ E_{a,\mathrm{comp}}^{+-}.
```

Interpretation:

- `E_{a,\mathrm{bulk}}^{+-}`:
  true mismatch in the filtered bulk;
- `E_{a,\partial}^{+-}`:
  boundary / commutator / Toeplitz-Hankel term;
- `E_{a,\mathrm{cap}}^{+-}`:
  finite-dimensional Suzuki cap term;
- `E_{a,\mathrm{comp}}^{+-}`:
  pure finite-section compression bookkeeping.

## Current expected vanishing table

### 1. Bulk term

Expectation:

```tex
E_{a,\mathrm{bulk}}^{+-}=0.
```

Reason:

- `(+,-)` is the stable anchor in all recent diagnostics;
- the old strongest filtered thesis in `Main_closure.tex` already points to
  exact `(+,-)` once `\widetilde Q_{M,N}` is used.

### 2. Boundary term

Main structural guess:

```tex
E_{a,\partial}^{+-}=0.
```

or at worst an explicitly simpler term than in `(++)`.

Reason:

- the moving-basis / prefix-holdout pathology concentrates in `(++)`, not in
  `(+,-)`;
- this strongly suggests that the same-sign boundary channel does not survive
  in the cross-sign block.

### 3. Cap term

Working expectation:

```tex
E_{a,\mathrm{cap}}^{+-}=0
```

or a very transparent finite cap term that does not move with `M`.

This is the only correction channel currently allowed to remain nonzero without
changing the theorem shape too much.

### 4. Compression term

Expectation:

```tex
E_{a,\mathrm{comp}}^{+-}=0
```

after the comparison object is written correctly in filtered form.

Reason:

- `\widetilde Q_{M,N}` was introduced precisely to absorb the naive section
  boundary bookkeeping.

## Decision table

### Best case

```tex
E_{a,\mathrm{bulk}}^{+-}
=
E_{a,\partial}^{+-}
=
E_{a,\mathrm{cap}}^{+-}
=
E_{a,\mathrm{comp}}^{+-}
=0.
```

Then `(+,-)` is exact.

### Acceptable corrected case

Only one channel survives, and it is explicit:

- cap-only;
- or a tiny transparent boundary term with fixed operator meaning.

### Bad case

Any surviving term that:

- moves with `M` like the failed `(++)` basis stories;
- cannot be named as boundary/cap/compression;
- or behaves like genuine bulk mismatch.

## Next proof obligations

1. identify the exact symbolic source of `E_{a,\partial}^{+-}`;
2. show that the same-sign commutator channel cancels in cross-sign form;
3. isolate whether any cap contribution can survive in `(+,-)`;
4. show that finite compression adds no extra hidden moving term.

## Relation to `(++)`

This note should become asymmetrical on purpose:

- `(+,-)` aims for exactness or very clean correction;
- `(++)` is where the surviving boundary channel is expected to live.

So if a term appears equally badly in both blocks, that is evidence against the
current theorem picture.
