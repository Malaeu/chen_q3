# `(+,-)` cancellation ledger (2026-03-15)

## Status

Day 2 active artifact for the `Q_\zeta`-core short-circuit sprint.

This note refines the Day 1 adapter ledger by splitting the cross-sign defect
into named channels, isolating the infinite-tail versus finite-section layers,
and recording the exact cancellation claims that should be turned into the
first theorem attempt.

## Frozen theorem target

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_a^{+-}.
```

Current sprint question:

- is `E_a^{+-}=0`?
- if not, which part of `E_a^{+-}` is genuine and which part is just
  bookkeeping?

The first important asymmetry is frozen here:

- `(+,-)` is the calibration block;
- `(++)` is the hard same-sign block;
- any channel that survives equally badly in both blocks counts against the
  current theorem picture.

## Two-layer defect split

The Day 2 receiver should separate the true operator defect from pure finite
compression bookkeeping.

### Infinite-tail level

Define the cross-sign infinite-tail defect

```tex
\mathcal D_{a,N}^{+-}
:=
S_{a,\infty,N}^{+*}G_g[a]S_{a,\infty,N}^{-}
-\kappa_{+-}(a)\Delta_N^{+*}Q_\infty^{+-}\Delta_N^-.
```

This is the structural object. It is where bulk, boundary, and cap should be
classified before any finite-section language is allowed to dominate.

### Finite-section level

Then the finite filtered defect should read

```tex
E_a^{+-}
=
P_{M,N}\,\mathcal D_{a,N}^{+-}\,P_{M,N}
+ E_{a,\mathrm{comp}}^{+-}.
```

So the finite-section note is only theorem-grade if it distinguishes:

- operator content coming from `\mathcal D_{a,N}^{+-}`;
- pure compression bookkeeping carried by `E_{a,\mathrm{comp}}^{+-}`.

## Working decomposition

Write

```tex
\mathcal D_{a,N}^{+-}
=
\mathcal D_{a,\mathrm{bulk}}^{+-}
+ \mathcal D_{a,\partial}^{+-}
+ \mathcal D_{a,\mathrm{cap}}^{+-},
```

Interpretation:

- `\mathcal D_{a,\mathrm{bulk}}^{+-}`:
  true mismatch in the filtered bulk;
- `\mathcal D_{a,\partial}^{+-}`:
  boundary / commutator / Toeplitz-Hankel term;
- `\mathcal D_{a,\mathrm{cap}}^{+-}`:
  finite-dimensional Suzuki cap term;
- `E_{a,\mathrm{comp}}^{+-}`:
  pure finite-section compression bookkeeping.

Equivalently, at the finite level:

```tex
E_a^{+-}
=
E_{a,\mathrm{bulk}}^{+-}
+ E_{a,\partial}^{+-}
+ E_{a,\mathrm{cap}}^{+-}
+ E_{a,\mathrm{comp}}^{+-},
```

with the understanding that the first three should descend from the
infinite-tail channels above rather than being treated as ad hoc matrix
remainders.

## Current expected vanishing / surviving table

| Channel | Structural meaning | Expected status in `(+,-)` | What kills the picture |
| --- | --- | --- | --- |
| `\mathcal D_{a,\mathrm{bulk}}^{+-}` | genuine filtered bulk mismatch | must vanish | any nonzero unnamed bulk residue |
| `\mathcal D_{a,\partial}^{+-}` | boundary / commutator / Toeplitz-Hankel channel | should vanish, or be much simpler than `(++)` | an `M`-moving same-sign style term |
| `\mathcal D_{a,\mathrm{cap}}^{+-}` | finite Suzuki cap channel | may survive only as explicit fixed finite term | cap term that drifts with `M` or mimics basis-fit behavior |
| `E_{a,\mathrm{comp}}^{+-}` | pure finite-section bookkeeping | must vanish once `\widetilde Q_{M,N}` is used correctly | any extra hidden section defect after filtered reformulation |

### 1. Bulk term

Expectation:

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

Reason:

- `(+,-)` is the stable anchor in all recent diagnostics;
- the old strongest filtered thesis in `Main_closure.tex` already points to
  exact `(+,-)` once `\widetilde Q_{M,N}` is used.

### 2. Boundary term

Main structural guess:

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

This is stronger than a generic “small correction” claim: the preferred theorem
shape is that the cross-sign boundary / commutator channel disappears
altogether, and any surviving boundary term would already count as a degraded
fallback.

Reason:

- the moving-basis / prefix-holdout pathology concentrates in `(++)`, not in
  `(+,-)`;
- this strongly suggests that the same-sign boundary channel does not survive
  in the cross-sign block.

### 3. Cap term

Working expectation:

```tex
\mathcal D_{a,\mathrm{cap}}^{+-}=0
```

or a very transparent finite cap term that does not move with `M`.

This is the only correction channel currently allowed to remain nonzero without
changing the theorem shape too much. In other words: cap-only is the preferred
corrected fallback; cross-sign boundary survival is already second-best.

### 4. Compression term

Expectation:

```tex
E_{a,\mathrm{comp}}^{+-}=0
```

after the comparison object is written correctly in filtered form.

Reason:

- `\widetilde Q_{M,N}` was introduced precisely to absorb the naive section
  boundary bookkeeping.

## Candidate sublemmas

The note is theorem-ready only if the next proof attempt can be split into
small named claims. The intended sublemma stack is:

### CL1. Cross-sign bulk exactness

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

This is the non-negotiable structural claim: if it fails, the route is not a
boundary/cap correction story.

### CL2. Cross-sign boundary cancellation

```tex
\mathcal D_{a,\partial}^{+-}=0
```

or a named explicitly simpler operator.

Interpretation:

- the same-sign boundary/commutator channel that is expected to survive in
  `(++)` must cancel in `(+,-)`;
- if a cross-sign boundary term survives, it must have a fixed operator form
  rather than a moving matrix-fit phenotype.

### CL3. Cross-sign cap transparency

```tex
\mathcal D_{a,\mathrm{cap}}^{+-}=0
```

or an explicit finite-dimensional cap term independent of the section length.

### CL4. Compression neutrality

```tex
E_{a,\mathrm{comp}}^{+-}=0.
```

This is the section-level bookkeeping lemma saying that the filtered comparison
object already absorbed the naive finite-section defect.

### CL5. Final adapter fork

Conclude one of:

1. exact cross-sign identity;
2. explicit corrected cross-sign identity;
3. named obstruction that kills the current theorem shape.

## Theorem fork

### Best case

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}
=
\mathcal D_{a,\partial}^{+-}
=
\mathcal D_{a,\mathrm{cap}}^{+-}
=
E_{a,\mathrm{comp}}^{+-}
=0.
```

Then `(+,-)` is exact.

### Acceptable corrected case

Only one channel survives, and it is explicit:

- preferred corrected case: cap-only;
- degraded corrected case: a tiny transparent boundary term with fixed operator
  meaning.

Allowed theorem output:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+C_a^{+-,\mathrm{cap}}
```

or

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+H_a^{+-,\partial},
```

with `H_a^{+-,\partial}` named, stable, and not moving with section length.

### Bad case

Any surviving term that:

- moves with `M` like the failed `(++)` basis stories;
- cannot be named as boundary/cap/compression;
- or behaves like genuine bulk mismatch.

This is the route-kill condition for the cross-sign adapter theorem.

## Exact proof-obligation receiver

1. identify the exact symbolic source of `\mathcal D_{a,\partial}^{+-}`;
2. show that the same-sign commutator channel cancels in cross-sign form;
3. isolate whether any cap contribution can survive in `(+,-)`;
4. show that finite compression adds no extra hidden moving term;
5. separate which statements are infinite-tail lemmas and which are finite
   compression lemmas.

## Relation to `(++)`

This note should become asymmetrical on purpose:

- `(+,-)` aims for exactness or very clean correction;
- `(++)` is where the surviving boundary channel is expected to live.

So if a term appears equally badly in both blocks, that is evidence against the
current theorem picture.

Concrete handoff to `A3`:

- if `A2` lands, then `A3` should start from the contrast

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}},
```

not from any new shared-basis hunt.
