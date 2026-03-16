# `H1^\infty \to H1^\partial \to H1^f` proof-obligation table (2026-03-16)

## Status

Day 4 active artifact for the `Q_\zeta`-core short-circuit sprint.

This note is the next receiver after:

- `A2`: the `(+,-)` adapter theorem was reduced to exactness / cap-only
  fallback;
- `A3`: the `(++)` block was reduced to a same-sign boundary term plus cap.

The role of this note is to make the remaining `H1` work look like a finite
list of lemmas rather than one large cloud.

## Frozen input from `A2` and `A3`

Cross-sign adapter target:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_{a,\mathrm{cap}}^{+-},
```

with preferred stronger version `E_{a,\mathrm{cap}}^{+-}=0`.

Same-sign target:

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

## Stage map

The current intended theorem ladder is:

```tex
H1^\infty \to H1^\partial \to H1^f.
```

Interpretation:

- `H1^\infty`: classify the infinite-tail defect;
- `H1^\partial`: isolate the surviving boundary/cap channels;
- `H1^f`: descend to the finite filtered sections with no extra mystery term.

## Proof-obligation table

| ID | Stage | Exact target | Why it matters | Kill condition |
| --- | --- | --- | --- | --- |
| `PO1` | `H1^\infty` | define `\mathcal D_{a,N}` and split it blockwise | fixes the actual operator object | defect cannot be written stably at the tail level |
| `PO2` | `H1^\infty` | prove cross-sign bulk exactness | keeps `(+,-)` as calibration block | persistent cross-sign bulk residue |
| `PO3` | `H1^\partial` | prove cross-sign boundary cancellation | preserves asymmetry of the sprint | non-cap cross-sign boundary survives |
| `PO4` | `H1^\partial` | identify same-sign boundary term `H_a^{\mathrm{ss}}` | turns `(++)` into a named operator problem | `(++)` has only matrix-fit language and no operator source |
| `PO5` | `H1^\partial` | separate finite cap term `C_a^{\mathrm{cap}}` | isolates the later augmented-cap brick | cap and boundary cannot be separated |
| `PO6` | `H1^f` | show compression adds no extra theorem channel | prevents finite sections from reintroducing mystery defects | a new moving section defect appears after compression |
| `PO7` | `H1^f` | write the final filtered theorem statement | makes `H1` reusable by `H2^f` | theorem still depends on rank/basis language |

## Detailed obligations

### PO1. Tail defect definition

Define

```tex
\mathcal D_{a,N}
:=
S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
-\kappa_{+-}(a)\Delta_N^*Q_\infty\Delta_N.
```

Need:

- blockwise decomposition into `(++),(+-)` and their Hermitian mirrors;
- no finite-section bookkeeping inside this stage.

### PO2. Cross-sign bulk exactness

Need:

```tex
\mathcal D_{a,\mathrm{bulk}}^{+-}=0.
```

Preferred outcome:

```tex
\mathcal D_{a,N}^{+-}=\mathcal C_a^{+-,\mathrm{cap}},
```

with preferred stronger value `\mathcal C_a^{+-,\mathrm{cap}}=0`.

### PO3. Cross-sign boundary cancellation

Need:

```tex
\mathcal D_{a,\partial}^{+-}=0.
```

This is the sharp asymmetry lemma that prevents `(+,-)` from inheriting the
same-sign moving-boundary story.

### PO4. Same-sign boundary identification

Need:

```tex
\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}},
```

with `H_a^{\mathrm{ss}}` explicitly read as boundary / commutator /
Toeplitz-Hankel type.

### PO5. Cap separation

Need:

```tex
\mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}},
```

and clear separation from `H_a^{\mathrm{ss}}`.

### PO6. Compression neutrality

Need finite descent statements:

```tex
E_{a,\mathrm{comp}}^{+-}=0,
\qquad
E_{a,\mathrm{comp}}^{++}=0
```

or fully explicit bookkeeping that is not promoted to theorem content.

### PO7. Final filtered theorem package

Desired endpoint:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_{a,\mathrm{cap}}^{+-},
```

```tex
M^{++}(a)=\kappa_{+-}(a)\widetilde Q^{++}+H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}},
```

with the remaining two blocks obtained by symmetry.

## Minimal lemma order

The current best local order is:

1. `PO1`
2. `PO2`
3. `PO3`
4. `PO4`
5. `PO5`
6. `PO6`
7. `PO7`

This is intentionally asymmetric: the cross-sign block is still the
calibration block, and the same-sign block is attacked only after that
calibration is frozen.

## Handoff to `H2^f`

The entire point of `A4` is to make the post-`H1` interface rigid.

`H2^f` should be allowed to read only this package:

- exact or cap-only cross-sign adapter;
- same-sign boundary term `H_a^{\mathrm{ss}}`;
- finite cap term `C_a^{\mathrm{cap}}`;
- no extra independent compression defect.

If those four items are not isolated, then `H2^f` is still being asked to
consume an unnamed defect cloud rather than a theorem.

## Parallel lane `B` interface

Lane `B` does not change the lemma order above.

Its job is narrower:

- keep one smallest explicit `PSD-pd` finite-block certificate step alive;
- provide a fallback constructive corridor if `H1` later stalls;
- avoid stealing theorem content from lane `A`.

So after `A4` the correct parallel posture is:

- lane `A`: continue with `PO1 -> PO3` as the first real lemma attack;
- lane `B`: continue the smallest explicit certificate block without touching
  the `H1` theorem shape.

## Success criterion for `A4`

This note lands only if it answers:

- what exact lemma must be proven next;
- which stage it belongs to;
- what counts as route-kill;
- how the result will be handed to `H2^f`.

## Non-goals

- do not reopen shared-basis/rank language;
- do not jump straight to augmented-cap positivity;
- do not mix tail-level operator defects with finite-section bookkeeping;
- do not open a new RH route outside `H-bridge` / `PSD-pd`.
