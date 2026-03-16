# `(++)` boundary inventory (2026-03-15)

## Status

Day 3 active artifact for the `Q_\zeta`-core short-circuit sprint.

This note starts only after the `(+,-)` cancellation ledger is made
theorem-ready. Its role is to inventory what can still survive in the same-sign
block once the cross-sign block is treated as exact or explicitly corrected.

The current preferred Day 2 outcome is already sharper than “generic corrected
cross-sign identity”:

- cross-sign bulk should be exact;
- cross-sign boundary should cancel;
- cross-sign compression should vanish;
- only a cap-only fallback remains admissible on the `(+,-)` side.

## Frozen theorem target

The next theorem attempt should already be phrased in filtered form:

```tex
M^{++}(a)=\kappa_{+-}(a)\widetilde Q^{++}+E_a^{++}.
```

The purpose of this note is to determine which pieces of `E_a^{++}` are
admissible theorem content and which pieces would kill the current route.

## Frozen contrast

The note begins from the contrast fixed at the end of `A2`:

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

The working assumption is not that this formula is already proven, but that it
is now the correct receiver for the next theorem attempt.

## Purpose

The inventory must answer only this:

- which channels can survive in `(++)` after `(+,-)` is calibrated;
- which of those channels are genuinely operator-theoretic;
- which are only finite compression shadows;
- which observed numerical pathologies are explained automatically once the
  surviving channels are named.

## Two-layer defect split

At the infinite-tail level, define the same-sign defect

```tex
\mathcal D_{a,N}^{++}
:=
S_{a,\infty,N}^{+*}G_g[a]S_{a,\infty,N}^{+}
-\kappa_{+-}(a)\Delta_N^{+*}Q_\infty^{++}\Delta_N^+.
```

The inventory target is

```tex
\mathcal D_{a,N}^{++}
=
\mathcal D_{a,\partial}^{++}
+ \mathcal D_{a,\mathrm{cap}}^{++}
+ \mathcal D_{a,\mathrm{bulk}}^{++},
```

with the expectation that only the first two channels should remain live.

At the finite-section level, the bookkeeping split should read

```tex
E_a^{++}
=
P_{M,N}\mathcal D_{a,N}^{++}P_{M,N}
+ E_{a,\mathrm{comp}}^{++}.
```

So the same-sign theorem is only clean if it distinguishes:

- true operator content inherited from `\mathcal D_{a,N}^{++}`;
- pure finite-section bookkeeping carried by `E_{a,\mathrm{comp}}^{++}`.

## Working decomposition

Equivalently, at the finite level:

```tex
E_a^{++}
=
E_{a,\partial}^{++}
+ E_{a,\mathrm{cap}}^{++}
+ E_{a,\mathrm{bulk}}^{++}
+ E_{a,\mathrm{comp}}^{++}.
```

The intended theorem picture is that the first two channels may remain live,
while the last two must be excluded or reduced to explicit bookkeeping.

## Current expected survive / vanish table

| Channel | Structural meaning | Expected status in `(++)` | What kills the picture |
| --- | --- | --- | --- |
| `\mathcal D_{a,\partial}^{++}` | same-sign boundary / commutator / Toeplitz-Hankel channel | allowed to survive, but only as a named operator `H_a^{\mathrm{ss}}` | unnamed moving residue with no operator source |
| `\mathcal D_{a,\mathrm{cap}}^{++}` | finite Suzuki cap channel | allowed to survive as explicit finite block `C_a^{\mathrm{cap}}` | drifting matrix-fit term that does not stabilize as cap |
| `\mathcal D_{a,\mathrm{bulk}}^{++}` | genuine filtered bulk mismatch | should vanish | any persistent nonzero bulk residue |
| `E_{a,\mathrm{comp}}^{++}` | pure finite-section bookkeeping | should vanish or become fully explicit | independent theorem-shaped section defect after filtered reformulation |

## Candidate surviving channels

### 1. Same-sign boundary / commutator channel

Main guess:

```tex
\mathcal D_{a,\partial}^{++}\neq 0.
```

Expected form:

- Toeplitz-Hankel correction;
- commutator with the cutoff / shift;
- short-range near-edge term rather than global bulk deformation.

This is the main new object of `A3`. If it exists, it should explain why
family-specific low-rank shadows look good in-sample but break under honest
prefix transfer across `M`.

### 2. Finite Suzuki cap channel

Main guess:

```tex
\mathcal D_{a,\mathrm{cap}}^{++}\neq 0
```

but finite-dimensional and stable once the cutoff `N` is fixed.

This is the channel that should feed the later augmented-cap theorem rather
than being mistaken for a floating matrix-fit defect.

This term is allowed to coexist with `H_a^{\mathrm{ss}}`; the live theorem
shape does not require choosing one survivor in place of the other.

### 3. Genuine bulk mismatch

Working expectation:

```tex
\mathcal D_{a,\mathrm{bulk}}^{++}=0.
```

If this term survives as a true unnamed bulk residue, then the present
boundary/cap theorem picture is probably wrong.

### 4. Pure compression term

Working expectation:

```tex
E_{a,\mathrm{comp}}^{++}=0
```

or at least fully explicit after the filtered comparison object is written
correctly.

This term is not allowed to become the main theorem content.

## Why `(++)` is the right place for the surviving channel

Current diagnostics already point here:

- low-mode story is dead;
- shared global rank-3 theorem-shape is dead;
- pooled in-sample basis signals can look good;
- honest prefix holdout across `M` fails badly;
- `(+,-)` is the stable anchor.

This is exactly the phenotype expected from a moving near-edge correction in
the same-sign block, not from a universal low-rank cap basis.

## Current explanatory map

The point of the same-sign inventory is not merely to allow a correction.
It is to explain the entire current numerical story with one operator picture:

- if `H_a^{\mathrm{ss}}` survives, then low-rank shadows in fixed `M` are no
  longer mysterious;
- if `H_a^{\mathrm{ss}}` is short-range and tied to the cutoff geometry, then
  failed prefix transfer across `M` is exactly what one should expect;
- if `C_a^{\mathrm{cap}}` is finite-dimensional, then the later augmented-cap
  theorem becomes a clean second brick rather than a rescue hack.

## Inventory table

| Channel | Expected status in `(++)` | Meaning if it survives |
| --- | --- | --- |
| `\mathcal D_{a,\partial}^{++}` | likely survives | genuine same-sign boundary / commutator term |
| `\mathcal D_{a,\mathrm{cap}}^{++}` | may survive | finite Suzuki cap correction |
| `\mathcal D_{a,\mathrm{bulk}}^{++}` | should vanish | route-kill if it survives unnamed |
| `E_{a,\mathrm{comp}}^{++}` | should vanish or become explicit | bookkeeping only, not theorem content |

## Candidate sublemmas

### SS1. Same-sign boundary identification

Show that the surviving correction in `(++)` has a named operator form.

Target output:

```tex
\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}.
```

### SS2. Cap separation

Separate the finite cap channel from the same-sign boundary channel.

Target output:

```tex
\mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}.
```

### SS3. Bulk exclusion

Show that the residual term is not a genuine bulk mismatch.

Target output:

```tex
\mathcal D_{a,\mathrm{bulk}}^{++}=0.
```

### SS4. Compression bookkeeping lemma

Show that finite sections do not introduce a fake moving theorem channel beyond
the already named operator terms.

Target output:

```tex
E_{a,\mathrm{comp}}^{++}=0
```

or a fully explicit bookkeeping term that is not promoted to theorem content.

### SS5. Final same-sign fork

Conclude one of:

1. exact same-sign filtered identity;
2. explicit same-sign boundary-plus-cap identity;
3. named obstruction that kills the boundary/cap theorem picture.

## Theorem fork

### Strong exact case

```tex
\mathcal D_{a,\partial}^{++}
=
\mathcal D_{a,\mathrm{cap}}^{++}
=
\mathcal D_{a,\mathrm{bulk}}^{++}
=
E_{a,\mathrm{comp}}^{++}
=0.
```

This is allowed, but it is not the live expectation.

### Preferred live case

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}},
```

with

- `H_a^{\mathrm{ss}}` = named same-sign boundary / commutator /
  Toeplitz-Hankel operator;
- `C_a^{\mathrm{cap}}` = explicit finite Suzuki cap term;
- no extra bulk residue;
- no extra independent compression defect.

### Bad case

Any remainder that:

- behaves like genuine bulk mismatch;
- moves with `M` but cannot be tied to a named boundary operator;
- or survives as a third independent theorem channel beyond boundary/cap.

## Success criterion for `A3`

This note lands only if it makes the next theorem attempt unambiguous:

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}
```

with a clear meaning for both summands and a clear rejection criterion for any
extra unnamed residue.

## Handoff to `A4`

If `A3` lands, then `A4` should no longer talk about basis choice at all.
It should talk only about the proof obligations needed to derive:

```tex
H1^\infty \to H1^\partial \to H1^f
```

with:

- `H1^\infty`: identify the tail defect;
- `H1^\partial`: isolate `H_a^{\mathrm{ss}}` and `C_a^{\mathrm{cap}}`;
- `H1^f`: descend to finite sections with no extra mystery term.

## Non-goals

- do not reopen rank/basis hunting;
- do not refit `\kappa(a)` using `(++)`;
- do not jump to augmented cap positivity yet;
- do not treat finite matrix shadows as theorem content.
