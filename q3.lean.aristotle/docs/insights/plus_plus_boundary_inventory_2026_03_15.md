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

## Working decomposition

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
D_a^{++}
=
P_{M,N}\mathcal D_{a,N}^{++}P_{M,N}
+ E_{a,\mathrm{comp}}^{++}.
```

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

### 2. Finite Suzuki cap channel

Main guess:

```tex
\mathcal D_{a,\mathrm{cap}}^{++}\neq 0
```

but finite-dimensional and stable once the cutoff `N` is fixed.

This is the channel that should feed the later augmented-cap theorem rather
than being mistaken for a floating matrix-fit defect.

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

## Why `(++)` is the right place for the surviving channel

Current diagnostics already point here:

- low-mode story is dead;
- shared global rank-3 theorem-shape is dead;
- pooled in-sample basis signals can look good;
- honest prefix holdout across `M` fails badly;
- `(+,-)` is the stable anchor.

This is exactly the phenotype expected from a moving near-edge correction in
the same-sign block, not from a universal low-rank cap basis.

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

### SS2. Cap separation

Separate the finite cap channel from the same-sign boundary channel.

### SS3. Bulk exclusion

Show that the residual term is not a genuine bulk mismatch.

### SS4. Compression bookkeeping lemma

Show that finite sections do not introduce a fake moving theorem channel beyond
the already named operator terms.

## Success criterion for `A3`

This note lands only if it makes the next theorem attempt unambiguous:

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}
```

with a clear meaning for both summands and a clear rejection criterion for any
extra unnamed residue.

## Non-goals

- do not reopen rank/basis hunting;
- do not refit `\kappa(a)` using `(++)`;
- do not jump to augmented cap positivity yet;
- do not treat finite matrix shadows as theorem content.
