# `(+,-)` adapter ledger (2026-03-15)

## Status

Day 1 local artifact for the `Q_\zeta`-core short-circuit sprint.

This note is not the proof. It is the deterministic receiver for the first
adapter theorem.

## Frozen target

Work on the already-frozen filtered scale:

```tex
\kappa(a)=\kappa_{+-}(a),
\qquad
\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N},
\qquad
B_{M,N}=S_{a,M,N}^*J_aS_{a,M,N}=\Delta_{M,N}^*\Delta_{M,N}.
```

The first adapter theorem target is:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_a^{+-}.
```

Decision to be made:

- exact case: `E_a^{+-}=0`;
- corrected case: `E_a^{+-}` has explicit boundary/cap form;
- kill case: no stable theorem-grade shape.

## Strongest existing clues

### 1. Old strongest filtered thesis already favored exact `(+,-)`

The old `Main_closure` theorem table still records:

```tex
M^{+-}(a)=\kappa(a)\widetilde Q_{M,N}^{+-}
```

with the explicit remark:

```text
no extra section-boundary defect once \widetilde Q_{M,N} is used.
```

So the current Day 1 target is not invented from zero. It is a sharpened audit
of the old strongest filtered thesis.

### 2. Only `(++),(+-)` are independent

By Hermitian symmetry, `(-+),(--)` are consequences once `(++),(+-)` are
understood.

So the first adapter theorem really can be isolated in `(+,-)` without loss.

### 3. Raw mismatch does not touch the target

The dead raw identity

```tex
w_{rs}(a)=\kappa(a)q_{rs}
```

is irrelevant for the current target except as a warning:
the correct object is the filtered comparison
`\widetilde Q_{M,N}`, not the raw Toeplitz block.

### 4. Current numerics make `(+,-)` the right calibration block

The reset diagnostics consistently say:

- `(+,-)` is much more stable than `(++)`;
- the shared rank story failed globally because of `(++)`, not because of
  `(+,-)`;
- therefore `\kappa(a)` should now be frozen from `(+,-)` rather than fitted
  jointly.

## Local oracle / external sanity-check

Local embedding search confirms:

- `Main_closure.tex` still points to exact `(+,-)` after filtered reformulation;
- `h1_raw_entry_reduction_2026_03_08.md` isolates only `(++),(+-)` as
  independent live blocks;
- `h1_two_sided_filtered_bridge_2026_03_08.md` keeps the exact metric side and
  filtered geometry frozen.

External sanity-check:

- the finite section method and Toeplitz/Hankel finite-section literature treat
  boundary corrections as standard finite-section phenomena rather than as
  evidence of genuine bulk mismatch;
- that supports the project guess that any surviving correction should sit in a
  boundary/cap term, not in a floating basis fit.

## Expected decomposition template

The right bookkeeping split is:

```tex
M^{+-}(a)-\kappa_{+-}(a)\widetilde Q^{+-}
=
H_a^{+-,\partial}
+ C_a^{+-,\mathrm{cap}}
+ E_{a,M,N}^{+-,\mathrm{comp}}.
```

The working expectation is stronger:

```tex
H_a^{+-,\partial}=0,
\qquad
E_{a,M,N}^{+-,\mathrm{comp}}=0,
```

once the comparison object is formulated correctly, leaving either

```tex
E_a^{+-}=0
```

or a very transparent cap term.

## Proof-obligation ledger

### PO1. Freeze the calibration

Treat

```tex
\kappa(a)=\kappa_{+-}(a)
```

as structural and stop re-fitting it through `(++)`.

### PO2. Infinite-tail `(+,-)` defect

Define the cross-sign infinite-tail defect

```tex
\mathcal D_{a,N}^{+-}
:=
S_{a,\infty,N}^{+*}G_g[a]S_{a,\infty,N}^{-}
-\kappa_{+-}(a)\Delta_N^{+*}Q_\infty^{+-}\Delta_N^-.
```

Need:

- either show `\mathcal D_{a,N}^{+-}=0`;
- or identify it explicitly as cap-only.

### PO3. Boundary cancellation lemma

Prove that the same-sign boundary / commutator term does **not** survive in the
cross-sign block, or survives in a much simpler transparent way.

This is the main structural lemma of the adapter.

### PO4. Finite compression lemma

Show that if the infinite-tail block is exact or cap-only, then the finite
section

```tex
M^{+-}(a)-\kappa_{+-}(a)\widetilde Q^{+-}
```

contains no hidden extra moving section defect.

### PO5. Final theorem fork

Conclude one of:

1. exact filtered `(+,-)` identity;
2. explicit corrected filtered `(+,-)` identity with named cap term;
3. route-killing instability.

## What we expect to vanish

Expected cancellations in `(+,-)`:

- same-sign boundary term;
- moving-basis artifact;
- generic prefix-holdout pathology;
- any need for theorem-grade common `(++)` basis language.

## What remains for `(++)`

If the adapter lands, the remaining hard object is cleanly:

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

So the entire residual risk moves where it belongs: same-sign boundary/cap.

## Non-goals

- do not use rank language as theorem content;
- do not reopen the raw identity;
- do not jump to augmented cap positivity before this adapter is classified.
