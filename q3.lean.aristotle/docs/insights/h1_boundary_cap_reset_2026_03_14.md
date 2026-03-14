# H1 boundary/cap reset (2026-03-14)

## Status

This note resets the live `H1^f` question after the rank/basis diagnostics
became too strong as theorem language.

The public route stays

```text
T0-pd -> H-bridge -> H4 -> RH,
```

with `H1^f` as the only serious live blocker.

## What survives the reset

- the two-sided filtered geometry is still the right one;
- the exact metric side is still
  `S_{a,M,N}^*J_aS_{a,M,N}=B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}`;
- the raw identity `w_{rs}(a)=\kappa(a)q_{rs}` stays dead;
- the `(+,-)` block still behaves much more like a stable anchor than `(++ )`.

## What changes

The language

```text
shared rank-3 defect / rank-4 basis / rank-5 basis / rank-6 basis
```

must now be treated as diagnostic only.

It is not the front-door theorem shape anymore.

The right root question is instead:

```tex
D_{a,M,N}
:=
S_{a,M,N}^*G_g[a]S_{a,M,N}
- \kappa(a)\,\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}.
```

What structural class should `D_{a,M,N}` belong to?

## Best current guess

The most plausible class is:

```text
explicit boundary/cap correction,
whose finite-matrix shadow looks like a moving Toeplitz-Hankel /
commutator / near-edge defect.
```

This explains the current numerics better than either:

- genuine bulk mismatch;
- or one fixed shared finite-rank cap-space across `M`.

## Simplified theorem map

The right order is now:

```text
H1^∞  ->  H1^∂  ->  H1^f  ->  H2^f  ->  H3^f  ->  H4^f
```

where:

- `H1^∞`: infinite filtered comparison before finite compression;
- `H1^∂`: isolate explicit boundary/cap term;
- `H1^f`: compress the already identified decomposition to finite tails.

## First algebraic target

Do not start from a new SVD fit.

Start from the infinite-tail defect

```tex
\mathcal D_{a,N}
:=
S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
- \kappa(a)\,\Delta_N^*Q_\infty\Delta_N,
```

and try to prove a decomposition

```tex
\mathcal D_{a,N}=H_{a,N}+C_{a,N},
```

with:

- `H_{a,N}` = explicit short-range boundary / Toeplitz-Hankel /
  commutator term;
- `C_{a,N}` = genuine finite-dimensional cap term.

Then the finite-section defect should become

```tex
D_{a,M,N}=P_{M,N}\mathcal D_{a,N}P_{M,N}+\mathcal E_{a,M,N},
```

where `\mathcal E_{a,M,N}` is only compression bookkeeping.

## Immediate next tasks

1. Test whether the `(+,-)` block satisfies an exact filtered identity after
   the right reformulation.
2. Derive the surviving same-sign boundary term for `(++ )`.
3. Stop treating basis choice as theorem content.

## Kill list

- stop primary work on rank-`4/5/6` scans;
- stop reading pooled in-sample bases as theorem evidence;
- stop trying to revive the shared small-rank theorem shape;
- stop going to cap positivity before the defect is structurally classified.
