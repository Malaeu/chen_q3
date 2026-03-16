# `PO1` tail-defect attack (2026-03-16)

## Status

First active theorem-phase artifact after the closed `Q_\zeta`-core sprint.

This note is the receiver for the first real `H1` attack packet:

```tex
PO1a \to PO1b.
```

## Why this is next

After the sprint decision, the next honest move is no longer another
coordination pass.

The whole route now depends on writing one exact tail object cleanly before
arguing about cancellations:

```tex
\mathcal D_{a,N}
:=
S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
-\kappa_{+-}(a)\Delta_N^*Q_\infty\Delta_N.
```

If this object is not frozen cleanly, every later statement about cross-sign
exactness or same-sign boundary structure remains too verbal.

## Exact target

The first theorem packet should produce:

### PO1a. Tail defect definition

```tex
\mathcal D_{a,N}
:=
S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
-\kappa_{+-}(a)\Delta_N^*Q_\infty\Delta_N.
```

### PO1b. Blockwise split

```tex
\mathcal D_{a,N}
=
\begin{pmatrix}
\mathcal D_{a,N}^{++} & \mathcal D_{a,N}^{+-} \\
\mathcal D_{a,N}^{-+} & \mathcal D_{a,N}^{--}
\end{pmatrix},
```

with

```tex
\mathcal D_{a,N}^{--}=\overline{\mathcal D_{a,N}^{++}}^{\,T},
\qquad
\mathcal D_{a,N}^{-+}=\overline{\mathcal D_{a,N}^{+-}}^{\,T}.
```

So the live work immediately reduces again to `(++),(+-)`.

## Exact source anchors already frozen

The new tail note should not float independently of the existing manuscript.
Its input is already fixed in three places:

- `Main_closure.tex` defines the finite two-sided tail package
  `\mathcal P_{M,N}`, `\Delta_{M,N}`, `B_{M,N}`, `\widetilde Q_{M,N}`,
  `\phi_n^\pm[a]`, `S_{a,M,N}` and the exact pullback
  `S_{a,M,N}^*J_aS_{a,M,N}=B_{M,N}`;
- the same file already freezes the finite filtered classifier picture
  `M^{\sigma\tau}(a)=\kappa(a)\widetilde Q_{M,N}^{\sigma\tau}+F_a^{\sigma\tau}`;
- `H2^f` already defines the closed tail space
  `V_a^{\mathrm{tail}}
   = \overline{\bigcup_{M>N_a}S_{a,M,N_a}\mathcal P_{M,N_a}}^{L^2(-a,a)}`.

So `PO1` is not inventing a new bridge. It is only lifting the already frozen
finite filtered package to one exact tail-level defect object.

## Minimal notation freeze for `PO1`

For fixed `a>0` and `N\ge 0`, introduce the algebraic two-sided tail model
space

```tex
\mathcal P_{\infty,N}^{\mathrm{alg}}
:=
\operatorname{span}\{z^n,z^{-n}: n>N\}.
```

Define the algebraic filtered shift by

```tex
\Delta_N z^n = z^n+z^{n+1},
\qquad
\Delta_N z^{-n}=z^{-n}+z^{-(n+1)}
\qquad (n>N).
```

Define the tail synthesis on basis vectors by

```tex
S_{a,\infty,N} z^n=\phi_n^+[a],
\qquad
S_{a,\infty,N} z^{-n}=\phi_n^-[a],
```

where

```tex
\phi_n^+[a]=\chi_{n,n+1}[a],
\qquad
\phi_n^-[a]=\chi_{-n,-(n+1)}[a].
```

The comparison object `Q_\infty` should be read as the infinite tail operator
whose finite sections recover `\widetilde Q_{M,N}` after restriction to
`\mathcal P_{M,N}`. In other words: `PO1` does not need an independent new
prime-side construction; it only needs a stable tail receiver compatible with
the already frozen finite filtered sections.

## Exact theorem-shaped packet

The next theorem attempt should be writable literally as the following pair.

### PO1a. Tail defect is well defined

For fixed `a>0` and `N\ge 0`, the sesquilinear form

```tex
\mathcal D_{a,N}(u,v)
:=
\langle G_g[a]S_{a,\infty,N}u,S_{a,\infty,N}v\rangle
-\kappa_{+-}(a)\langle Q_\infty\Delta_Nu,\Delta_Nv\rangle
```

is well defined on `\mathcal P_{\infty,N}^{\mathrm{alg}}`, and therefore
defines the tail defect operator/form

```tex
\mathcal D_{a,N}
:=
S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
-\kappa_{+-}(a)\Delta_N^*Q_\infty\Delta_N.
```

This is the exact point where the theorem phase stops talking about “the H1
defect” verbally and starts naming one concrete operator object.

### PO1b. Tail defect splits into two live blocks

Let

```tex
\mathcal P_{\infty,N}^{\mathrm{alg}}
=
\mathcal P_{\infty,N}^{+,\mathrm{alg}}
\oplus
\mathcal P_{\infty,N}^{-,\mathrm{alg}},
```

with

```tex
\mathcal P_{\infty,N}^{+,\mathrm{alg}}
:=
\operatorname{span}\{z^n:n>N\},
\qquad
\mathcal P_{\infty,N}^{-,\mathrm{alg}}
:=
\operatorname{span}\{z^{-n}:n>N\}.
```

Then

```tex
\mathcal D_{a,N}
=
\begin{pmatrix}
\mathcal D_{a,N}^{++} & \mathcal D_{a,N}^{+-} \\
\mathcal D_{a,N}^{-+} & \mathcal D_{a,N}^{--}
\end{pmatrix},
```

where

```tex
\mathcal D_{a,N}^{\sigma\tau}
:=
P_\sigma \mathcal D_{a,N} P_\tau,
\qquad
\sigma,\tau\in\{+,-\}.
```

Because `G_g[a]` and `Q_\infty` are Hermitian/self-adjoint comparison objects,
the remaining blocks are recovered by

```tex
\mathcal D_{a,N}^{--}=\overline{\mathcal D_{a,N}^{++}}^{\,T},
\qquad
\mathcal D_{a,N}^{-+}=\overline{\mathcal D_{a,N}^{+-}}^{\,T}.
```

So the live direct attack really does reduce to the two blocks `(++),(+-)`.

## Frozen input from the sprint

Cross-sign target:

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

## Required bookkeeping

The note must keep three levels separate:

1. infinite-tail operator object `\mathcal D_{a,N}`;
2. blockwise decomposition into `(++),(+-)` plus Hermitian mirrors;
3. later finite-section shadow
   ```tex
   E_a^{\sigma\tau}
   =
   P_{M,N}\mathcal D_{a,N}^{\sigma\tau}P_{M,N}
   + E_{a,\mathrm{comp}}^{\sigma\tau}.
   ```

Level 3 is not part of `PO1` itself. It is only recorded so the tail note does
not silently mix operator and finite-section language.

## What must be explicit

- what space `S_{a,\infty,N}` maps from and to;
- what `Q_\infty` means as the infinite filtered comparison object;
- how the four sign blocks are extracted;
- where Hermitian symmetry enters.

## First finite-shadow interface

`PO1` is still tail-level only, but it should already pin down how finite
sections are recovered later. The intended rule is:

```tex
P_{M,N}\mathcal D_{a,N}^{\sigma\tau}P_{M,N}
\rightsquigarrow
M^{\sigma\tau}(a)-\kappa_{+-}(a)\widetilde Q_{M,N}^{\sigma\tau},
```

with any extra term forced into explicit compression bookkeeping. This is the
bridge from `PO1` to `PO6`, but it must not be used inside the proof of
`PO1a/PO1b` itself.

## What must not happen

- no rank/basis language;
- no finite-section compression arguments inside `PO1`;
- no premature claims about cancellation;
- no mixing of cap identification with the bare definition lemma.

## Immediate next packet after `PO1`

If `PO1a/PO1b` land cleanly, the next packet is forced:

1. `PO2`: cross-sign bulk exactness;
2. `PO3`: cross-sign boundary cancellation.

Only after that does the route spend proof energy on the same-sign boundary
term `H_a^{\mathrm{ss}}`.

## Success criterion

This note lands only if the next theorem attempt can be written as:

- one exact definition lemma for `\mathcal D_{a,N}`;
- one exact block-splitting lemma with Hermitian mirrors.

## Immediate next receiver

If `PO1a/PO1b` are accepted in this form, the next local theorem packet is no
longer ambiguous:

1. prove `PO2` as cross-sign bulk exactness on `\mathcal D_{a,N}^{+-}`;
2. prove `PO3` as cross-sign boundary cancellation on the same block;
3. only then pass proof energy to the same-sign channel.
