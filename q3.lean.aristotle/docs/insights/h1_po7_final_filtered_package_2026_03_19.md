# `PO7` final filtered theorem package (2026-03-19)

## Status

Direct successor to `P6` in lane `A`.

`P6` already froze compression as bookkeeping-only:

```tex
D_{a,M,N}
=
P_{M,N}\mathcal D_{a,N}P_{M,N}+\mathcal E_{a,M,N},
```

with no new theorem-shaped channel allowed after finite descent.

So the next honest question is no longer structural classification but final
packaging:

```tex
\text{can } H1^f \text{ now be written as one clean filtered theorem?}
```

## Exact target

The desired endpoint is the final filtered package:

```tex
\textbf{PO7a.}\qquad
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_{a,\mathrm{cap}}^{+-},
```

```tex
\textbf{PO7b.}\qquad
M^{++}(a)=\kappa_{+-}(a)\widetilde Q^{++}+H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}},
```

with the remaining two blocks obtained by Hermitian symmetry.

## Why this is next

After `P6`, every live piece of `H1` has already been named:

- mixed block calibrated;
- same-sign boundary identified;
- cap separated;
- compression demoted to bookkeeping.

So `PO7` should not discover new structure. It should package the already-won
structure into the final theorem-ready form of `H1^f`.

## Best existing support

### 1. The proof-obligation table already names the endpoint

`docs/insights/h1_proof_obligation_table_2026_03_16.md` already freezes the
final package in exactly this form.

### 2. The previous gates already determine the pieces

- `P3` fixed the mixed-block cancellation posture;
- `P4` fixed `H_a^{\mathrm{ss}}`;
- `P5` fixed `C_a^{\mathrm{cap}}`;
- `P6` fixed compression neutrality.

So `PO7` is packaging, not a new search.

## Proof-facing packet

### PO7.1. Mixed block line

Keep the mixed block in the exact Door-1 language:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_{a,\mathrm{cap}}^{+-}.
```

No boundary language should leak back into this line.

### PO7.2. Same-sign line

Keep the same-sign line in the exact Door-2 language:

```tex
M^{++}(a)=\kappa_{+-}(a)\widetilde Q^{++}+H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

No third channel is allowed.

### PO7.3. Symmetry closure

The remaining blocks should be obtained by symmetry, not by separate theorem
search:

```tex
(-+) \text{ and } (--)\quad \text{by Hermitian symmetry.}
```

## Route-kill condition

`PO7` fails if final packaging reopens any earlier gate:

- mixed block gets a new boundary term;
- same-sign line gets a third channel;
- compression is promoted back into theorem content;
- notation starts floating again.

Operationally:

```text
if final packaging reintroduces structure that earlier gates already killed,
then H1^f is not actually closed.
```

## What `PO7` must not do

- no reopening of Door 1;
- no reopening of Door 2;
- no reopening of Door 3;
- no augmented-cap positivity;
- no new architecture.

## Handoff after `PO7`

If `PO7` lands, the next honest move is no longer inside `H1`.
It is the upper route:

```tex
H1^f \to H2^f \to H3^f \to H4^f.
```

## Success criterion

This note lands only if the next theorem attempt is not “what remains inside
`H1`?”, but simply the upper bridge continuation beyond `H1^f`.
