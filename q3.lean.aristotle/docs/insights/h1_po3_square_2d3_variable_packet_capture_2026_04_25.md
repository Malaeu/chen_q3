# `PO3-square.2d3` variable comparable packet capture (2026-04-25)

## Status

Follow-up after the threshold-exhaustive packet split.

The row-error side can now be closed at the correct level by using a
threshold-exhaustive packet `P_k(delta_k)`.  The remaining issue is not another
mirror estimate and not a fixed finite `RowClusterExhaustion` claim.  It is
whether the endpoint-adaptive row equations capture the possibly variable
threshold packet with enough conditioning.

## Verdict

The fastest viable theorem shape is a stable-projection dichotomy.

Stable branch:

```tex
\operatorname{dist}(q_k,\ker V_k)
\le
\frac{\|\varepsilon_k\|}{\sigma_k^+}
\to0.
```

Route-kill branch:

```tex
\frac{\|\varepsilon_k\|}{\sigma_k^+}\not\to0
```

or the kernel of the selected endpoint-row matrix is not the expected
Vandermonde/Hermite line.

Anything weaker hides the actual analytic blocker.

## Abstract stable-capture theorem

Let

```tex
P_k(\delta_k)=\{x_{k,1},\dots,x_{k,n_k}\}
```

be the threshold-exhaustive comparable packet and define normalized packet
coefficients

```tex
q_{k,i}:=
\frac{c_{k,i}A_{I_k}(x_{k,i})}{M_k^\star}.
```

The normalized endpoint-row equations have the form

```tex
V_k q_k=\varepsilon_k,
\qquad
V_{k,p,i}:=\frac{m_{\rho_p}(x_{k,i})}{m_{\rho_p}(\xi_k)}.
```

If `ker V_k = C h_k` and

```tex
\sigma_k^+
:=
\inf_{\substack{u\perp h_k\\ \|u\|_2=1}}
\|V_ku\|_2
>0,
```

then

```tex
\operatorname{dist}_2(q_k,\mathbb C h_k)
\le
\frac{\|\varepsilon_k\|_2}{\sigma_k^+}.
```

The proof is the projection estimate:

```tex
q_k=\Pi_k q_k+(1-\Pi_k)q_k,
\qquad
V_k\Pi_k q_k=0,
```

so

```tex
\sigma_k^+\|(1-\Pi_k)q_k\|_2
\le
\|V_k(1-\Pi_k)q_k\|_2
=
\|V_kq_k\|_2
=
\|\varepsilon_k\|_2.
```

## Norm correction

If only the row-wise sup error is known,

```tex
E_k:=\max_p|\varepsilon_{k,p}|,
```

and there are `r_k` rows, then

```tex
\|\varepsilon_k\|_2\le \sqrt{r_k}\,E_k.
```

Thus the honest condition is

```tex
\frac{\sqrt{r_k}\max_p|\varepsilon_{k,p}|}{\sigma_k^+}\to0.
```

The condition using only `max_p |epsilon| / sigma_k^+` is safe only when
`r_k` is bounded or when the stability is formulated in an
`\ell^\infty`-compatible operator norm.

## Endpoint rows and growing packets

For bounded `n_k`, endpoint rows are viable under the usual separated compact
local-coordinate hypotheses:

```tex
n_k\le n_0,\qquad
\min_{i\ne j}|t_{k,i}-t_{k,j}|\ge c_0>0.
```

Then the endpoint-row matrix converges to a finite Vandermonde block and the
restricted singular gap stays bounded below.

For growing `n_k`, endpoint rows are viable only with an explicit singular-gap
theorem:

```tex
\frac{\sqrt{n_k}\max_p|\varepsilon_{k,p}|}{\sigma_k^+}\to0.
```

Zero-counting gives a size bound, not a conditioning bound.  Vandermonde
matrices may be extremely ill-conditioned as the packet grows.

## Clustered packets and confluent/Hermite limits

Confluent/Hermite limits identify the correct kernel when packet points
cluster.  They do not remove conditioning.

If clustering requires a renormalization `T_k`, the real condition becomes

```tex
\frac{\|T_k\varepsilon_k\|}{\sigma_{\mathrm{conf},k}}\to0.
```

Confluent capture is therefore useful only with bounded cluster multiplicity,
nondegenerate cluster shape, valid derivative/confluent rows, and small
renormalized row errors.

## Lean consumer now frozen

The abstract consumer has been added to
`Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean`:

```text
po3_variable_comparable_packet_capture_of_stable_projection
```

It states the reusable inequality

```tex
\|q-\mathrm{Proj}\,q\|\le C\|\varepsilon\|
```

from the hypotheses

```tex
Vq=\varepsilon,
\qquad
\|x-\mathrm{Proj}\,x\|\le C\|Vx\|.
```

This avoids formalizing singular values immediately.  Analytically,
`C_k = 1 / sigma_k^+`.

## Next target

The next analytic theorem is:

```text
EndpointRowStableProjectionOrRouteKill
```

Either prove a stable projection for the threshold packet:

```tex
C_k\|\varepsilon_k\|\to0,
```

or record a route-kill:

- every admissible threshold packet grows without a singular-gap estimate;
- the endpoint-row matrix has kernel dimension different from one;
- the kernel is not the expected Vandermonde/Hermite line;
- clustered packets require a confluent renormalization whose error is not
  small enough.

This is the sharp live blocker after the row-error split.

## Follow-up selection

The next review selects the fastest branch:

```text
EndpointRowsStableProjection_boundedSeparated
```

Do not start with clustered or growing packets.  First attempt the bounded
packet with separated exponential nodes and endpoint-row convergence to the
rectangular Vandermonde model.  The Lean-facing certificate is now
`PO3EndpointRowBoundedSeparatedStableProjectionCertificate`, with consumer
`po3_endpoint_rows_stable_projection_of_bounded_separated_packet`.  See
`h1_po3_square_2d3_bounded_separated_projection_2026_04_25.md`.
