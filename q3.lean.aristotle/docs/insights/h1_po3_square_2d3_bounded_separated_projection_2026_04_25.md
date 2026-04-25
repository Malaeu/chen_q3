# `PO3-square.2d3` bounded-separated stable projection (2026-04-25)

## Status

This note freezes the fastest viable branch after the variable-packet capture
review.

The current `PO3-square.2d3` packet chain is:

```text
threshold-exhaustive packet
  -> row errors small
  -> stable projection capture
  -> bounded-separated endpoint-row theorem, or route-kill.
```

## Verdict

The next theorem to attempt is:

```text
EndpointRowsStableProjection_boundedSeparated
```

This is the only branch that can close the current stable-projection blocker
without new spacing/no-resonance assumptions and without a new architecture.

Clustered bounded packets are a conditional fallback.  Growing packets are a
route-kill unless a separate quantitative singular-gap theorem is proved.

## Theorem target

Let

```tex
P_k(\delta_k)=\{x_{k,1},\dots,x_{k,n_k}\},
\qquad n_k\le n_0.
```

Define local coordinates by

```tex
t_{k,i}:=\Lambda_k(\xi_k)(x_{k,i}-\xi_k).
```

The endpoint-row product limit is orientation-sensitive.  With row slopes
`alpha_p`, the row model is

```tex
V_{k,p,i}\to e^{-\alpha_p t_{k,i}}.
```

For left-edge upper extensions usually `alpha_p=p`, so the nodes are
`e^{-t_{k,i}}`.  For right-edge later-base lower truncations usually
`alpha_p=-p`, so the nodes are `e^{t_{k,i}}`.  Both are valid Vandermonde
systems.

Assume the corresponding exponential nodes are bounded and separated.

Choose rows `rho_{k,0},...,rho_{k,n_k-2}` and define

```tex
V_{k,p,i}:=
\frac{m_{\rho_{k,p}}(x_{k,i})}{m_{\rho_{k,p}}(\xi_k)}.
```

The endpoint-row asymptotic target is

```tex
\max_{p,i}|V_{k,p,i}-e^{-\alpha_p t_{k,i}}|\to0.
```

Then the rectangular Vandermonde matrix

with rows `e^{-\alpha_p t_i}`.  In the standard left-edge case this is
`W_{k,p,i}=z_{k,i}^p` with `z_{k,i}=e^{-t_{k,i}}`; in the right-edge
later-base truncation case it is the same Vandermonde form with
`z_{k,i}=e^{t_{k,i}}`.

has rank `n_k-1` and a one-dimensional finite-difference kernel.  A generator
is

```tex
h_{k,i}^{VdM}:=
\frac{1}{\prod_{j\ne i}(z_{k,i}-z_{k,j})}.
```

Because `n_k <= n_0` and the nodes remain in a compact separated class, the
smallest nonzero singular value of `W_k` has a uniform positive lower bound.
The perturbation `V_k-W_k -> 0` gives the stable projection estimate

```tex
\|u-\Pi_k u\|_2\le C_*\|V_ku\|_2
```

for all large `k`, where `Pi_k` is projection onto `ker V_k`.

For the row equation

```tex
V_k q_k=\varepsilon_k
```

the frozen stable-projection consumer gives

```tex
\operatorname{dist}(q_k,\ker V_k)
\le
C_*\|\varepsilon_k\|_2
\to0.
```

Since `n_k <= n_0`, the row sup-error also suffices:

```tex
\|\varepsilon_k\|_2\le\sqrt{n_0}\max_p|\varepsilon_{k,p}|.
```

## Endpoint-row asymptotic sublemma

The real Gamma/product work in this branch is the uniform row limit

```tex
\frac{m_{\rho_{k,p}}(\xi_k+t/\Lambda_k(\xi_k))}
     {m_{\rho_{k,p}}(\xi_k)}
\to e^{-\alpha_p t}
```

uniformly for

```tex
0\le p\le n_0-2,\qquad t\in K
```

with `K` compact.

The proof should use the log expansion

```tex
\log
\frac{m_{\rho_{k,p}}(\xi_k+t/\Lambda_k)}
     {m_{\rho_{k,p}}(\xi_k)}
=
-\frac{t}{\Lambda_k}\Theta_{k,p}(\xi_k)
+
O\left(
\frac{|t|^2}{|\Lambda_k|^2}S_{k,p}(\xi_k)
\right),
```

where

```tex
\Theta_{k,p}(\xi_k)=-\partial_x\log m_{\rho_{k,p}}(\xi_k).
```

Endpoint-adaptive row choice must give

```tex
\Theta_{k,p}(\xi_k)/\Lambda_k(\xi_k)\to\alpha_p,
```

and the second-order term must be `o(1)` uniformly for bounded
`p <= n_0-2`.

## Clustered fallback

If `n_k` is bounded but the nodes cluster, the ordinary Vandermonde gap
collapses.  Then the fallback target is confluent/Hermite:

```tex
T_kV_k\to W_k^{conf}.
```

Capture requires

```tex
C_{conf}\|T_k\varepsilon_k\|\to0.
```

For a cluster of multiplicity `m` and scale `h_k`, a typical sufficient
condition is

```tex
h_k^{-(m-1)}\|\varepsilon_k\|\to0.
```

Confluence identifies the right kernel but amplifies row errors; it does not
remove conditioning.

## Growing-packet route-kill

If

```tex
n_k\to\infty,
```

the endpoint rows do not automatically give useful conditioning.  Even
`n_k=O(log xi_k)` is not enough.  The necessary condition is

```tex
\frac{\sqrt{n_k}\max_p|\varepsilon_{k,p}|}{\sigma_k^+}\to0.
```

Without an explicit lower singular-gap theorem, the growing-packet branch is
a route-kill for the current finite/Hermite capture proof.

## Lean consumer now frozen

The bounded-separated branch now has a Lean-facing certificate wrapper in
`Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean`:

```text
PO3EndpointRowBoundedSeparatedStableProjectionCertificate
```

and consumer theorem:

```text
po3_endpoint_rows_stable_projection_of_bounded_separated_packet
```

The record stores the proof-facing assumptions:

- bounded packet;
- separated exponential nodes;
- endpoint rows converge to the Vandermonde model;
- stable projection estimate.

The next analytic proof must supply this certificate for the real endpoint
rows, using the orientation-safe product asymptotic
`po3_endpoint_row_multiplier_uniform_asymptotic_of_theta_slope`, or route-kill
by one of the obstructions above.
