# `PO3-square.2d3` threshold-exhaustive packet split (2026-04-25)

## Status

Mainline correction after the `RH_Maerz_2026` review of the
`RowClusterExhaustion` target.

The fixed finite-packet form of `RowClusterExhaustion` is not the right
unconditional theorem shape.  With only the structured support

```tex
Y_a=\{x_\gamma,x_\gamma-1\},\qquad x_\gamma=a\gamma/\pi,
```

and coefficient decay `|c_gamma|=O(gamma^-3)`, zero-counting gives at most
`O(log xi_k)` local support density.  It does not force a fixed finite packet
to contain every comparable endpoint-row contribution.

The correct next split is:

1. close row errors by replacing the fixed finite packet with a
   threshold-exhaustive comparable packet;
2. treat packet capture itself as the next honest blocker, because the packet
   may grow or become ill-conditioned.

## Verdict

The finite packet route survives only as a stable bounded-packet branch.

The unconditional target should now be the thresholded/dichotomy form:

```text
ThresholdExhaustivePacketRowError
  -> VariableComparablePacketCapture
  -> either stable Vandermonde/Hermite capture, or route-kill.
```

This keeps the already-frozen `EndpointRowLogMassMirrorControl` consumer and
removes the false claim that a preselected finite `P_k` is exhaustive from
zero-counting alone.

## Definitions

Let `R_k` be the selected endpoint-adaptive row family and let `E_k` be a
row-effective support region satisfying the zero-counting size bound

```tex
\#(E_k\cap Y_a)\le C\log(2+\xi_k).
```

For a base row `I_k` and an endpoint-adaptive row `I_{k,\rho}`, write

```tex
m_\rho(x):=\frac{A_{I_{k,\rho}}(x)}{A_{I_k}(x)}.
```

Define the row-effective maximum

```tex
M_k^*:=\max_{y\in E_k}|c_yA_{I_k}(y)|
```

and the row scale

```tex
D_{k,\rho}:=M_k^*|m_\rho(\xi_k)|.
```

Choose a threshold `\delta_k>0` with

```tex
\delta_k\log(2+\xi_k)\to0.
```

The threshold-exhaustive comparable packet is

```tex
P_k(\delta_k):=
\left\{
y\in E_k:
\max_{\rho\in R_k}
\frac{|c_yA_{I_{k,\rho}}(y)|}
     {M_k^*|m_\rho(\xi_k)|}
\ge \delta_k
\right\}.
```

By definition, `P_k(delta_k)` contains every support point in the
row-effective region whose normalized endpoint-row contribution is larger than
the threshold.

## Theorem target 1: threshold row error

```text
ThresholdExhaustivePacketRowError
```

For every selected endpoint row `rho`,

```tex
\sum_{y\in E_k\setminus P_k(\delta_k)}
|c_yA_{I_{k,\rho}}(y)|
= o(D_{k,\rho}).
```

Proof skeleton:

- every omitted point contributes `< delta_k D_{k,\rho}` in the selected row;
- there are at most `C log(2+xi_k)` row-effective points;
- therefore

```tex
\sum_{y\in E_k\setminus P_k(\delta_k)}
|c_yA_{I_{k,\rho}}(y)|
\le
C\,\delta_k\log(2+\xi_k)\,D_{k,\rho}
=o(D_{k,\rho}).
```

This is the correct replacement for the false fixed-packet
`RowClusterExhaustion` target.

## Mirror side

The existing log-loss mirror split remains valid.

If

```tex
\eta_{k,\rho}\log(2+\xi_k)\to0
```

and the far mirror tail is `o(D_{k,\rho})`, then
`EndpointRowLogMassMirrorControl` gives

```tex
\sum_{y\in X}c_yB_{I_{k,\rho}}(y)=o(D_{k,\rho}).
```

Together with `ThresholdExhaustivePacketRowError`, this closes the normalized
row-error estimate for the threshold packet:

```tex
\varepsilon_{k,\rho}:=
\frac{
\sum_X c_yB_{I_{k,\rho}}(y)
-
\sum_{X\setminus P_k(\delta_k)}c_yA_{I_{k,\rho}}(y)
}
{M_k^*m_\rho(\xi_k)}
\to0.
```

## Theorem target 2: variable comparable packet capture

```text
VariableComparablePacketCapture
```

Let

```tex
n_k:=|P_k(\delta_k)|.
```

If `n_k` stays bounded and the local coordinates remain separated, the old
finite Vandermonde/Hermite capture branch can be used.

If `n_k` grows, or if the local coordinates cluster, fixed finite capture is
not available automatically.  The honest target is a quantitative conditioning
criterion.

Choose rows `rho_0,...,rho_{n_k-2}` and define

```tex
V_{k,p,i}:=
\frac{m_{\rho_p}(x_{k,i})}{m_{\rho_p}(\xi_k)},
\qquad x_{k,i}\in P_k(\delta_k).
```

The packet coefficients can be captured only if the nonzero singular scale of
`V_k` dominates the normalized row errors:

```tex
\sigma_{\min}^{+}(V_k)^{-1}\max_p|\varepsilon_{k,\rho_p}|\to0.
```

Under this assumption the normalized packet vector is forced into the
approximate one-dimensional kernel of the endpoint-row matrix.  Without it,
the current finite-packet proof has no legitimate Hermite/residue landing.

## Route-kill criteria

Kill the fixed finite adaptive Vandermonde route if, for every admissible
threshold `\delta_k` with

```tex
\delta_k\log(2+\xi_k)\to0,
```

the comparable packet size satisfies

```tex
|P_k(\delta_k)|\to\infty.
```

Also kill the stable packet-capture branch if the conditioning criterion fails:

```tex
\sigma_{\min}^{+}(V_k)
\not\gg
\max_p|\varepsilon_{k,\rho_p}|.
```

Mathematically, this says that the real transform-side support creates a
growing or ill-conditioned comparable cluster.  In that case the previous
fixed finite Vandermonde/Hermite capture is not a proof of `PO3-square.2d3`.

## Mainline consequence

The next mainline task is not to prove fixed-packet `RowClusterExhaustion`.
It is:

```text
close row errors with threshold-exhaustive packets;
then decide VariableComparablePacketCapture.
```

This is now the sharp `PO3-square.2d3` blocker.  Once the stable branch is
proved, it feeds the existing `PO3SquareTransformPacketCertificate` landing
surface.  If the variable packet branch is growing or ill-conditioned, that is
the route obstruction to record.
