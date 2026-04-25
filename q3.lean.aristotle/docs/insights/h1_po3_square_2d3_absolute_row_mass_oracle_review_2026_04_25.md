# `PO3-square.2d3` absolute row-mass Oracle review (2026-04-25)

## Status

Mainline advisory review accepted.  This records the `RH_März_2026` project
review of the live `PO3-square.2d3.absolute-row-mass-control` target.

The review agrees with the local mirror-row audit:

- `AbsoluteRowMassControl` is the right sufficient target for `MirrorRowSmall`;
- it is not automatic from `Y_a={x_gamma,x_gamma-1}` and
  `|c_gamma|=O(gamma^-3)`;
- the missing input is row-stable absolute top-packet isolation.

## Verdict

Viable only with an extra assumption.

The extra assumption is not a new architecture.  It is the exact local
isolation statement needed for the already-selected endpoint-adaptive rows.

## Correct next lemma

The canonical Lean-facing statement should be named:

```text
EndpointRowAbsoluteMassControl_from_packet_isolation
```

The descriptive route address remains:

```text
endpoint_row_absolute_mass_control_of_isolated_edge_packet
```

Let

```tex
A_I(x)=\prod_{j\in I}(x-j)^{-1},
\qquad
B_I(x)=\prod_{j\in I}(x+j)^{-1},
\qquad
m_\rho(x)=A_{I_\rho}(x)/A_{I_k}(x).
```

Let `X=Y_a={x_gamma,x_gamma-1}` with `x_gamma=a gamma/pi`, and assume

```tex
|c_x|\le C(1+x)^{-3}.
```

Let `P_k` be the selected edge-log packet around `xi_k`, and define

```tex
M_k:=\max_{p\in P_k}|c_pA_{I_k}(p)|,
\qquad
D_{k,\rho}:=M_k|m_\rho(\xi_k)|.
```

The corrected target must not control only a named near region unless the
complement is already proved negligible.  For each selected endpoint row
`rho`, choose a row-effective region `E_{k,\rho}` and assume:

1. endpoint-row packet stability, bounded above and below on `P_k`:

```tex
0<c_\rho\le |m_\rho(p)/m_\rho(\xi_k)|\le C_\rho
\qquad (p\in P_k);
```

2. near-region mirror suppression:

```tex
\eta_{k,\rho}:=
\sup_{x\in E_{k,\rho}}
\frac{|B_{I_\rho}(x)|}{|A_{I_\rho}(x)|}
\to 0;
```

3. exterior absolute `A`-mass control inside the row-effective region:

```tex
\sum_{x\in E_{k,\rho}\setminus P_k}|c_xA_{I_\rho}(x)|
=o(D_{k,\rho});
```

equivalently, using `A_{I_\rho}(x)=A_{I_k}(x)m_\rho(x)`,

```tex
\sum_{x\in E_{k,\rho}\setminus P_k}
|c_xA_{I_k}(x)|\,|m_\rho(x)/m_\rho(\xi_k)|
=o(M_k);
```

4. `A`-ineffective tail control:

```tex
\sum_{x\notin E_{k,\rho}}|c_xA_{I_\rho}(x)|
=o(D_{k,\rho});
```

5. far mirror-tail control:

```tex
\sum_{x\notin E_{k,\rho}}|c_xB_{I_\rho}(x)|
=o(D_{k,\rho}).
```

Then:

```tex
\sum_{x\in X\setminus P_k}|c_xA_{I_\rho}(x)|=o(D_{k,\rho}),
```

```tex
\sum_{x\in X}c_xB_{I_\rho}(x)=o(D_{k,\rho}),
```

and hence the normalized row error

```tex
\varepsilon_\rho
=
\frac{\sum_Xc_xB_{I_\rho}(x)-\sum_{X\setminus P_k}c_xA_{I_\rho}(x)}
{M_km_\rho(\xi_k)}
```

tends to zero.

## Proof skeleton

For the `A`-exterior:

```tex
|c_xA_{I_\rho}(x)|
=|m_\rho(\xi_k)|\,
|c_xA_{I_k}(x)|\,|m_\rho(x)/m_\rho(\xi_k)|.
```

The near exterior is `o(D_{k,\rho})` by the isolation assumption, and the far
part is `o(D_{k,\rho})` by the far `A`-tail or by the exhaustive near-region
definition.

For the mirror row:

```tex
\left|\sum_Xc_xB_{I_\rho}(x)\right|
\le
\sum_{X^{near}}|c_xB_{I_\rho}(x)|
+
\sum_{X^{far}}|c_xB_{I_\rho}(x)|.
```

On the near region,

```tex
|B_{I_\rho}(x)|\le \eta_{k,\rho}|A_{I_\rho}(x)|.
```

The packet part is `O(D_{k,\rho})` by top-packet row stability and the
definition of `M_k`; the near exterior is `o(D_{k,\rho})`; multiplying by
`\eta_{k,\rho}->0` gives `o(D_{k,\rho})`.  The far mirror tail is already
`o(D_{k,\rho})`.

## Why this is not automatic

The weak point is exactly

```tex
\sum_{x\in E_{k,\rho}\setminus P_k}
|c_xA_{I_k}(x)|\,|m_\rho(x)/m_\rho(\xi_k)|
=o(M_k).
```

The decay `|c_x|=O(x^{-3})` and unconditional zero counting do not by themselves
isolate one local top packet.  At edge-log scale, local zero density can allow
several support points with comparable coefficient size and comparable
reciprocal-product size.  Endpoint-adaptive Vandermonde rows can capture a
finite comparable packet, but they do not prove that all exterior comparable
absolute mass is absent.

Therefore the top packet must be chosen exhaustively: it must include every
row-effective support point whose normalized contribution is comparable to
`M_k|m_\rho(\xi_k)|`.

The precise local obstruction is a bounded-local-coordinate exterior
competitor.  If there is a sequence `y_k in Y_a \ P_k` such that

```tex
y_k=\xi_k+\frac{t+o(1)}{\Lambda_k(\xi_k)}
\qquad (|t|<\infty),
```

then the endpoint-adaptive local model gives

```tex
\frac{A_{I_\rho}(y_k)}{A_{I_\rho}(\xi_k)}
=\exp(-\alpha_\rho t+o(1)).
```

The decay `|c_\gamma|\lesssim\gamma^{-3}` does not force
`|c_{y_k}|/|c_{\xi_k}| -> 0` on this scale, because the heights are
comparable.  Hence a single exterior point at bounded local coordinate can
contribute a non-vanishing fraction of `D_{k,\rho}`.  This is the exact reason
the estimate cannot be derived from `Y_a` and polynomial coefficient decay
alone.

## Route-kill criterion

The current route is blocked at `PO3-square.2d3.absolute-row-mass-control` if
there exists a required endpoint row `rho`, a subsequence `k_n`, and exterior
support points `y_{k_n}\in Y_a\setminus P_{k_n}` such that

```tex
\Lambda_{k_n}(\xi_{k_n})(y_{k_n}-\xi_{k_n})
```

stays bounded and

```tex
\liminf_{n\to\infty}
\frac{
|c_{y_{k_n}}A_{I_{k_n,\rho}}(y_{k_n})|
}{
M_{k_n}|m_{k_n,\rho}(\xi_{k_n})|
}
>0.
```

Equivalently, the route is blocked if there exists a selected row sequence
`rho_k` and a subsequence `k_n` such that

```tex
\limsup_{n\to\infty}
\frac{
\sum_{x\in E_{k_n,\rho_{k_n}}\setminus P_{k_n}}
|c_xA_{I_{\rho_{k_n}}}(x)|
}{
M_{k_n}|m_{\rho_{k_n}}(\xi_{k_n})|
}
>0.
```

Equivalently, the real transform-side support contains a row-effective
exterior cloud of comparable absolute `A`-mass that is hidden only by signed
cancellation.

There is a separate far-mirror escape channel if

```tex
\limsup_{n\to\infty}
\frac{
\sum_{x\in X^{far}_{k_n,\rho_{k_n}}}
|c_xB_{I_{\rho_{k_n}}}(x)|
}{
M_{k_n}|m_{\rho_{k_n}}(\xi_{k_n})|
}
>0.
```

## Next action

Do not claim `MirrorRowSmall` from shell-level mirror decay.

The next mainline step is:

```text
PO3-square.2d3.isolated-edge-packet
```

Define the row-effective top packet exhaustively for each endpoint-adaptive
row family, then prove the isolation statement above or record the exterior
cloud as the precise route-kill obstruction.
