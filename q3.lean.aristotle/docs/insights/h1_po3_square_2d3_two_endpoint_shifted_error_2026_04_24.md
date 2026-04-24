# `PO3-square.2d3` two-endpoint shifted-error control (2026-04-24)

## Status

Mainline.  This is the next live theorem target after the base-monotonicity
bridge in `Q3/Proofs/HBridge_PO3_Shell.lean`.

The lower-shell feeder is still frozen.  This note does not introduce a new
route or a new certificate architecture.  It records the exact analytic
estimate that must feed the already-frozen adaptive Vandermonde capture.

External sanity check:

- DLMF `5.11` supports the Gamma-ratio asymptotic language used for shifted
  product rows.
- DLMF `5.15` supports the digamma/psi recurrence and reflection language used
  in the slope trichotomy.

## Fixed objects

Use the interval-product avatar

```tex
A_{L,U}(x):=\prod_{j=L}^{U}(x-j)^{-1}.
```

The old profile is the special case

```tex
A_k^{(N)}(x)=A_{N+1,N+k+1}(x)
```

up to the already-frozen harmless sign convention in
`po3_gamma_profile_eq_prod`.

The wall rows are available after later bases because the shell now has:

```lean
po3_tail_zero_mono
po3_square_tail_zero_mono
po3_bilateral_integer_tail_zero_mono
po3_square2d1_target_mono
```

Therefore, for a base interval

```tex
I_k=[L_k,U_k],
```

we may use both endpoint-oriented rows:

```tex
I^+_{k,p}=[L_k,U_k+s^+_{k,p}],
```

for left-edge packets, and

```tex
I^-_{k,p}=[L_k+s^-_{k,p},U_k],
```

for right-edge packets, provided `L_k+s^-_{k,p}` is a later base.

## Adaptive row multipliers

Let `P_k={x_{k,1},...,x_{k,m}}` be the proposed edge-log top packet around a
moving center `xi_k`.

For any selected endpoint row `rho=(k,p,orientation)`, define

```tex
m_\rho(x):=\frac{A_{I_\rho}(x)}{A_{I_k}(x)}.
```

The normalized row entries are

```tex
\Psi_{\rho,i}:=\frac{m_\rho(x_{k,i})}{m_\rho(\xi_k)}.
```

Endpoint-adaptive shifts are chosen so that, after writing

```tex
x_{k,i}=\xi_k+t_{k,i}/\Lambda_k(\xi_k)+o(1/\log k),
```

the rows converge to a rectangular Vandermonde block:

```tex
\Psi_{\rho_p,i}\to \exp(-p\,t_i)
```

on compact separated `t_i` configurations.

This is the part already isolated by the adaptive-shift note and corrected by
the shift-orientation audit.  The remaining problem is not row rank.  It is
the normalized row error.

## Exact shifted-error equation

For each selected row `rho`, the wall identity has the form

```tex
\sum_{x\in X} c_x A_{I_\rho}(x)
=
\sum_{x\in X} c_x B_{I_\rho}(x).
```

Split `X=P_k \sqcup R_k`.  Then

```tex
\sum_{i\in P_k} c_i A_{I_\rho}(x_i)
=
\sum_{x\in X} c_x B_{I_\rho}(x)
-
\sum_{x\in R_k} c_x A_{I_\rho}(x).
```

Let the base packet scale be

```tex
M_k:=\max_{i\in P_k}|c_i A_{I_k}(x_i)|.
```

After dividing by `M_k m_\rho(\xi_k)`, the row equation becomes

```tex
\sum_{i\in P_k} q_{k,i}\Psi_{\rho,i}
=
\varepsilon_{\rho},
```

where

```tex
q_{k,i}:=\frac{c_i A_{I_k}(x_i)}{M_k}
```

and

```tex
\varepsilon_{\rho}
:=
\frac{
\sum_{x\in X} c_x B_{I_\rho}(x)
-
\sum_{x\in R_k} c_x A_{I_\rho}(x)}
{M_k m_\rho(\xi_k)}.
```

This is the exact object that must be controlled.

## The theorem target

`PO3-square.2d3.shifted-error-control` should prove the following.

Assume:

1. `P_k` is an edge-log top packet with compact separated local coordinates
   `t_{k,i}`.
2. Endpoint-adaptive rows `rho_0,...,rho_{m-2}` are selected so that
   `Psi_{rho_p,i}->exp(-p t_i)`.
3. The shifted remainder is small in every selected row:

```tex
\sum_{x\in R_k} c_x A_{I_{\rho_p}}(x)
=
o(M_k m_{\rho_p}(\xi_k)).
```

4. The shifted mirror is small in every selected row:

```tex
\sum_{x\in X} c_x B_{I_{\rho_p}}(x)
=
o(M_k m_{\rho_p}(\xi_k)).
```

Then

```tex
\varepsilon_{\rho_p}\to 0
\qquad (p=0,\dots,m-2),
```

and the normalized packet vector `q_k` lies asymptotically in the one-dimensional
kernel of the limiting Vandermonde block.  Equivalently, the packet is forced
into the exponential finite-difference/Hermite line.

## What would invalidate this route

There are only two real failure modes at this node.

First, the same top packet `P_k` may fail to remain dominant under the selected
endpoint-oriented rows.  Then the adaptive rows are not legitimate tests for
that packet, and the top-packet extraction must be refined before Hermite
capture can be used.

Second, the mirror or exterior remainder may fail to be

```tex
o(M_k m_\rho(\xi_k))
```

for at least one required Vandermonde row.  Then the wall has a real escape
channel and the route-kill registry must record that obstruction.

## Next exact step

Do not introduce more shell packaging.

The next proof attempt is exactly:

```tex
RemainderRowSmall + MirrorRowSmall
\quad\Longrightarrow\quad
\varepsilon_{\rho_p}\to 0
```

for the endpoint-adaptive rows above.

If this cannot be proved from the real transform-side formulas, stop at this
node and write the obstruction explicitly.  Do not claim residue/Hermite
incompatibility until this row-error estimate is closed.
