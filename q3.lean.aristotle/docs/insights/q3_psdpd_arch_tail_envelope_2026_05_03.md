# Arch tail envelope for the PSD-pd Arch matrix

## Goal

Isolate the analytic tail lemma used by the Step 22 Arch interval patch.

The Arch matrix entries have the form

\[
A_{ij}
=
\frac{\ell}{\pi}
\int_0^\infty
\Omega(t)
|E_{\ell,k}(it)|^2
\cos(t(u_j-u_i))\,dt.
\]

Step 22 computes the finite part by interval integration and controls the tail
by an analytic envelope.  The reusable lemma target is:

\[
|\Omega(t)|\le 10\log(2+t)
\qquad (t\ge0),
\]

where

\[
\Omega(t)
=
-\log\pi+
\operatorname{Re}\psi\left(\frac14+\frac{it}{2}\right).
\]

For the finite certificate, the actually needed statement is weaker:

\[
|\Omega(t)|\le 10\log(2+t)
\qquad (t\ge T),
\]

with \(T=260\).  The global version is cleaner as a standalone target; the
tail-only version is enough for Step 22.

## Tail bound shape

For the B-spline packet,

\[
|E_{\ell,k}(it)|^2
=
\frac1{s_kc_k}
\left|
\frac{\sin(\ell t/(2s_k))}
{\ell t/(2s_k)}
\right|^{2k+2}.
\]

Using \(|\sin x/x|\le 1/|x|\), for \(t>0\):

\[
|E_{\ell,k}(it)|^2
\le
\frac1{s_kc_k}
\left(\frac{2s_k}{\ell t}\right)^{2k+2}.
\]

Therefore

\[
|A_{>T}(d)|
\le
\frac{\ell}{\pi}
\frac1{s_kc_k}
\left(\frac{2s_k}{\ell}\right)^{2k+2}
10
\int_T^\infty
\log(2+t)t^{-2k-2}\,dt.
\]

For the primary certificate \(k=11\), so the exponent is \(24\).  With
\(\ell=0.30\) and \(T=260\), Step 22 obtained the conservative tail radius

\[
1.3296454597994329\cdot 10^{-18}.
\]

## Proof shape

The digamma term should be bounded using a standard right-half-plane growth
estimate:

\[
|\psi(z)| \le C_0+\log(1+|z|)
\qquad (\operatorname{Re}z\ge 1/4).
\]

Substitute \(z=1/4+it/2\), absorb \(-\log\pi\) and constants into the factor
10, and obtain

\[
|\Omega(t)|\le 10\log(2+t).
\]

If proving the bound globally is inconvenient, split:

1. prove the analytic bound for \(t\ge T_0\);
2. certify the compact interval \([0,T_0]\) separately by interval arithmetic.

For Step 22 only the tail range \(t\ge260\) is used.

## Lean targets

- `archOmega_log_bound_tail`:
  \[
  t\ge T_0\Rightarrow |\Omega(t)|\le 10\log(2+t).
  \]
- `sinc_power_tail_bound`:
  \[
  |E_{\ell,k}(it)|^2
  \le
  \frac1{s_kc_k}\left(\frac{2s_k}{\ell t}\right)^{2k+2}.
  \]
- `arch_A_tail_radius_bound`:
  combine the two bounds into the tail radius for \(A_{ij}\).

## Status

This note records the analytic lemma candidate behind the Step 22 Arch tail.
The finite interval-backed block is already closed numerically/interval-wise;
formalizing this envelope makes the tail auditable as a reusable proof object.
