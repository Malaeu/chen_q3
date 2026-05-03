# Q3 PSD-pd Step 12 B-spline Packet Formulas (2026-05-03)

Status: in progress

Placement:

- This refines the fallback corrected-cone `PSD-pd` certificate route.
- It does not claim RH.
- It chooses a concrete compact packet basis for the Step 10/11 finite
  certificate engine.

Notation fix:

- use `k` for the B-spline degree/order parameter;
- use `r` for prime powers `p^r`.

This avoids the collision in expressions such as `m log p`.

## Centered B-spline bump

Start with the centered box

```math
b_0(x)=\mathbf 1_{[-1/2,1/2]}(x).
```

Define the centered cardinal B-spline

```math
b_k=b_0*\cdots*b_0
```

with `k+1` box factors.  Then

```math
\operatorname{supp} b_k
\subset
\left[-\frac{k+1}{2},\frac{k+1}{2}\right],
\qquad
\int b_k=1.
```

Let

```math
s_k=\frac{k+1}{2},
\qquad
c_k=b_{2k+1}(0).
```

Because `b_k` is even,

```math
\|b_k\|_2^2=(b_k*b_k)(0)=b_{2k+1}(0)=c_k.
```

Use the normalized compact bump

```math
\boxed{
\eta_k(x)=
\sqrt{\frac{s_k}{c_k}}\,
b_k(s_kx).
}
```

Then

```math
\operatorname{supp}\eta_k\subset[-1,1],
\qquad
\|\eta_k\|_2=1.
```

## Transform

The bilateral Laplace transform of `b_k` is

```math
L_k(z)=
\int b_k(x)e^{zx}\,dx
=
\left(
\frac{\sinh(z/2)}{z/2}
\right)^{k+1}.
```

For the scaled bump define

```math
E_{\ell,k}(z)=
\int_{-1}^{1}\eta_k(x)e^{\ell zx}\,dx.
```

Then

```math
\boxed{
E_{\ell,k}(z)
=
\frac{1}{\sqrt{s_kc_k}}
\left(
\frac{\sinh(\ell z/(2s_k))}
{\ell z/(2s_k)}
\right)^{k+1}.
}
```

On the critical/Fourier axis:

```math
\boxed{
E_{\ell,k}(it)
=
\frac{1}{\sqrt{s_kc_k}}
\left(
\frac{\sin(\ell t/(2s_k))}
{\ell t/(2s_k)}
\right)^{k+1}.
}
```

## Autocorrelation

Define

```math
r_k(x)=\int \eta_k(y)\eta_k(y+x)\,dy.
```

Then

```math
\boxed{
r_k(x)=\frac{b_{2k+1}(s_kx)}{c_k}.
}
```

Thus

```math
\operatorname{supp}r_k\subset[-2,2],
\qquad
r_k(0)=1,
```

and

```math
\boxed{
r_k'(x)=
\frac{s_k}{c_k}\,
b_{2k+1}'(s_kx).
}
```

## Local packet basis

Fix:

```math
I_L=[-L,L],
\qquad
\ell>0,
\qquad
u_j\in[-L+\ell,L-\ell].
```

Use

```math
\boxed{
\psi_j(u)=
\ell^{-1/2}
\eta_k\!\left(\frac{u-u_j}{\ell}\right).
}
```

Then

```math
\operatorname{supp}\psi_j\subset[u_j-\ell,u_j+\ell]\subset[-L,L].
```

The transform is

```math
\boxed{
H_j(z)=
\sqrt{\ell}\,e^{zu_j}E_{\ell,k}(z).
}
```

## Gram matrix

Set

```math
d_{ij}=u_j-u_i.
```

Then

```math
\boxed{
G_{ij}=
r_k(d_{ij}/\ell).
}
```

Because `r_k` is supported in `[-2,2]`, `G` is banded:

```math
G_{ij}=0
\quad\text{if}\quad
|d_{ij}|>2\ell.
```

## Arch matrix

The Archimedean matrix is

```math
\boxed{
A_{ij}
=
\frac{\ell}{2\pi}
\int_{\mathbb R}
\Omega(t)\,
|E_{\ell,k}(it)|^2
e^{itd_{ij}}\,dt.
}
```

Since `Omega` and `|E|^2` are even/real:

```math
\boxed{
A_{ij}
=
\frac{\ell}{\pi}
\int_0^\infty
\Omega(t)\,
|E_{\ell,k}(it)|^2
\cos(td_{ij})\,dt.
}
```

Here

```math
\boxed{
|E_{\ell,k}(it)|^2
=
\frac1{s_kc_k}
\left(
\frac{\sin(\ell t/(2s_k))}
{\ell t/(2s_k)}
\right)^{2k+2}.
}
```

Therefore `A_ij=a_{ell,k}(d_ij)`.  On a uniform grid, `A` is Toeplitz.

## Boundary constraints

Boundary-null means

```math
H_v(1/2)=0,
\qquad
H_v(-1/2)=0.
```

For a symmetric real bump,

```math
E_{\ell,k}(1/2)=E_{\ell,k}(-1/2).
```

The nonzero common scalar can be dropped, so the constraint matrix is

```math
\boxed{
Q=
\begin{pmatrix}
e^{u_1/2}&\cdots&e^{u_n/2}\\
e^{-u_1/2}&\cdots&e^{-u_n/2}
\end{pmatrix}.
}
```

Let `N` have columns spanning `ker Q`.

## Prime matrix

For a prime-power shift

```math
a=r\log p,
\qquad
w_a=\frac{\log p}{p^{r/2}}
=\log p\,e^{-a/2},
```

use only `a<=2L`.

The cross-correlation is

```math
C_{ij}(a)
=
\langle\psi_j,S_a\psi_i\rangle
=
r_k((d_{ij}-a)/\ell).
```

Thus

```math
\boxed{
P_{ij}
=
\sum_{r\log p\le2L}
\frac{\log p}{p^{r/2}}
\left[
r_k\!\left(\frac{d_{ij}-r\log p}{\ell}\right)
+
r_k\!\left(\frac{d_{ij}+r\log p}{\ell}\right)
\right].
}
```

This is a sparse shifted-band matrix because `r_k` vanishes outside `[-2,2]`.

## Continuous main matrix

The continuous main measure is

```math
d\mu_0(a)=e^{a/2}\,da.
```

Define

```math
\boxed{
(P_0)_{ij}
=
\int_0^{2L}
e^{a/2}
\left[
r_k\!\left(\frac{d_{ij}-a}{\ell}\right)
+
r_k\!\left(\frac{d_{ij}+a}{\ell}\right)
\right]\,da.
}
```

Equivalently,

```math
(P_0)_{ij}=P_0^+(d_{ij})+P_0^-(d_{ij}),
```

where

```math
\boxed{
P_0^+(d)=
\ell e^{d/2}
\int_{[(d-2L)/\ell,d/\ell]\cap[-2,2]}
e^{-\ell x/2}r_k(x)\,dx,
}
```

and

```math
\boxed{
P_0^-(d)=
\ell e^{-d/2}
\int_{[d/\ell,(d+2L)/\ell]\cap[-2,2]}
e^{\ell x/2}r_k(x)\,dx.
}
```

Since `r_k` is piecewise polynomial, these one-dimensional integrals are
friendly to exact symbolic integration or interval quadrature.

## Fluctuation matrix

Define

```math
\boxed{
P_\nu=P-P_0.
}
```

Equivalently, using Step 11 cumulative error

```math
E(x)=
\sum_{r\log p\le x}
\frac{\log p}{p^{r/2}}
-2(e^{x/2}-1),
```

the entries are local smoothed-error bands:

```math
\boxed{
(P_\nu)_{ij}
=
\mathcal E_{\ell,k}(d_{ij})
+
\mathcal E_{\ell,k}(-d_{ij}),
}
```

with

```math
\boxed{
\mathcal E_{\ell,k}(d)
=
\frac1\ell
\int_0^{2L}
E(a)\,
r_k'\!\left(\frac{d-a}{\ell}\right)\,da.
}
```

## Certificate matrix

Set

```math
R=A-P_0.
```

The reduced matrices are

```math
R^\circ=N^\ast RN,
\qquad
P_\nu^\circ=N^\ast P_\nu N.
```

The finite certificate is

```math
\boxed{
C^\circ
=
N^\ast(A-P)N
=
N^\ast(R-P_\nu)N
\succeq0.
}
```

Equivalently:

```math
\boxed{
\lambda_{\max}(P_\nu^\circ,R^\circ)\le1.
}
```

## Proof-grade warning

`b_k` is only `C^{k-1}`.  That is acceptable for a fast Galerkin/certificate
pilot, but the final admissible-test proof needs one of the following:

1. a smoothing limit

```math
\eta_{k,\varepsilon}=\eta_k*\phi_\varepsilon
```

with a strict gap `C^circ >= delta G^circ` preserved for small `epsilon`;

2. or a `C^\infty` compact bump from the start, with the same matrix formulas
but interval quadrature for `E_ell`, `r`, `P0`, and `A`.

Recommended workflow:

```math
\boxed{
\text{B-spline for reconnaissance; } C^\infty\text{ bump for final certificate.}
}
```

## Search synthesis

Local semantic search:

- existing Q3 notes already support finite packet dictionaries, finite Gram
  matrices, autocorrelation compact support, and the `(2M+1)` Rayleigh scaling
  audit;
- no prior local note had the explicit B-spline packet formulas above;
- the Step 12 packet should stay under fallback `PSD-pd`, not replace the
  active `H-bridge` route.

External sanity:

- centered cardinal B-splines are convolution powers of the centered box and
  have sinc-power Fourier transform;
- cardinal B-splines are compactly supported piecewise polynomials with
  smoothness controlled by degree;
- rigorous finite positive-definiteness checks can later use verified
  Cholesky / interval methods.

References:

- de Boor, *cardinal B-splines*:
  `https://pages.cs.wisc.edu/~deboor/toast/pages005.html`
- bsplines.org, *Flavors and Types of B-Splines*:
  `https://bsplines.org/flavors-and-types-of-b-splines/`
- Rump, *Verification of Positive Definiteness*:
  `https://www.tuhh.de/ti3/paper/rump/Ru06c.pdf`

## Next target

Step 13 should implement the numerical pilot:

- build `G,A,P,P0,Pnu,Q,N`;
- compute `C^circ=N^*(A-P)N`;
- compute the generalized eigenvalue
  `lambda_max(Pnu^circ,R^circ)`;
- report the gap and the worst vector;
- prepare interval-Cholesky hooks for proof-grade finite certificates.
