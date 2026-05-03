# Q3 PSD-pd Step 11 Smoothed Prime Error (2026-05-03)

Status: in progress

Placement:

- This refines the fallback corrected-cone `PSD-pd` route.
- It does not claim RH.
- It supplies the analytic target behind the Step 10 relative certificate
  `lambda_max(Pnu^circ, R^circ) <= 1`.

## Prime fluctuation as a Stieltjes error

Define the cumulative prime-weight in log coordinates:

```math
M(x)=
\sum_{m\log p\le x}
\frac{\log p}{p^{m/2}}
=
\sum_{n\le e^x}\frac{\Lambda(n)}{\sqrt n}.
```

The continuous main mass is

```math
M_0(x)=\int_0^x e^{a/2}\,da=2(e^{x/2}-1).
```

Set

```math
E(x)=M(x)-M_0(x).
```

Then the fluctuation measure is

```math
d\nu=d\mu-e^{a/2}da=dE.
```

For a Hermitian square `f=h*h^sharp`, define

```math
\varphi_h(a)=f(a)+f(-a).
```

The prime-fluctuation form is

```math
\mathcal P_\nu(h)
=
\int_0^{2L}\varphi_h(a)\,dE(a).
```

Using Stieltjes integration by parts, with the endpoint terms killed by
`E(0)=0` and the compact-support edge of `f`, the working representation is

```math
\boxed{
\mathcal P_\nu(h)
=
-\int_0^{2L}
E(a)\,\varphi_h'(a)\,da.
}
```

This is the important compression: raw prime spikes are replaced by the
cumulative error `E` tested against a smooth autocorrelation derivative.

## Local bump basis formula

For the local bump basis

```math
\psi_j(u)=\ell^{-1/2}\eta((u-u_j)/\ell),
```

let

```math
r_\eta(x)=\int \eta(y)\overline{\eta(y+x)}\,dy.
```

Then

```math
C_{ij}(a)
=
r_\eta((u_j-u_i-a)/\ell).
```

Writing `d_ij=u_j-u_i`, Stieltjes integration by parts gives

```math
(P_\nu)_{ij}
=
\mathcal E_\ell(d_{ij})+\mathcal E_\ell(-d_{ij}),
```

where

```math
\boxed{
\mathcal E_\ell(d)
=
\frac1\ell
\int_0^{2L}
E(a)\,
r_\eta'\!\left(\frac{d-a}{\ell}\right)\,da.
}
```

Thus the finite fluctuation matrix is built from local smoothed windows of
the Chebyshev/von-Mangoldt error, not from unsmoothed prime spikes.

## Correct certificate target

Keep the Step 10 base energy:

```math
R=A-P_0=A+S_0.
```

On the boundary-null finite space, the proof target is:

```math
\boxed{
R^\circ-P_\nu^\circ\succeq0.
}
```

Equivalently, on the quotient where needed,

```math
\boxed{
\lambda_{\max}(P_\nu^\circ,R^\circ)\le1.
}
```

Step 11 provides the concrete way to build `Pnu^circ`:

```math
P_\nu=P_\nu(E,\eta,\ell,L).
```

## Do not use pointwise RH-level error

The tempting target

```math
|E(x)|\ \text{pointwise small}
```

is the wrong level.  Strong pointwise bounds for this normalized prime error
would run close to RH-level prime number theorem error estimates.

The correct target is operator domination on the autocorrelation class:

```math
\boxed{
\sup_{h\ne0,\ Qh=0}
\frac{\mathcal P_\nu(h)}{R(h)}
\le1.
}
```

This may hold even when `E(x)` is locally large, because the test functions
are not arbitrary; they are autocorrelation derivatives coming from
`h*h^sharp`.

## Lean landing surface added

`Q3/Proofs/PSD_FormAlgebra.lean` now includes the Step 11 consumer algebra.

New names:

- `Q3.Proofs.fluctuation_le_base_of_abs_relative_bound`
- `Q3.Proofs.formNonnegOn_diff_of_abs_relative_fluctuation_bound`

The checked algebra is:

```math
q_P=q_0+q_\nu,
\qquad
0\le R=q_A-q_0,
\qquad
|q_\nu|\le\theta R,
\qquad
\theta\le1
\Longrightarrow
q_A-q_P\ge0
```

on the boundary-null predicate.

This is exactly the consumer needed for a future smoothed-error theorem.

Verification command:

```text
cd q3.lean.aristotle && lake env lean Q3/Proofs/PSD_FormAlgebra.lean
```

## Search synthesis

Local semantic search:

- closest existing hits were `DigammaRemainder` Stieltjes swap machinery and
  older localized prime/RKHS notes;
- no existing note already had the exact formula
  `Pnu(h)=-int E(a) phi_h'(a) da` or the local smoothed-error coefficient
  `E_ell(d)`;
- older A3/RKHS prime-cap notes remain useful as precedent for operator norm
  targets, but they do not replace the new Step 11 certificate.

External sanity:

- Encyclopedia of Mathematics records the Chebyshev function identity
  `psi(x)=sum_{n<=x} Lambda(n)` and the prime-power form
  `psi(x)=sum_{p^m<=x} log p`.
- Standard integration-by-parts references support the endpoint-transfer
  calculation; here the Stieltjes form is used with the cumulative function
  `E`.
- Verified PSD / Cholesky literature supports the planned finite certificate
  engine, but a certified finite level is still only evidence until paired with
  a uniform exhaustion theorem.

References:

- Encyclopedia of Mathematics, *Chebyshev function*:
  `https://encyclopediaofmath.org/wiki/Chebyshev_function`
- Encyclopedia of Mathematics, *Stieltjes integral*:
  `https://encyclopediaofmath.org/wiki/Stieltjes_integral`
- Encyclopedia of Mathematics, *Integration by parts*:
  `https://encyclopediaofmath.org/wiki/Integration_by_parts`
- Rump, *Verification of Positive Definiteness*:
  `https://www.tuhh.de/ti3/paper/rump/Ru06c.pdf`

## Next target

Step 12 should choose a concrete compact bump `eta` and derive explicit
entries for:

- `G`;
- `A`;
- `P0`;
- `Pnu`;
- boundary constraint matrix `Q`;
- projection `N`;
- generalized eigenvalue / interval-Cholesky certificate.

Recommended first engineering choice: use a compact polynomial bump or
B-spline-like autocorrelation so that `r_eta` and `r_eta'` are explicit enough
for interval arithmetic.
