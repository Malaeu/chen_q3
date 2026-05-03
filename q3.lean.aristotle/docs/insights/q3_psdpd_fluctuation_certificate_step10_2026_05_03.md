# Q3 PSD-pd Step 10 Fluctuation Certificate (2026-05-03)

Status: in progress

Placement:

- This refines the fallback corrected-cone `PSD-pd` route.
- It does not claim RH.
- It is the finite certificate layer after the prime fluctuation split.

## Correction to the previous target

The previous sufficient target

```math
A-P_\nu\succeq0
```

is valid but too strong.

After the split

```math
P=P_0+P_\nu
```

and the boundary-null Green identity

```math
-P_0=S_0\ge0,
```

the real form is

```math
\mathcal W(h)=\mathcal A(h)+S_0(h)-\mathcal P_\nu(h).
```

Thus the correct base energy is

```math
R=A+S_0=A-P_0.
```

The sharp target is:

```math
\boxed{
R-P_\nu\succeq0.
}
```

Do not discard `S0`: it is the positive Green block that can cover
low-frequency weakness in the Archimedean term.

## Finite matrix target

On a finite test basis with boundary constraints

```math
Qv=(H_v(1/2),H_v(-1/2))=0,
```

let `N` span `ker Q`.

Define

```math
R^\circ=N^\ast(A-P_0)N,
```

```math
P_\nu^\circ=N^\ast(P-P_0)N.
```

Then the Step 10 certificate is:

```math
\boxed{
R^\circ-P_\nu^\circ\succeq0.
}
```

Equivalently, if `R^\circ` is positive definite,

```math
\boxed{
\lambda_{\max}
\left(
(R^\circ)^{-1/2}P_\nu^\circ(R^\circ)^{-1/2}
\right)
\le1.
}
```

If `R^\circ` is only semidefinite, use the quotient/generalized-eigenvalue
form:

```math
P_\nu^\circ x=\lambda R^\circ x,
\qquad
\lambda_{\max}\le1,
```

with compatibility on `ker R^\circ`.

## Matrix entries

Prime matrix:

```math
P_{ij}
=
\sum_{m\log p\le2L}
\frac{\log p}{p^{m/2}}
\left[
C_{ij}(m\log p)+C_{ij}(-m\log p)
\right].
```

Continuous main matrix:

```math
(P_0)_{ij}
=
\int_0^{2L}
e^{a/2}
\left[
C_{ij}(a)+C_{ij}(-a)
\right]\,da.
```

Fluctuation matrix:

```math
(P_\nu)_{ij}=P_{ij}-(P_0)_{ij}.
```

For the local bump basis

```math
\psi_j(u)=\ell^{-1/2}\eta((u-u_j)/\ell),
```

the cross-correlation is

```math
C_{ij}(a)=r_\eta((u_j-u_i-a)/\ell),
```

so `Pnu` is exactly a local arithmetic discrepancy: prime spikes minus the
continuous `e^{a/2}` background.

## Lean landing surface added

`Q3/Proofs/PSD_FormAlgebra.lean` now includes the abstract Step 10 algebra.

New names:

- `Q3.Proofs.fluctuationBase`
- `Q3.Proofs.formDiff_eq_base_minus_fluct_of_split`
- `Q3.Proofs.formDiff_nonneg_of_fluctuation_le_base`
- `Q3.Proofs.formNonnegOn_diff_of_fluctuation_le_base`
- `Q3.Proofs.fluctuation_le_base_of_relative_bound`
- `Q3.Proofs.formNonnegOn_diff_of_relative_fluctuation_bound`

Verification:

```text
cd q3.lean.aristotle && lake env lean Q3/Proofs/PSD_FormAlgebra.lean
```

The checked algebra is:

```math
q_P=q_0+q_\nu,
\qquad
q_\nu\le q_A-q_0
\Longrightarrow
q_A-q_P\ge0.
```

The relative version records:

```math
q_\nu\le\theta(q_A-q_0),
\qquad
0\le q_A-q_0,
\qquad
\theta\le1
\Longrightarrow
q_A-q_P\ge0.
```

## Search synthesis

Local semantic search:

- no prior note already had the exact Step 10 target
  `R=A-P0`, `Pnu=P-P0`, `lambda_max(Pnu,R)<=1`;
- older localization and RKHS/cap notes are related but do not contain the
  Green-corrected fluctuation certificate;
- finite checker / certified Cholesky language exists as a general route, but
  still needs instantiation with the `R-Pnu` matrix.

External sanity:

- Chebyshev/von Mangoldt sources confirm that `psi(x)=sum_{n<=x}Lambda(n)`
  has main term `x`, which after the `n^{-1/2}` log-coordinate weighting gives
  cumulative main mass `2(e^{x/2}-1)` and density `e^{a/2} da`.
- Interval/PSD matrix literature supports certified finite matrix checks, but
  this remains a certificate method, not a substitute for a uniform analytic
  exhaustion theorem.

References:

- Encyclopedia of Mathematics, *Chebyshev function*:
  `https://encyclopediaofmath.org/wiki/Chebyshev_function`
- Encyclopedia of Mathematics, *Mangoldt function*:
  `https://encyclopediaofmath.org/wiki/Mangoldt_function`
- Rump, *Verification methods: Rigorous results using floating-point
  arithmetic*, Acta Numerica 2010:
  `https://doi.org/10.1017/S096249291000005X`

## Next target

Step 11 should attack the fluctuation operator:

```math
\boxed{
\mathcal P_\nu(h)
\le
\theta\left(\mathcal A(h)+S_0(h)\right),
\qquad
\theta<1.
}
```

Equivalently, prove a uniform bound for

```math
E(x)
=
\sum_{m\log p\le x}\frac{\log p}{p^{m/2}}
-2(e^{x/2}-1).
```

This is now the sharp analytic remainder problem.

