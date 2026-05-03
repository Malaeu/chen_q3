# Q3 PSD-pd Prime-Fluctuation Split (2026-05-03)

Status: in progress

Placement:

- This refines the fallback `PSD-pd` Step 9 target.
- It does not claim RH.
- It replaces direct domination of the full prime form by domination of the
  signed prime fluctuation after removing the continuous main kernel.

## Target

On the boundary-null subspace

```math
H(1/2)=H(-1/2)=0,
```

the boundary term vanishes and

```math
\mathcal W(h)=\mathcal A(h)-\mathcal P(h).
```

Write the prime measure in log coordinates as

```math
d\mu(a)=\sum_{p,m\ge1}\frac{\log p}{p^{m/2}}\delta_{m\log p}(a),
```

and split

```math
d\mu=d\mu_0+d\nu,
\qquad
d\mu_0(a)=e^{a/2}\,da.
```

Then

```math
\mathcal P(h)=\mathcal P_0(h)+\mathcal P_\nu(h).
```

The new target is:

```math
\boxed{
\mathcal A(h)\ge\mathcal P_\nu(h)
}
```

on boundary-null compact-support Hermitian-square tests.

## Green negativity of the continuous main kernel

For `h` supported in `[-L,L]`, define

```math
\Phi(u)=\int_{\mathbb R}e^{|u-v|/2}h(v)\,dv.
```

Then the continuous main prime term is

```math
\mathcal P_0(h)
=
\iint h(u)\overline{h(v)}e^{|u-v|/2}\,du\,dv
=
\langle h,\Phi\rangle.
```

The kernel satisfies, distributionally,

```math
\left(\partial_u^2-\frac14\right)e^{|u-v|/2}
=\delta(u-v).
```

Hence

```math
\left(\partial_u^2-\frac14\right)\Phi=h.
```

Boundary-null constraints make `Phi` compactly supported:

- for `u>L`,
  `Phi(u)=e^{u/2}\int h(v)e^{-v/2}dv=0`;
- for `u<-L`,
  `Phi(u)=e^{-u/2}\int h(v)e^{v/2}dv=0`.

Therefore integration by parts gives

```math
\mathcal P_0(h)
=
\left\langle
\left(\partial_u^2-\frac14\right)\Phi,\Phi
\right\rangle
=
-\|\Phi'\|_2^2-\frac14\|\Phi\|_2^2
\le0.
```

Thus the continuous main kernel is not an obstruction.  On the boundary-null
subspace, `-P0` is a positive SOS block.

## Reduced positivity theorem shape

Since

```math
\mathcal P=\mathcal P_0+\mathcal P_\nu
```

and

```math
\mathcal P_0(h)\le0,
```

we have

```math
\mathcal W(h)
=
\mathcal A(h)-\mathcal P_\nu(h)-\mathcal P_0(h)
\ge
\mathcal A(h)-\mathcal P_\nu(h).
```

So it is enough to prove:

```math
\boxed{
\mathcal A(h)-\mathcal P_\nu(h)\ge0.
}
```

Finite matrix target:

```math
P_\nu=P-P_0,
```

```math
\boxed{
N^\ast(A-P_\nu)N\succeq0.
}
```

This is strictly sharper than trying to prove `N^*(A-P)N >= 0` directly.

## Lean landing surface added

`Q3/Proofs/PSD_FormAlgebra.lean` now also contains the abstract algebra for the
main/fluctuation split.

New names:

- `Q3.Proofs.formDiff_eq_fluctuation_minus_main_of_split`
- `Q3.Proofs.formDiff_nonneg_of_main_nonpos_fluctuation_nonneg`
- `Q3.Proofs.formNonnegOn_diff_of_main_nonpos_fluctuation`
- `Q3.Proofs.formPSD_diff_of_main_nonpos_fluctuation`

Verification:

```text
cd q3.lean.aristotle && lake env lean Q3/Proofs/PSD_FormAlgebra.lean
```

The checked algebra is:

```math
q_P=q_0+q_\nu,
\qquad
q_0\le0,
\qquad
0\le q_A-q_\nu
\Longrightarrow
0\le q_A-q_P.
```

## Search synthesis

Local semantic search did not reveal an existing note containing this exact
`P0` Green-negativity split.  The closest hits were RKHS prime cap notes,
localization notes, and broad explicit-formula structure notes; none already
recorded the boundary-null conversion of the continuous kernel into
`-\|\Phi'\|^2-\frac14\|\Phi\|^2`.

External sanity:

- the Guinand--Weil explicit formula is the correct context for the split into
  zero, gamma, and prime-power terms;
- the von Mangoldt Dirichlet-series identity
  `-zeta'/zeta = sum Lambda(n)n^{-s}` is the source of the prime-power weights.

References:

- Garrett, *Guinand's explicit formula*:
  `https://www-users.cse.umn.edu/~garrett/m/complex/notes_2020-21/12g_guinand_explicit_fml.pdf`
- Encyclopedia of Mathematics, *Mangoldt function*:
  `https://encyclopediaofmath.org/wiki/Mangoldt_function`

## Next target

The next real theorem is not `A >= P`.  It is:

```math
\boxed{
A\ge P-P_0
}
```

on the boundary-null compact-support Hermitian-square class.

Equivalently, prove the fluctuation certificate:

```math
\boxed{
N^\ast(A-P_\nu)N\succeq0.
}
```

This is the current sharpest Step 10 target.

