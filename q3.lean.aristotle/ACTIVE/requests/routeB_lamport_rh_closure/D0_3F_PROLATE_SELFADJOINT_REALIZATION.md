# D0.3f — ProlateSelfadjointRealization

Status: `MATH_PROVED / EXTERNAL_PRIMARY_SOURCE_LOCKED / LEAN_UNPINNED / NOT_RH`

Exit: `PROLATE_SELFADJOINT_REALIZATION_LOCKED`.

This leaf repairs the former `D0_3_PW_SELFADJOINT_DOMAIN_MISSING` blocker. It
uses the versioned source lock `D0_3F_EXTERNAL_SOURCE_LOCK.json` and an exact
unitary scaling to match the project's normalization.

## 1. Exact project operator

Fix `lambda>1` and put

```text
Ktime_lambda = L2([-lambda,lambda],dx),
p_lambda(x)  = lambda^2-x^2,
V_lambda(x)  = (2*pi*lambda*x)^2.
```

Let `Amax_lambda` be the class of complex functions `f` on
`(-lambda,lambda)` such that:

1. `f in L2(-lambda,lambda)`;
2. `f'` exists and is locally absolutely continuous;
3. the distribution/pointwise-a.e. expression

   ```text
   PWExpr_lambda f = -(p_lambda f')' + V_lambda f
   ```

   belongs to `L2(-lambda,lambda)`.

Define the canonical window domain

```text
Dom(PW_lambda) = {
  f in Amax_lambda :
  lim_(x->-lambda+) p_lambda(x)f'(x)=0 and
  lim_(x-> lambda-) p_lambda(x)f'(x)=0
}.
```

Then

```text
PW_lambda : Dom(PW_lambda) subset Ktime_lambda -> Ktime_lambda,
PW_lambda f = PWExpr_lambda f.
```

Both endpoint limits are part of the type. The core
`C_c^infinity(-lambda,lambda)` from D0.3e is contained in this domain but is
not itself the selfadjoint domain.

## 2. Imported primary theorem

Katsnelson treats

```text
L_a f = -d/dt((1-t^2/a^2)f') + t^2 f
```

on `L2([-a,a])`. The paper defines its maximal domain, classifies all
selfadjoint extensions, and identifies the canonical identity-matrix
extension by the two zero-flux conditions

```text
lim_(x->plus_or_minus a) (1-x^2/a^2)f'(x)=0.
```

That extension is positive and selfadjoint and is the unique extension
commuting with the correspondingly normalized truncated Fourier operator. The
same paper proves simple discrete spectrum and identifies a complete
orthogonal family of prolate spheroidal wavefunctions.

The exact source version, TeX member, hash, and theorem labels are recorded in
`D0_3F_EXTERNAL_SOURCE_LOCK.json`.

## 3. Exact scaling to the project normalization

Put

```text
c=sqrt(2*pi),
a=c*lambda,
(U f)(t)=c^(-1/2)f(t/c).
```

Then `U:Ktime_lambda -> L2([-a,a],dt)` is unitary. Direct differentiation
gives the exact conjugacy

```text
PW_lambda
  = (c^2*lambda^2) U^(-1) L_(a,I) U
  = (2*pi*lambda^2) U^(-1) L_(a,I) U.                 (3.1)
```

Indeed the principal term becomes
`-d/dx((lambda^2-x^2)f')`, while the source potential `t^2` becomes exactly
`(2*pi*lambda*x)^2` after multiplication by `c^2*lambda^2`.

The source flux condition transforms by nonzero scalar factors into exactly

```text
lim p_lambda f'=0 at x=-lambda and x=+lambda.
```

Positive scalar multiplication and unitary conjugacy preserve
selfadjointness, positivity, spectral multiplicity, discreteness, and
completeness. Thus every operator property claimed in this leaf follows
directly for the exact project expression and exact project domain.

## 4. Dimensionless cross-check

The unitary rescaling

```text
(S_lambda f)(y)=sqrt(lambda) f(lambda*y),    -1<=y<=1,
```

transports `PW_lambda` to

```text
-d/dy((1-y^2)d/dy) + c_lambda^2 y^2,
c_lambda=2*pi*lambda^2,
```

with boundary condition

```text
lim_(y->plus_or_minus 1) (1-y^2)g'(y)=0.
```

This matches the exact dimensionless bandwidth and prolate wavefunction
normalization in `PEN_3_3_G04_OBJECT_DICTIONARY.md`.

## 5. Truncated-Fourier commutation check

Under `t=c*x` and `xi=c*y`, the source kernel `exp(i*t*xi)` becomes exactly
the project kernel `K(x,y)=exp(2*pi*i*x*y)`. Equivalently, direct
differentiation gives

```text
PW_x K(x,y)=PW_y K(x,y).
```

For `f in Dom(PW_lambda)`, two integrations by parts move `PW_x` from `f` to
the kernel. The boundary terms vanish because `p_lambda f'` tends to zero,
`p_lambda` itself tends to zero, and the canonical source domain has finite
endpoint values. Thus the canonical realization commutes with the truncated
Fourier operator on the window.

This commutation validates the choice of selfadjoint extension. It does not
identify `PW_lambda` with `A_m`, `Dlog_m`, `WeilOp_m_N`, or the missing
detector.

## 6. Lamport proof

```text
<1>1. The versioned primary source defines the maximal domain and the unique
      zero-flux selfadjoint extension of its prolate expression.
<1>2. Set c=sqrt(2*pi), a=c*lambda, and use the displayed unitary U.
<1>3. Exact conjugacy (3.1) transports the source action, both endpoint flux
      conditions, and the kernel exp(i*t*xi) to the project conventions.
<1>4. Positive scalar/unitary transport preserves selfadjointness,
      positivity, simple discrete spectrum, and completeness.
<1>5. Rescaling to [-1,1] gives c_lambda=2*pi*lambda^2 and the standard prolate
      differential equation used by the project trial functions.
<1>6. Kernel differentiation plus the zero-flux boundary conditions verifies
      truncated-Fourier commutation.
<1>7. Therefore the exact window operator, domain, action, and
      selfadjointness required by D0.3f are locked.
```

Conclusion: `D0.3f = PROVED`. QED.

## 7. Planted falsifiers

- `CORE_IS_DOMAIN`: replacing the selfadjoint domain by
  `C_c^infinity(-lambda,lambda)` must fail.
- `NO_BOUNDARY`: the maximal domain alone has a family of selfadjoint
  extensions and is not the canonical operator.
- `DIRICHLET_ALIAS`: imposing `f(plus_or_minus lambda)=0` is not the source's
  zero-flux realization.
- `ONE_ENDPOINT`: checking only one flux limit leaves the boundary form open.
- `WRONG_SCALING`: omitting `c=sqrt(2*pi)` or replacing
  `c_lambda=2*pi*lambda^2` by `2*pi*lambda` fails the exact conjugacy.
- `GLOBAL_WINDOW_ALIAS`: the global natural selfadjoint extension on `L2(R)`
  is a distinct carrier and does not fill this window slot.
- `OPERATOR_CONFLATION`: no equality with the Weil, scaling, or detector
  operators follows from sharing prolate trial functions.

## 8. Explicit nonclaims

```text
NO_PW_EQUALS_WEIL_OPERATOR
NO_PW_EQUALS_DLOG
NO_CANONICAL_DETECTOR_OPERATOR
NO_GROUND_TRIAL_TRACKING
NO_H1_H4
NO_D0_3_ASSEMBLY
NO_D0_ASSEMBLY
NO_RH
```
