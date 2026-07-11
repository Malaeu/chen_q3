# D0.3 — Exact operator type registry

Status: `MATH_PROVED / ALL_EIGHT_COMPONENTS_LOCKED / NOT_RH`

Parent status: `PROVED / LEAN_INTERFACE_UNPINNED`.

Honest exit: `EXACT_OPERATOR_TYPES_LOCKED`.

This artifact proves `D0.3a`–`D0.3h` and their explicit assembly. The detector
slot is filled only by the exact two-parameter finite carrier `Mfin_m_N`; the
one-parameter symbol `M_lambda` remains undefined pending a selector/bridge.

## 1. Common index and identification rule

Fix a D0.1 index `(m,N)`, and write

```text
lambda = sqrt(m),       L = log(m),
H_m    = L2([lambda^-1,lambda],du/u),
E_m_N  = span_C{V_n_m: |n|<=N}.
```

All Hilbert-space inner products are antilinear in the first slot. Two
operators may be identified only after proving all of:

1. a named unitary between their carrier Hilbert spaces;
2. equality of the transported operator domains;
3. an intertwining identity on that domain;
4. equality of the named inner-product structures used for any
   selfadjointness claim.

Sharing a symbol, an eigenvector, or an ambient vector space is insufficient.

## 2. D0.3a — form-representation operator `A_m`

Let `BW_m` be the closed lower-semibounded form from D0.2. Define

```text
Dom(A_m) = {
  f in Dom(BW_m) :
  exists h in H_m, for every g in Dom(BW_m),
    BW_m(f,g)=<h,g>_H_m
}.
```

The representing vector is unique, and `A_m f := h`. Thus

```text
A_m : Dom(A_m) subset H_m -> H_m,
BW_m(f,g)=<A_m f,g>_H_m
  for f in Dom(A_m), g in Dom(BW_m).
```

The closed-semibounded-form representation theorem and the source's compact
resolvent theorem give:

```text
A_m is lower bounded and selfadjoint in the standard H_m inner product;
A_m has purely discrete spectrum.
```

The diagonal formula `<A_m f,f>` is not asserted for arbitrary
`f in Dom(BW_m)`: applying `A_m` additionally requires `f in Dom(A_m)`.

Source pin: `literature/zotero/H8ULBMAL/fulltext.md`, Section 3.2,
representation theorem through Theorem 3.6.

Verdict: `D0.3a = PROVED / SOURCE_LOCKED / LEAN_UNPINNED`.

## 3. D0.3b — periodic scaling operator `Dlog_m`

Under the D0.1 unitary

```text
kappa_m : L2([0,L],dx) -> H_m,
kappa_m(F)(u)=F(log(lambda*u)),
```

define

```text
H1_per([0,L]) = {F in H1([0,L]) : trace(F)(0)=trace(F)(L)},
Dom(Dlog_m)   = kappa_m(H1_per([0,L])),
Dlog_m        = kappa_m (-i*d/dx) kappa_m^(-1).
```

Equivalently, on its domain,

```text
Dlog_m f = -i*u*(d/du)f = -i*(d/d log u)f.
```

It is selfadjoint in the standard `H_m` inner product and

```text
Dlog_m(V_n_m) = (2*pi*n/L) V_n_m,        n in Z.
```

The periodic trace condition is part of the operator type. The finite index
matrix `diag(n)` used in diagnostics is not this operator unless the factor
`2*pi/L` and the synthesis map are written explicitly.

Source pin: `fulltext.md`, equation (5.14), Corollary 5.6, and the periodic
scaling spectrum used in Lemma 5.8.

Verdict: `D0.3b = PROVED / SOURCE_LOCKED / LEAN_UNPINNED`.

## 4. D0.3c — finite Riesz operator of the restricted form

Because `E_m_N` is finite dimensional, D0.2's restricted Hermitian form has
a unique standard-inner-product Riesz operator

```text
WeilOp_m_N : E_m_N -> E_m_N
```

defined by

```text
BW_m_N(f,g)=<WeilOp_m_N f,g>_H_m.
```

In the ordered ON basis `(V_-N_m,...,V_N_m)`, its matrix is exactly
`WeilMat_m_N`. It is bounded and selfadjoint on `E_m_N`.

This proves only a form compression. It does not prove

```text
E_m_N subset Dom(A_m),
A_m(E_m_N) subset E_m_N,
WeilOp_m_N = A_m restricted to E_m_N,
WeilOp_m_N = P_m_N A_m P_m_N.
```

Those statements require additional domain/invariance hypotheses and are not
imported from the finite matrix identity.

Verdict: `D0.3c = PROVED / FINITE_RIESZ_THEOREM / LEAN_UNPINNED`.

## 5. D0.3d — raw perturbation versus modified-space realization

This slot registers two different dependent objects.

### 5.1 Raw rank-one constructor

For `xi in E_m_N` with `delta_m_N(xi)=1`, define on the same domain as
`Dlog_m`

```text
PertRaw_m_N_xi
  := Dlog_m - |Dlog_m xi><delta_m_N|,
Dom(PertRaw_m_N_xi)=Dom(Dlog_m).
```

Then

```text
PertRaw_m_N_xi(xi)=0,
PertRaw_m_N_xi(f)=Dlog_m(f) when delta_m_N(f)=0.
```

This is a well-typed finite-rank perturbation for the displayed parameters.
Its standard-`H_m` selfadjointness is `NOT_CLAIMED`; it is false in general.
The parameter `xi` may not be erased from the object name.

### 5.2 Conditional canonical source realization

Suppose additionally that:

```text
epsilon_m_N is a simple bottom eigenvalue of WeilOp_m_N;
xi is its even eigenvector;
delta_m_N(xi) != 0 and has been rescaled to 1.
```

Then the source's canonical `Dlog^(m,N)` is the above raw formula as a map,
but its selfadjoint theorem uses the distinct Hilbert carrier

```text
K_m_N_xi
  = (E_m_N / C*xi, inner product induced by
       BW_m_N - epsilon_m_N*<.,.>_H_m)
    direct_sum E_m_N^perp.
```

The theorem does not assert that `PertRaw_m_N_xi` is selfadjoint in the
original standard `H_m` inner product. The simple-even hypothesis is the open
H2a obligation; this registry records the conditional interface but does not
prove H2a or canonical existence for every `(m,N)`.

Source pin: `fulltext.md`, Proposition 5.7 and Theorem 5.10.

Verdict: `D0.3d = PROVED AS A TYPED CONDITIONAL INTERFACE`; hypothesis supply
remains `OPEN_H2a`.

## 6. D0.3e — prolate differential expression

On the additive time-window space

```text
Ktime_m = L2([-lambda,lambda],dx),
```

the exact formal differential expression is

```text
PWExpr_m f
  = -d/dx ((lambda^2-x^2) d/dx f)
    + (2*pi*lambda*x)^2 f.
```

It is unconditionally well typed, for example, as

```text
PWExpr_m : C_c^infinity((-lambda,lambda)) -> Ktime_m.
```

The project dictionary also locks the normalized prolate wavefunctions and
their parity/index conventions used to build trial packets. This does not yet
lock an exact selfadjoint operator domain at the singular endpoints.

Source pins: `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md`, Section 1, and
`fulltext.md`, Sections 7–8.

Verdict: `D0.3e = PROVED / FORMAL_EXPRESSION_SOURCE_LOCKED`.

## 7. D0.3f — exact prolate selfadjoint realization

The versioned primary-source import and exact unitary scaling in
`D0_3F_PROLATE_SELFADJOINT_REALIZATION.md` prove the window realization

```text
PW_m : Dom(PW_m) subset Ktime_m -> Ktime_m,
Dom(PW_m) = {f in Dom_max:
  lim_(x->-lambda+) (lambda^2-x^2)f'(x)=0 and
  lim_(x-> lambda-) (lambda^2-x^2)f'(x)=0}.
```

It is the positive selfadjoint realization with simple discrete spectrum and
complete prolate eigenfamily. With `c=sqrt(2*pi)` and `a=c*lambda`, it is
exactly `(2*pi*lambda^2)U^(-1)L_(a,I)U`; hence the source kernel `exp(i*t*xi)`
becomes the project kernel `exp(2*pi*i*x*y)`. The global natural extension on
`L2(R)` remains a separate operator.

Verdict: `D0.3f = PROVED / EXTERNAL_PRIMARY_SOURCE_LOCKED`.

Exit: `PROLATE_SELFADJOINT_REALIZATION_LOCKED`.

## 8. D0.3g — canonical detector operator

Architectural review ratified the already proved finite Riesz operator under
the scoped name

```text
Mfin_m_N := WeilOp_m_N : E_m_N -> E_m_N.
```

Its ordered ON basis is `(V_-N_m,...,V_N_m)`, Gram is `I`, and matrix is
`WeilMat_m_N`. Exact centrosymmetry proves that the reversal involution reduces
it into even and odd sectors of dimensions `N+1` and `N`. The full spectrum is
named `nu_j`; sector spectra are `epsilon_plus_j` and `epsilon_minus_j`.
Static-Schur quantities retain the distinct name `theta_j`.

The complete proof, decomposition, review classification, and eight
falsifiers are in:

```text
D0_3G_CANONICAL_FINITE_WEIL_DETECTOR.md
D0_3G_DECOMPOSITION_CONTRACT.md
D0_3G_PRO_REVIEW_DECISION.md
D0_3G_CERTIFICATE.json
```

This does not define `M_lambda`, prove a strict sector gap, identify
`nu_3-nu_1` with an even-sector gap, choose `N(lambda)`, or connect the finite
carrier to `Dlog^(lambda,N)`.

Verdict: `D0.3g = PROVED / SOURCE_LOCKED / LEAN_UNPINNED`.

Exit: `D03G_CANONICAL_WEILOP_LOCKED`.

## 9. D0.3h — nonconflation firewall

The registry proves the following negative bookkeeping statements.

1. `A_m` and `Dlog_m` share `H_m` but not their defining domain/action/source;
   moreover `A_m` is lower bounded whereas the spectrum of `Dlog_m` is the
   two-sided set `(2*pi/L)Z`, so they are not equal.
2. `WeilOp_m_N` acts on finite `E_m_N`; without operator-domain membership and
   invariance it is not a restriction of `A_m`.
3. `PertRaw_m_N_xi` is `xi`-indexed and is not granted the modified-space
   selfadjoint theorem in the standard `H_m` metric.
4. `PWExpr_m` lives on additive `x in [-lambda,lambda]`, whereas `A_m` and
   `Dlog_m` live on multiplicative positive `u`. No unitary/intertwiner is
   supplied here.
5. `Mfin_m_N` is not `M_lambda`, `Dlog^(m,N)`, a Schur operator, or a prolate
   pilot; all such crosswalks require separate theorems.
6. `G_even` is a Weil compression, not a Gram matrix; the scalar zero profile
   `K_N(gamma)`, a Schur matrix `K`, and the transcript symbol `K_N` are three
   different types.

Verdict: `D0.3h = PROVED / NO_EQUALITY_ASSERTED / LEAN_UNPINNED`.

## 10. Lamport assembly status

```text
<1>1. D0.3.0 defines D0.3 as an eight-field AND record.
<1>2. D0.3a is proved by the representation and compact-resolvent theorems.
<1>3. D0.3b is proved by periodic derivative spectral theory and the unitary
      coordinate map kappa_m.
<1>4. D0.3c is proved by finite-dimensional Riesz representation.
<1>5. D0.3d is proved only as a parameterized/conditional type split; no H2a
      conclusion is drawn.
<1>6. D0.3e is proved as a formal differential expression.
<1>7. D0.3f is proved by the versioned Katsnelson source plus exact unitary
      scaling to the project operator.
<1>8. D0.3g is proved by exact finite Riesz representation, source matrix
      parity, finite spectral theory, and the ratified namespace firewall.
<1>9. D0.3h proves the nonconflation firewall.
<1>10. All eight children are proved, so D0.3i constructs the D0.3 record.
```

Conclusion:

```text
D0.3 = PROVED
EXACT_OPERATOR_TYPES_LOCKED
NOT_RH
```

D0.6 is proved independently. The compiler advances to D0.4, which projects
and packages the exact parity-sector theorem without importing a bottom-three
ordering or numerical cleanliness claim.

## 11. Planted falsifiers

- `FORM_DOMAIN_ONLY`: applying `A_m` to a vector known only to lie in the form
  domain must be rejected.
- `WRONG_DLOG_DOMAIN`: the function `F(x)=x` lies in `H1([0,L])` but fails the
  periodic trace condition.
- `FINITE_COMPRESSION_ALIAS`: for
  `A=[[0,1],[1,0]]` and `E=span(e1)`, the form compression is `[0]` while
  `A(e1)=e2` is outside `E`.
- `MISSING_XI`: two normalized vectors with different `Dlog xi` produce
  different raw perturbations.
- `SELFADJOINTNESS_SMUGGLE`: the adjoint of
  `-|Dlog xi><delta|` is `-|delta><Dlog xi|`; they need not agree.
- `PW_SPACE_ALIAS`: a legal additive input at negative `x` is not a positive
  multiplicative coordinate `u`.
- `DETECTOR_ALIAS`: validation must fail if `Mfin_m_N` is renamed `M_lambda`
  or identified with `G_even`, a Schur complement, or a prolate pilot.
- `QW_SHIFT_DEPENDENCY`: replacing `QW` by `QW+t||.||^2` shifts `A_m` and
  `WeilOp_m_N` by `tI`, but does not shift `Dlog_m` or `PWExpr_m`.

## 12. Explicit nonclaims

```text
NO_M_LAMBDA
NO_SIMPLE_EVEN_GROUND
NO_STANDARD_H_SELFADJOINT_PERTURBATION
NO_WEILMAT_EQUALS_A_RESTRICTION
NO_PROLATE_WEIL_OPERATOR_EQUALITY
NO_D0_ASSEMBLY
NO_H1_H4
NO_RH
```
