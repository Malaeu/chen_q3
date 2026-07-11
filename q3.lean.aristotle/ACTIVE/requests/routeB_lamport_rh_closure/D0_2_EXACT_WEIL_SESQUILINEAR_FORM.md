# D0.2 — ExactWeilSesquilinearForm

Status: `MATH_PROVED / PRIMARY_SOURCE_LOCKED / LEAN_INTERFACE_UNPINNED / NOT_RH`

Progress class: `PROOF_PROGRESS`

This leaf fixes the exact Weil functional, its lower-semicontinuous window
form, the associated sesquilinear form, and its finite matrix restriction on
the already locked space `E_(m,N)`. It does not assert positivity, identify a
ground vector, or use the RH-equivalent asymptotic corollary located later in
the source.

## 1. Leaf contract

### Statement

For every D0.1 index `(m,N)` with `m>=2`, `N>=1`, let

```text
lambda = sqrt(m),
L      = log(m),
H_m    = L2([lambda^-1,lambda],du/u),
E_m_N  = span_C{V_n_m : |n|<=N}.
```

There is an exact lower-bounded lower-semicontinuous quadratic form

```text
qW_m : H_m -> R union {+infinity}
```

with form domain

```text
Dom(qW_m) = {f in H_m : qW_m(f)<+infinity}.
```

Its polarization `BW_m` is antilinear in the first variable, linear in the
second, and Hermitian. Every `E_m_N` lies in the form domain. Define

```text
BW_m_N = BW_m restricted to E_m_N x E_m_N,
qW_m_N(f) = BW_m_N(f,f).
```

In the ordered ON basis `(V_-N_m,...,V_N_m)`, the matrix

```text
T_m_N = (tau_(r,s)),
tau_(r,s)=BW_m(V_r_m,V_s_m),
```

is real symmetric. If

```text
f=sum_r c_r V_r_m,
g=sum_s d_s V_s_m,
```

then exactly

```text
BW_m_N(f,g) = sum_(r,s) conjugate(c_r) tau_(r,s) d_s,
qW_m_N(f)   = c^* T_m_N c.
```

No claim `qW_m>=0` is made.

### Type inventory

- functions: complex-valued;
- group: `R_+^*` with Haar measure `d^*u=du/u`;
- involution: the group-algebra involution that makes `f^* * g`
  antilinear in `f`;
- functional codomain on the core: `C`, real on diagonal inputs;
- closed quadratic form codomain: `R union {+infinity}`;
- form domain: generally a proper dense subspace of `H_m`;
- finite restriction: a Hermitian form on the concrete complex space
  `E_m_N`, represented by a real symmetric `(2N+1)`-square matrix;
- coefficient convention: column vectors ordered from `-N` through `N` and
  conjugate transpose on the left.

### Parent contract

`D0.2` supplies the exact-form component of the AND assembly D0. It consumes
D0.1 and does not imply D0 alone.

### Dependencies

- D0.1 `EXACT_HILBERT_SPACE_AND_NORM_LOCKED`;
- source definitions (3.3), (3.5), (3.7), (3.10)–(3.16);
- source Propositions 3.3–3.4 and Lemma 5.1;
- elementary expansion of a sesquilinear form in a finite basis.

No ZEO, alpha detector, RH-zero statistic, or RH-conditional theorem is used.

### Two proof routes

1. Primary-source route: lock the exact functional and import the source's
   lower-bounded/l.s.c. theorem plus its finite real-symmetric matrix lemma.
2. Polarization route: start from the real diagonal quadratic form, recover
   the Hermitian form by polarization, then expand it in the D0.1 ON basis and
   independently test signs/conjugation.

Both routes agree; route 1 supplies the analytic theorem and route 2 validates
the finite algebra.

## 2. Exact functional and sign convention

The source first has a Mellin-class function `f`, then passes to the
half-density

```text
F(x)=x^(1/2) f(x).
```

D0.2 uses this half-density `F` in `L2(d^*u)`; it never silently inserts the
original Mellin `f` into the Hilbert form. For suitable compactly supported
half-densities, define

```text
Fhat(t) = integral_(R_+^*) F(u) u^(-i*t) d^*u.
```

The non-archimedean terms are

```text
W_p(F) = (log p) sum_(a>=1) p^(-a/2) [F(p^a)+F(p^(-a))].
```

The endpoint/pole term is

```text
W_0_2(F)=Fhat(i/2)+Fhat(-i/2).
```

The archimedean distribution `W_R` is the source distribution (3.8), or
equivalently its explicit multiplicative formula preceding (3.8). The Weil
functional has the exact sign ledger

```text
Psi(F) = W_0_2(F) - W_R(F) - sum_p W_p(F).
```

For the multiplicative convolution and involution,

```text
F^*(u)=conjugate(F(u^-1)),
QW(f,g)=Psi(f^* * g).
```

The source also supplies the one-sided distribution

```text
Psi_sharp = W_0_2_sharp - W_R_sharp - sum_p W_p_sharp
```

on `[1,infinity)`, with

```text
Psi(h)=Psi_sharp(h+h o inversion).
```

The factor `1/2` in `W_R_sharp` is part of the definition and must not be
dropped.

## 3. Exact window and finite restriction

The source defines `qW_m` as the restriction/closure of the Weil quadratic
form to `H_m`. It proves:

```text
qW_m is lower bounded and lower semicontinuous;
E=span{V_n:n in Z} is a form core;
the minimum of qW_m_N converges to the lower bound as N->infinity.
```

For modes in the core,

```text
tau_(r,s)
 = BW_m(V_r_m,V_s_m)
 = Psi_sharp(F_(r,s)),
F_(r,s)(u)=q(U_r_m,U_s_m)(log u).
```

Equivalently, with the real distribution

```text
D_m = log_*(Psi_sharp)
```

on `[0,L]`,

```text
tau_(r,s)=integral_[0,L] q(U_r_m,U_s_m)(y) D_m(y).
```

Here the last expression is distributional pairing notation, not an
unjustified Lebesgue-density assertion. The source's Lemma 5.1 proves that
`T_m_N` is real symmetric and has the structured entries

```text
tau_(r,r)=a_r,
tau_(r,s)=(b_r-b_s)/(r-s) for r!=s,
a_(-r)=a_r,
b_(-r)=-b_r.
```

To prevent name collisions, this compiler reserves:

```text
PrimeShift_(lambda,k)  for the bounded prime-shift operator in (3.20),
WeilMat_(m,N)          for the finite matrix (tau_(r,s)),
ShiftedWeilMat_(m,N)   for the later matrix QW^N-epsilon*I.
```

## 4. Lamport proof

### Theorem D0.2

The objects in Sections 1–3 satisfy the D0.2 statement.

Proof.

`<1>1.` **The source core form is exactly sesquilinear.**

The source defines `QW(f,g)=Psi(f^**g)` by polarization and fixes inner
products to be antilinear in the first variable. Thus `QW` is antilinear in
`f` and linear in `g`. Its diagonal values are real, so the polarization is
Hermitian.

`<1>2.` **The window form has the correct closed-form type.**

Source Proposition 3.3 states that the window quadratic form is lower bounded
and lower semicontinuous on `H_m`. Therefore it is correctly typed as an
extended-real quadratic form, finite precisely on `Dom(qW_m)`, with an
associated Hermitian sesquilinear form on that domain.

`<1>3.` **The D0.1 modes are legal form-domain vectors.**

The source's `E=span{V_n:n in Z}` is a form core. Hence each finite
`E_m_N` is contained in the form domain, and restriction to it is an ordinary
finite-valued Hermitian form.

`<1>4.` **The matrix entries use the same objects and signs.**

Proposition 3.2 transports `QW` through the D0.1 unitary `kappa`; equations
(4.1) and (5.1) give the displayed `Psi_sharp`/`D_m` formula for
`tau_(r,s)`. No reconstructed detector or alternative matrix enters.

`<1>5.` **The finite matrix is real symmetric.**

Source Lemma 5.1 proves the exact real-symmetric structure. In particular

```text
tau_(r,s)=tau_(s,r)=conjugate(tau_(s,r)).
```

Thus `T_m_N` is Hermitian on the complex coefficient space.

`<1>6.` **Coefficient expansion has conjugation on the left.**

Sesquilinearity gives

```text
BW_m_N(sum_r c_r V_r, sum_s d_s V_s)
 = sum_(r,s) conjugate(c_r) d_s BW_m(V_r,V_s)
 = c^* T_m_N d.
```

Setting `d=c` yields `qW_m_N(f)=c^*T_m_Nc`, a real number.

`<1>7.` **Lower bounded does not mean positive.**

The source explicitly states that the continuum lower spectral bound cannot
be asserted nonnegative. Restriction to a finite space preserves a finite
lower bound, but supplies no sign theorem. This prevents a hidden import of
Weil positivity/RH.

Likewise, for a unit trial vector `k`, the number `qW_m_N(k)` is only a
Rayleigh value. Min–max gives `epsilon_(m,N)<=qW_m_N(k)`; equality requires
`k` to lie in the bottom eigenspace. D0.2 does not identify the project trial
value `a_1`, a pilot `mu_1`, or a Gram/Schur eigenvalue with the source bottom
eigenvalue `epsilon_(m,N)`.

`<1>8.` **No domain or operator overclaim occurs.**

The l.s.c. form is allowed to take `+infinity` outside its form domain. D0.2
does not identify it with the selfadjoint representation operator `A_lambda`;
that representation belongs to D0.3.

Steps `<1>1`–`<1>8` prove the exact leaf statement. QED.

## 5. Cheapest planted falsifiers

### F1 — prime-sign reversal

For symbolic component values `W_0_2=7`, `W_R=2`, and `sum W_p=3`, the source
ledger gives `Psi=2`. The planted `+sum W_p` gives `8`.

Expected code: `D0_2_PRIME_SIGN_PLANT_FIRES`.

### F2 — missing coefficient conjugation

For the one-dimensional matrix `[1]`, `c=i`, and `d=1`, sesquilinearity gives
`conjugate(i)*1=-i`; the planted bilinear expansion gives `+i`.

Expected code: `D0_2_CONJUGATION_PLANT_FIRES`.

### F3 — positivity smuggling

The planted statement `qW_m(f)>=0 for all f` is rejected because the source
explicitly says its lower spectral bound is not known to be nonnegative.

Expected code: `D0_2_POSITIVITY_OVERCLAIM_PLANT_FIRES`.

### F4 — everywhere-finite form

The planted type `qW_m:H_m->R` is rejected by the source type
`H_m->R union {+infinity}` and its explicit form domain.

Expected code: `D0_2_DOMAIN_OVERCLAIM_PLANT_FIRES`.

### F5 — dropped archimedean half-factor

The planted one-sided archimedean formula without the source's factor `1/2`
is rejected directly by (3.15) and its proof note.

Expected code: `D0_2_ARCH_HALF_FACTOR_PLANT_FIRES`.

### F6 — trial/eigenvalue conflation

For the diagonal matrix `diag(0,2)` and unit trial vector `(0,1)`, the
Rayleigh value is `2` while the lowest eigenvalue is `0`. This rejects the
planted identity “every trial value is the ground eigenvalue.”

Expected code: `D0_2_TRIAL_EIGENVALUE_CONFLATION_PLANT_FIRES`.

## 6. Source evidence and exclusions

Primary source `literature/zotero/H8ULBMAL/fulltext.md`:

- lines 81–95: involutive convolution and antilinear-first convention;
- lines 169–250: Weil class, multiplicative Fourier transform, local
  distributions, exact `Psi` signs, and sesquilinear `QW`;
- lines 252–289: `Psi_sharp` and the `kappa` crosswalk;
- lines 312–339: window form, lower-bounded/l.s.c. theorem, domain,
  polarization, and core;
- lines 425–442: exact matrix entry crosswalk;
- lines 702–734: finite restriction and real-symmetric matrix theorem;
- lines 418–423: explicit warning that nonnegativity is not available.

Not supplied here:

- the representation operator `A_lambda` or `D_log` — D0.3;
- parity-sector theorem — D0.4;
- a ground/trial vector — D0.5;
- transform and normalization — D0.6/D0.7;
- any operator crosswalk — D0.8;
- any identification of `a_1`, pilot `mu_1`, or a projected/Gram matrix with
  the source ground eigenvalue;
- Weil positivity, ZEO, H1–H4, or RH.

Final leaf verdict:

```text
D0.2 = PROVED
EXACT_WEIL_FORM_LOCKED
LOWER_BOUNDED_NOT_POSITIVE
LEAN_INTERFACE_UNPINNED
NOT_RH
```
