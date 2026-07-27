# SOFT_L2 — ExactProjectionDefectLagEquation

Status: `SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED / NOT_RH`

Authority: the materialized
`SOFT_L2_PRO_VERDICT_ROUND9_2026-07-13.md` and
`SOFT_L2_PRO_VERDICT_ROUND10_2026-07-13.md`, read jointly: the exact
`CODEX DIRECTIVE` ledger of round 9 with the admissibility and diagnostic
refinements of round 10. No round-9 obligation is weakened.

This leaf locks an exact operator identity and its projection ledger. It does
not assert asymptotic smallness, a limiting equation, uniqueness, or RH.

## 1. Typed inputs and the domain firewall

Work in the additive log-coordinate Hilbert space

```text
H = L2(R,du),                 (U_a f)(u)=f(u-a),
<.,.> antilinear in the first slot.
```

Fix `L>0`, `I_L=[-L/2,L/2]`, and let

```text
P_L       = orthogonal multiplication projection 1_(I_L),
Q_L       = I-P_L,
Pi_(m,N)  = orthogonal Galerkin projection onto the zero-extended
            Fourier carrier with indices -N,...,N,
Pi_sec    = the selected parity-sector projection.
```

The centered window and symmetric Fourier carrier give the nesting and
commutation relations

```text
Pi_(m,N) P_L = P_L Pi_(m,N) = Pi_(m,N),
Pi_sec Pi_(m,N) = Pi_(m,N) Pi_sec.
```

The **full finite carrier projection** is therefore

```text
S_(m,N) := Pi_sec Pi_(m,N) P_L.
```

It is an orthogonal projection, not merely a product name. Fix a normalized
finite ground vector `q` and eigenvalue `mu` with

```text
S_(m,N) q = q,       ||q||_2=1.
```

Let

```text
T_full = T_Arch - T_prime,
T_prime = sum_n w_n (U_(ell_n)+U_(-ell_n)),
w_n=Lambda(n)/sqrt(n),       ell_n=log n,
M = S_(m,N) T_full S_(m,N) + C_corr,
M q = mu q.
```

`C_corr` is the exact pole/midpoint correction operator with the displayed
`+C_corr` sign. The operator statement is made on the explicit domain

```text
q in Dom(T_Arch) intersect Dom(T_prime),
T_full q in H,               C_corr q in H.
```

This hypothesis is load-bearing. D0.2 proves that the finite Fourier carrier
lies in the **form** domain, while D0.3 explicitly does not identify the
finite Riesz operator with `P A_m P` or prove `E_(m,N) subset Dom(A_m)`.
Accordingly this leaf neither derives the domain statement from D0.2 nor
rewrites the Arch term as a convolution without an additional domain/kernel
theorem. The exact ledger below is the operator theorem under the typed input
required by the directive; the numerical ledger in Step 2 uses the exact
Weil functional directly and makes no operator-domain inference.

## 2. Master projection identity

Define the full autocorrelation

```text
A(t) := <U_t q,q>.
```

Test `M q=mu q` against `S U_t q`. Since `S=S*=S^2` and `Sq=q`,

```text
<S U_t q,T_full q> + <S U_t q,C_corr q> = mu A(t).
```

Adding the omitted orthogonal component gives, exactly,

```text
<U_t q,T_full q>
  = mu A(t) + E_proj(t) + E_corr(t),                 (2.1)

E_proj(t) = <(I-S)U_t q,T_full q>,                  (2.2)
E_corr(t) = -<S U_t q,C_corr q>.                    (2.3)
```

Equation (2.2) is the required identity

```text
Eproj = <(I-S) U_t q,T_full q>.
```

No component has yet been called a boundary term.

With the D0.6 shift convention,

```text
<U_t q,T_prime q>
  = sum_n w_n [A(t-ell_n)+A(t+ell_n)].
```

If `L_Arch[A](t):=<U_t q,T_Arch q>`, (2.1) becomes the exact lag
equation

```text
L_Arch[A](t)
 - sum_n w_n [A(t-ell_n)+A(t+ell_n)]
 = mu A(t) + E_proj(t) + E_corr(t).                 (2.4)
```

`L_Arch[A]` is notation for the displayed pairing, not an unproved
convolution or a `Re xi'/xi` substitution.

## 3. Exact five-component decomposition

The nested projections give the orthogonal telescope

```text
I-S = R_win + R_Gal + R_sec,
R_win = Q_L,
R_Gal = P_L-Pi_(m,N)P_L,
R_sec = Pi_(m,N)P_L-S.
```

Thus the right side of (2.4) splits into exactly five named components:

```text
E_win(t)      = -<R_win U_t q,T_prime q>,
E_Gal(t)      =  <R_Gal U_t q,T_full q>,
E_sec(t)      =  <R_sec U_t q,T_full q>,
E_polemid(t)  = -<S U_t q,C_corr q>,
E_Arch(t)     =  <R_win U_t q,T_Arch q>.            (3.1)
```

Therefore

```text
E_proj = E_win + E_Gal + E_sec + E_Arch,
E_corr = E_polemid,
E_total = E_win+E_Gal+E_sec+E_Arch+E_polemid.       (3.2)
```

The five ledger rows are, in the directive's order:

1. window/prime-shift commutator;
2. Galerkin finite-carrier defect;
3. parity-sector defect;
4. pole/midpoint correction;
5. Arch window-truncation defect.

The Galerkin row is present even when it is numerically inconvenient. No
support theorem is claimed for `E_Gal`; in general it has no compact support
as a function of `t`. The same warning applies to `E_Arch` for a nonlocal
Arch operator and to the aggregate correction row.

## 4. Window-shift formula and exact support

For one shift `a`, put

```text
D_(a,L)(t) := <Q_L U_t q,Q_L U_a q>.
```

Because `q=P_L q` and `Q_L` is orthogonal,

```text
<P_L U_t q,P_L U_a q> = A(t-a)-D_(a,L)(t),

E_win(t) = -sum_n w_n
  [D_(ell_n,L)(t)+D_(-ell_n,L)(t)].                 (4.1)
```

The translated support of `q` lies in `I_L+t`. The two outside-window
pieces can overlap only on the same side of `I_L`, and the two translated
copies can overlap only when their displacement has magnitude below `L`.
Hence the exact implication is

```text
D_(a,L)(t) != 0  ==>  t*a>0 and |t-a|<L.           (4.2)
```

This is only a support implication for each window-shift term. It does not
say that the full projection defect is compactly supported, nor that the
window source lives only at large lags. In particular, for fixed `a>0`,
small positive `t` is allowed by (4.2).

## 5. Same-unit estimates

Define the L2 boundary scale

```text
r_L(a) := ||Q_L U_a q||_2.
```

For `0<a<L` and `-L<a<0`, respectively,

```text
r_L(a)^2 = integral_(L/2-a)^(L/2) |q(u)|^2 du,
r_L(a)^2 = integral_(-L/2)^(-L/2-a) |q(u)|^2 du.   (5.1)
```

Cauchy--Schwarz now stays in L2 units:

```text
|D_(a,L)(t)| <= r_L(t) r_L(a),                     (5.2)

|E_win(t)| <= r_L(t) sum_n w_n
  [r_L(ell_n)+r_L(-ell_n)],                        (5.3)

|E_Arch(t)| <= r_L(t) ||Q_L T_Arch q||_2.          (5.4)
```

For completeness, the other orthogonal rows have their own native scales

```text
g_(m,N)(t) = ||R_Gal U_t q||_2,
s_(m,N)(t) = ||R_sec U_t q||_2,

|E_Gal(t)| <= g_(m,N)(t) ||R_Gal T_full q||_2,
|E_sec(t)| <= s_(m,N)(t) ||R_sec T_full q||_2,
|E_polemid(t)| <= ||S U_t q||_2 ||C_corr q||_2.
```

Equations (5.2)--(5.4) are estimates, not smallness claims. No limit in
`m`, `N`, or `L` is taken here.

## 6. Both shift plants

### Plant A — move `q` relative to the fixed window

Keep `P_L`, `Pi_(m,N)`, and `S` fixed and replace `q` by `q_b=U_b q`.
Then

```text
A_(q_b)(t)=A_q(t),
D^(fixed)_(a,L;b)(t)
  = <Q_L U_(t+b)q,Q_L U_(a+b)q>.
```

The autocorrelation is inert but the window row generally changes. An
explicit planted witness is `L=2`, normalized
`q=1_[-1/2,1/2]`, `t=a=1/4`, `b=4/5`: the unshifted window defect is zero,
whereas the fixed-window shifted defect has positive overlap length `11/20`.
Thus the commutator is visible and
`SOFT_L2_WINDOW_SHIFT_COMMUTATOR_MISSING` does not fire.

Round 10 correctly notes that, after a later real-even canonical ground lock,
this relative translation is not an admissible competing ground state. Here
it remains a valid **planted falsifier of the formula**, not a symmetry claim
about the ground family.

### Plant B — translate `q` and the complete carrier together

Put

```text
P_L^b=U_b P_L U_(-b),
Pi_(m,N)^b=U_b Pi_(m,N) U_(-b),
Pi_sec^b=U_b Pi_sec U_(-b),
S^b=U_b S U_(-b),
q_b=U_b q.
```

Conjugate every translation-covariant full operator and the correction by
the same unitary. Then every pairing in (2.1)--(3.2), including
`D_(a,L)(t)`, is unchanged. The equation is covariant under the simultaneous
shift. Hence `SOFT_L2_SHIFT_PLANT_INERT` does not fire.

## 7. Stop-code audit and closeout

```text
SOFT_L2_WINDOW_SHIFT_COMMUTATOR_MISSING   NOT_FIRED (Plant A)
SOFT_L2_GALERKIN_SHIFT_DEFECT_MISSING     NOT_FIRED (E_Gal explicit)
SOFT_L2_ARCH_DOMAIN_GAP                   GUARDED_BY_EXPLICIT_OPERATOR_DOMAIN;
                                           no source-domain inference
SOFT_L2_CORRECTION_LEDGER_MISSING         NOT_FIRED (E_polemid explicit)
SOFT_L2_BOUNDARY_SCALE_UNPROVED           NOT_FIRED ((5.1)--(5.4))
SOFT_L2_SHIFT_PLANT_INERT                 NOT_FIRED (Plant B covariance)
```

Success code:

```text
SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED
```

Scope: exact algebraic/operator ledger under its displayed domain input.
This is `NOT_RH`. It does not activate D0.7e.5a, does not mint a theorem for
the full Route-B closure, and does not create Bus 010.
