# 011 — CONCRETE_HTRIAL_SOURCE_LOCK

Date: `2026-07-27`

Scope: source-lock and algebraic audit only; `CHALLENGER / NOT_RH`;
`BUS_010_VOID`; no STATE mutation.

```text
HTRIAL_IS_FREE_PARAMETER
H2_ZERO_CONFIRMED
HTRIAL_POINTWISE_SIGN_CONSTANT: NO
MELLIN_CROSSWALK: PROSHKA_VERIFIED_WITH_CORRECTION
```

## 1. Concrete \(hTrial_m\) source lock

### 1.1 What the already cited Stage-2 ranges say verbatim

`D0_5_GROUND_AND_TRIAL_TYPES.md:81-92`:

```text
## 3. Multiplicative and finite trial objects

Using the source's midpoint representative and starred summation map, define

gTrial_m
 := E_star(hTrial_m) restricted to [lambda^-1,lambda] in H_m,
gTrial_m_N := P_m_N(gTrial_m) in E_m_N.

The endpoint midpoint convention changes pointwise boundary identities but not
the H_m vector or its orthogonal projection.
```

`PEN_3_3_G04_OBJECT_DICTIONARY.md:112-133`:

\[
  h_\lambda^*(x):=
  \begin{cases}
    h_\lambda(x), & |x|<\lambda,\\
    \tfrac12h_\lambda(\lambda^-), & x=\lambda,\\
    \tfrac12h_\lambda(-\lambda^+), & x=-\lambda,\\
    0, & |x|>\lambda,
  \end{cases}
\]

\[
  \mathcal E_*(f)(u):=u^{1/2}\sum_{m\ge1}f^*(mu),
  \qquad
  \boxed{g_\lambda:=\mathcal E_*(h_\lambda)
    \big|_{[\lambda^{-1},\lambda]}}.
\]

Lines `141-160` add the exact half-weight at comb teeth and state that changing
these finitely many point values does not change the \(L^2(du/u)\) element,
Fourier coefficients, or Weil quadratic-form value. Lines `169-212` define
\(\mathcal H_\lambda\), the normalization \(k_{1,\lambda}\), the Fourier basis,
the projection \(P_{\lambda,N}\), and \(g_{\lambda,N}=P_{\lambda,N}g_\lambda\).

`fulltext.md:1262-1267`:

```text
where one uses the following map E:
E(f)(u) := u^(1/2) sum_(n=1)^infinity f(nu)                 (7.2)
```

`fulltext.md:1293-1297`:

```text
PW_lambda := -partial_x (lambda^2-x^2) partial_x
             +(2*pi*lambda*x)^2                            (7.5)

k_lambda(u) := E(h_lambda)(u), for all u in
[lambda^(-1),lambda]                                       (7.6)
```

and \(h_\lambda\) is described there as, up to a multiplicative scalar, the
only linear combination of \(h_{0,\lambda},h_{4,\lambda}\) with vanishing
integral.

`fulltext.md:1410-1419` applies \(E\) only on
\([\lambda^{-1},\lambda]\) and derives

\[
 |E(h_\lambda)(u)-E(h)(u)|
 \le u^{1/2}\delta(\lambda)\frac{\lambda}{u}.
\]

**Source-lock finding.** None of those already cited ranges supplies the
coefficients or normalization of \(hTrial_m\). They start with an already
chosen \(h_\lambda\)/`hTrial_m`.

### 1.2 The concrete formula, located immediately before the cited ranges

The missing D0 definition is verbatim at
`D0_5_GROUND_AND_TRIAL_TYPES.md:55-69`:

```text
Put lambda=sqrt(m) and C_lambda=2*pi*lambda^2. Let
h_0_lambda,h_4_lambda be the real, L2-normalized prolate eigenfunctions with
the source phase

I_0_lambda=integral h_0_lambda>0,
I_4_lambda=integral h_4_lambda>0.

Define

D_lambda=sqrt(I_0_lambda^2+I_4_lambda^2),
hTrial_m=(I_4_lambda*h_0_lambda-I_0_lambda*h_4_lambda)/D_lambda.
```

The same formula is typeset at
`PEN_3_3_G04_OBJECT_DICTIONARY.md:81-95`:

\[
 I_{0,\lambda}:=\int h_{0,\lambda},\qquad
 I_{4,\lambda}:=\int h_{4,\lambda},\qquad
 D_\lambda:=\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2},
\]

\[
 \boxed{
 h_\lambda
 :=\frac{I_{4,\lambda}h_{0,\lambda}
          -I_{0,\lambda}h_{4,\lambda}}{D_\lambda}.}
\]

Its components are fixed at dictionary lines `39-56`:

\[
 \widetilde h_{n,\lambda}(x)
 :=\operatorname{PS}_{n,0}\!\left(2\pi\lambda^2,\frac{x}{\lambda}\right),
 \quad |x|<\lambda,
\]

then zero-extended, \(L^2([-\lambda,\lambda],dx)\)-normalized, and signed by
\(I_{n,\lambda}>0\), for \(n=0,4\). The midpoint representative used by
\(\mathcal E_*\) is the piecewise \(h_\lambda^*\) above.

### 1.3 Why the result is still `HTRIAL_IS_FREE_PARAMETER`

The mathematical source fixes \(hTrial_m\), but the current Lean D0 chain does
not construct \(h_{0,\lambda}\), \(h_{4,\lambda}\), their integrals,
\(D_\lambda\), or the midpoint extension.

```lean
def E_star (hTrial_m : ℝ → ℂ) (u : ℝ) : ℂ := ...

def gTrial_m
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star : MemLp (E_star hTrial_m) 2 ...) : H_m i := ...
```

Source: `D0KTrialStage2.lean:24-26,41-47`. Stage 3 propagates the same free
argument through `TrialNonzero`, `sTrial_m_N`, `kTrial_m_N`, and `c_n`
(`D0KTrialStage3.lean:18-23,33-38,49-57,81-89`).

The choice is assumed at `D0KTrialStage2.lean:33-34`: “The prolate constructor
that supplies the midpoint representative must also supply this standard
membership certificate.” That concrete prolate constructor is absent.

Therefore:

```text
SPECIFICATION: concrete and normalized.
CURRENT LEAN OBJECT: free parameter hTrial_m plus MemLp certificate.
SOURCE-LOCK GAP: Stage-2 citations omit the coefficient formula at
                 D0.5:55-69 / dictionary:81-95.
```

## 2. Decisive \(H2\) mass fork

The source modes \(h_{0,\lambda}\) and \(h_{4,\lambda}\) are even
(`fulltext.md:1293-1297`, specifically line `1295`) and vanish outside
\([-\lambda,\lambda]\). Therefore

\[
 \int_0^\infty h_{n,\lambda}(v)\,dv
 =\int_0^\lambda h_{n,\lambda}(v)\,dv
 =\frac12\int_{-\lambda}^{\lambda}h_{n,\lambda}(v)\,dv
 =\frac12 I_{n,\lambda}
 \qquad(n=0,4).
\]

Substitution into the exact packet formula gives

\[
\begin{aligned}
A_m
&:=\int_0^\infty hTrial_m(v)\,dv\\
&=\frac{1}{D_\lambda}
  \left(
    I_{4,\lambda}\frac{I_{0,\lambda}}2
    -I_{0,\lambda}\frac{I_{4,\lambda}}2
  \right)\\
&=\boxed{0}.
\end{aligned}
\]

Here \(D_\lambda>0\), because
\(I_{0,\lambda}>0\), \(I_{4,\lambda}>0\), and
\(D_\lambda=\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2}\).

```text
H2_ZERO_CONFIRMED
A_m = 0 identically for every m in the D0 family.
No pole counterterm A_m * J_lambda(s) occurs.
```

The midpoint endpoint convention does not affect this Lebesgue integral.

### Planted sign test

The packet is real, has norm one, and has zero positive-half mass. It cannot
be pointwise nonnegative or pointwise nonpositive: either condition together
with the zero integral would force it to vanish almost everywhere on
\((0,\infty)\); evenness would then force it to vanish almost everywhere on
\(\mathbb R\), contradicting \(\|hTrial_m\|_2=1\).

```text
HTRIAL_POINTWISE_SIGN_CONSTANT: NO
```

In fact its positive and negative sets both have positive measure; for the
continuous prolate representative, both signs are attained pointwise. The
viable future sign target is therefore at the summed
\(\mathcal E_*(hTrial_m)\) level, not at the \(hTrial_m\) level.

## 3. Mellin crosswalk disposition

The independent Mythos-line verification is superseded by
`proshka/PROSHKA_MELLIN_CROSSWALK_2026-07-27.md`:

```text
UNWINDOWED_MELLIN_MULTIPLIER_CORRECT_CONDITIONAL
```

That verdict records the Müntz continuation with the zero-mass condition and
the exact window correction. The present calculation supplies its requested
branch input:

```text
H2-ZERO, not H2-POLE.
```

## ACTIONS LOG

Files written:

```text
ACTIVE/requests/routeB_lamport_rh_closure/
  011_concrete_htrial_source_lock.answer.md
```

Immutable source SHA-256:

```text
9cb7a9e34d0d051fc78c9c7a69e71fc91e7c7722f3d8c9a5713469d4f3bd5547
  D0_5_GROUND_AND_TRIAL_TYPES.md
010282dda8b76e8a9e0ea184f14a62d34f60b0d4b588f8f0e541b97a959ef71e
  PEN_3_3_G04_OBJECT_DICTIONARY.md
7ba4b01845df2989cdd763a19c83904e4114e26fc51d5d7f93d09489d52871d4
  fulltext.md
aabaf47cb484f0157fd7b2ac4f30811aec9595116c1193715e41de8b520393cd
  D0KTrialStage2.lean
924027a3dd9b95e75c776db552ad37779ed8dd75a7924d744a39cb1a613ebdfa
  D0KTrialStage3.lean
ed2217c1b65cf640b388fc26586f9eeb56340fcee8b7e06402c88f053381b3fa
  proshka/PROSHKA_MELLIN_CROSSWALK_2026-07-27.md
```

Commands: numbered source extraction with `nl -ba`; exact-token search with
`rg`; SHA-256 with `shasum -a 256`; mass algebra checked directly from
evenness and the two exact source integrals. No numerical datasets or grids
were used.

State:

```text
STATE.json: untouched
ROUTE_B_STATE.md: untouched
ROUTE_B_EXECUTION_STATE.json: untouched
Bus 010: not created
```
