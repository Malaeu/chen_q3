# SOFT_1 — ZeroFreeGaugeAndDistributionalIdentification

Status: `G1_G3_G5_G7_TYPED / G4_LINEAR_PRIME_CROSSWALK_MISSING / NOT_RH`

Gate output: `SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC`.

This executes `SOFT_1_GATE_CONTRACT.md` against its two authorities.  It fixes
one gauge-removed contract family, source-locks the off-axis anchor, writes the
exact transform-side pairing, and audits the requested prime/Gamma reduction.
It does not prove the finite roof, local normality, S2, or RH.  It does not
activate the 5a mint and does not create Bus 010.

## 1. G1 — typed gauge corollary

Let

```text
S = {z in C : |Im z| < 1/2},
gamma_j(z) = gammaC(1/2+i z) m_j^(-i z/2),
gamma_0(z) = exp(a+i b z),  a,b in R.
```

The source lock and `GammaSoftZeroFree.lean` give
`gamma_j,gamma_0 in HolUnit(S)`.  On `BDetNonzero` define the one and only
contract family

```text
H_(m,N)(z)
 := gammaC(1/2) * (Fhat_(m,N)(z)/bDet_(m,N)) / gamma_(m,N)(z).    (1.1)
```

### Theorem `GaugeSoftSubsequenceZeroEscape`

For a sequence `j |-> (m_j,N_j)` in `BDetNonzero`, assume:

```text
(HOL)    H_j is holomorphic on S;
(RZERO)  H_j(z)=0 and z in S imply Im(z)=0;
(ANCHOR) H_j(0)=Xi(0)!=0;
(LOCAL)  {H_j} is locally uniformly bounded on S;
(ID)     every locally-uniform cluster limit F satisfies
         F=c*Xi*gamma_0 on an accumulating subset of S, for a c!=0.
```

Then `Q3.RH`.

Proof.  Division by `gamma_j` and multiplication by the nonzero scalars
`gammaC(1/2)/bDet_j` preserve holomorphy and the zero set.  Formula (1.1) and
the central calibration give `H_j(0)=Xi(0)`.  The five hypotheses are therefore
exactly the hypotheses of the proved paper theorem
`SoftSubsequenceZeroEscape`, instantiated with the fixed, j-independent unit
`gamma_0`.  Its Montel, identity-theorem, and two-component Hurwitz proof gives
RH.  No new Hurwitz argument and no varying gauge enters the limit.  QED.

Intermediate theorem-shape code: `SOFT_GAUGE_ROOF_TYPED`.

This is an implication.  The physical finite roof and `(LOCAL)` remain open;
the theorem does not silently issue either one.

## 2. G2 — exact orientation lock

Put `lambda_m=sqrt(m)` and let `g_(m,N)` be the log-coordinate representative
of `kTrial_(m,N)`.  Define the bare transform

```text
B_(m,N)(z) := integral_0^L_m g_(m,N)(x) exp(i z x) dx.           (2.1)
```

D0.6 equation (3.1), evaluated at `-z`, and D0.7e equation (2.1) give the
single forced orientation

```text
Fplus_(m,N)(z) = T_m(kTrial_(m,N))(-z)
                 = lambda_m^(-i z) B_(m,N)(z),
Fhat_(m,N)(z)  = gammaC(1/2+i z) Fplus_(m,N)(z)
                 = gamma_(m,N)(z) B_(m,N)(z),
Fhat_(m,N)/gamma_(m,N) = B_(m,N).                              (2.2)
```

Thus (1.1) is equivalently

```text
H_(m,N)=gammaC(1/2) B_(m,N)/bDet_(m,N).                        (2.3)
```

There is exactly one centering phase.  `Fplus/gamma`, a second
`lambda_m^(-iz)` factor, and a post-hoc quotient by Xi are forbidden.

## 3. G3 — central and off-axis anchors

At zero, `gamma_(m,N)(0)=gammaC(1/2)`, independently of `(m,N)`.  On
`BDetNonzero`, D0.7e gives `G=Fhat/bDet` and `G(0)=Xi(0)`.  Hence (1.1) gives

```text
H_(m,N)(0)=Xi(0).                                               (3.1)
```

Equivalently, since
`bDet=gammaC(1/2)B_(m,N)(0)/Xi(0)`,

```text
H_(m,N)(z)=Xi(0) B_(m,N)(z)/B_(m,N)(0).                        (3.2)
```

If central nonvanishing is unavailable but the finite real-zero roof is
available, use the fixed functional `ell(f)=f(i/4)` and define

```text
H^quarter_(m,N)(z)
 := Xi(i/4) B_(m,N)(z)/B_(m,N)(i/4).                           (3.3)
```

The roof makes `B_(m,N)(i/4)!=0`: a zero-free gauge preserves zeros and
`i/4` is nonreal in `S`.  `SOFT_ZETA_ONE_QUARTER_SOURCE_LOCK.json` pins

```text
eta(1/4)>0,
1-2^(3/4)<0,
zeta(1/4)<0,
Xi(i/4)=xi(1/4)!=0.                                            (3.4)
```

This source lock is unconditional and contains no RH input.  The fallback is
well-defined conditional on the finite roof.  It does **not** give a uniform
lower bound on `|B_(m,N)(i/4)|`; therefore
`NONREAL_ANCHOR_UNIFORM_CONTROL` remains `OPEN`, and (3.3) does not prove
`(LOCAL)`.

## 4. G4 — exact pairing and the type obstruction

Fix a compact real interval `I` and a test function
`phi in C_c^infinity(I)`.  To avoid Hilbert-space conjugation ambiguity, use
the bilinear distribution pairing

```text
P_I(f,phi) := integral_I f(t) phi(t) dt.                        (4.1)
```

Write the finite trial vector in D0.1 coordinates as

```text
g_(m,N)(x)=L_m^(-1/2) sum_(|n|<=N) c_n exp(2*pi*i*n*x/L_m).
```

Equations (2.1)--(2.2), Fubini on the compact rectangle
`[0,L_m] x supp(phi)`, and the finite Fourier expansion give the exact linear
formula

```text
P_I(Fhat_(m,N),phi)
 = integral_0^L_m g_(m,N)(x) K_(m,phi)(x) dx
 = sum_(|n|<=N) c_n A_(m,phi,n),                                (4.2)

K_(m,phi)(x)
 := integral_I gammaC(1/2+i t) lambda_m^(-i t)
               exp(i t x) phi(t) dt,

A_(m,phi,n)
 := L_m^(-1/2) integral_0^L_m exp(2*pi*i*n*x/L_m)
                         K_(m,phi)(x) dx.                       (4.3)
```

Formula (4.2) is the requested Parseval/Fubini reduction on the support of
`kTrial`.  It is finite and exactly linear in the coefficient vector `c`.
Its side is `TRANSFORM_SIDE`; it contains the completed Gamma factor but no
prime or prime-power distribution.

The source-locked prime/Gamma ledger has a different input type.  D0.2 and
the H8 primary source lock

```text
Psi(h) = W_0_2(h) - W_R(h) - sum_p W_p(h),                      (4.4)
W_p(h) = log(p) sum_(a>=1) p^(-a/2)[h(p^a)+h(p^(-a))],
W_0_2(h)=hhat(i/2)+hhat(-i/2),
QW(f,g)=Psi(f^* * g).                                          (4.5)
```

The term ledger is:

| term | side | source lock | relation to (4.2) |
|---|---|---|---|
| `W_p(h)` | prime/prime-power | H8 (3.7), D0.2 section 2 | defined only after a legal Weil test `h` is supplied |
| `W_R(h)` | archimedean Gamma | H8 (3.8)--(3.9), D0.2 section 2 | defined only after the same `h` is supplied |
| `W_0_2(h)` | pole/endpoint | H8 (3.11), D0.2 section 2 | defined only after the same `h` is supplied |
| `sum_rho hhat((rho-1/2)/i)` | full zero side | H8 (3.2)--(3.6) | unconditional only with all nontrivial zeros, not a critical-line list |
| `P_I(Fhat,phi)` | transform side | D0.6 and D0.7e | formula (4.2); no source theorem identifies it with `Psi(h)` |

To turn (4.2) into the demanded prime/Gamma expression one needs a new,
source-locked **linear crosswalk** assigning a legal Weil test
`h_(m,N,phi)` such that

```text
P_I(Fhat_(m,N),phi)=Psi(h_(m,N,phi)).                           (4.6)
```

No such theorem occurs in D0.2, D0.6, D0.7e, or H8.  Parseval proves (4.2),
not (4.6).  The only locked route from `kTrial` to `Psi` is the
sesquilinear route `h=f^**g`, used for `QW` and finite matrix entries.

### Registered phase falsifier

Replace `kTrial` by `exp(i theta) kTrial`.  The left side of (4.2) is
multiplied by `exp(i theta)`.  In contrast,

```text
(exp(i theta)kTrial)^* * (exp(i theta)kTrial)
 = kTrial^* * kTrial,
```

so all currently locked diagonal Weil/quadratic data are unchanged.  Thus
those data cannot determine the requested linear pairing.  The planted
identification (4.6) is not merely unproved numerically; it is absent at the
type level.

Consequently G4 fails with
`SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC`.

## 5. G5 — joint-limit quantifier

The S2 wall is posed, not proved, on an explicit product-tail filter.  Let
`A` be a fixed cofinal admissible carrier contained eventually in the same
`BDetNonzero` and finite-roof locus used in Sections 1--4.  With one fixed
`c!=0` and one fixed `gamma_0(z)=exp(a+i b z)`, the exact target is

```text
for every compact real I, every phi in C_c^infinity(I), and every eps>0,
there exist M>=2 and N0>=1 such that for every (m,N) in A,
  m>=M and N>=N0 imply
  |P_I(H_(m,N),phi) - c*P_I(Xi*gamma_0,phi)| < eps.             (5.1)
```

This is `(m,N)->infinity` in the product order, uniform over every sufficiently
large independent pair in `A`.  It is not `N=120`, not a hidden selector
`N(m)`, and not a reconstructed `kappa`.  Statement (5.1) removes the
quantifier ambiguity, but remains an open theorem.

## 6. G6 — RH-import audit

The accepted inputs in Sections 1--5 are the SOFT_0 implication, the two
analytic source locks, D0.2/D0.6/D0.7e, and the full H8 explicit-formula
source.  The following were not imported:

- BFM or any `sum_rho |A(rho)|^2` moment;
- `1-rho=conjugate(rho)`;
- a parametrization of every zero as `1/2+i gamma`;
- a critical-line-only or cached finite zero list treated as exhaustive;
- Weil positivity;
- assumed convergence `H_(m,N)->Xi` or a post-hoc divisor definition;
- the off-axis probe as theorem evidence.

The full symmetric zero side in (4.4) is cited only to type the source
identity; it is not replaced by a critical-line sum.  Therefore
`RH_IMPORT_AUDIT_PASS`.  The audit does not repair G4.

## 7. G7 — registered backup

`MovingGridToIntervalBridge` remains `REGISTERED_NOT_EXECUTED`.  Its exact
contract is: grids `X_(m,N) subset I` have fill distance tending to zero in
the same product filter as (5.1); the maximum grid error tends to zero; and an
independent local bound on a larger compact supplies a Cauchy derivative
bound.  Then

```text
sup_I |H_(m,N)-c*Xi*gamma_0|
 <= max_(x in X_(m,N)) |H_(m,N)(x)-c*Xi(x)gamma_0(x)|
    + (C_deriv+||(Xi*gamma_0)'||_I) fill_distance(X_(m,N),I)
 -> 0.
```

The current ledger has no mesh/fill-distance theorem, so the backup is not a
closure claim.

## 8. Gate verdict

G1 is a typed implication, G2 is now unambiguous, G3 has an unconditional
source pin and an explicitly conditional roof input, G5 has a complete joint
quantifier, G6 passes the import firewall, and G7 is registered honestly.
G4 does not supply the demanded linear prime/Gamma pairing theorem.  The exact
available formula is (4.2); the missing theorem is (4.6).

`D0.7e.5a` remains `BLOCKED / ACTIVE`, with scheduler marker
`NON_CRITICAL_PENDING_SOFT_1`; its mint remains inactive.  Bus 010 is absent.
Route B remains `CHALLENGER / NOT_RH`.

```text
SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC
```
