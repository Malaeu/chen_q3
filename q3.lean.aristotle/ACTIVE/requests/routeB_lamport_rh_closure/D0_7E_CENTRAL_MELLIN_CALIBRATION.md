# D0.7e — CentralMellinCalibration owner-input audit

Status: `PARTIAL_MATH_PROVED / OWNER_DEFINITION_LOCKED / XWALK_BLOCKED / LEAN_UNPINNED / NOT_RH`

Progress class: `REPRESENTATION_PROGRESS`.

Partial exit: `D0_7E_CENTRAL_CALIBRATION_LOCKED`.

Stop: `D0_7E_XWALK_OPEN`.

## 1. Immutable input and exact acceptance scope

The physical owner input is

```text
D0_7E_OWNER_INPUT.md
sha256=a0f8ef78ec023aeef34f6ae03769faaf675a94d30d93b85a5da5258cb2f0bfed.
```

It is read-only evidence and is not edited by this audit. The owner explicitly
ratifies a new detector scalar rather than claiming that it was already in the
source paper. This is sufficient authority to introduce a definition, but not
to mark its proposed `WPrime`/ZEO theorem as proved.

The legal finite carrier is D0.1's two-parameter set

```text
I_fin={(m,N): m>=2 and N>=1},
lambda_m=sqrt(m),
L_m=2 log(lambda_m).
```

D0.7b defines the normalized trial only on

```text
TrialNonzero={(m,N) in I_fin: ||P_(m,N) g_(lambda_m)||>0}.
```

All definitions below therefore have `TrialNonzero` as their dependent
carrier. The owner text's proposed one-parameter rule
`N(lambda)=ceil(kappa*lambda^2)` is not accepted: `kappa` is unspecified, the
cited `F2.4` source does not exist in the repository, and D0.1 explicitly
retains independent `(m,N)`. This is the exact code
`D0_7E_N_SCHEDULE_UNPINNED`; it does not invalidate the finite definition.

## 2. Reflected transform crosswalk

For `(m,N) in TrialNonzero`, let

```text
k1_(m,N)=||P_(m,N)g_(lambda_m)||^(-1) P_(m,N)g_(lambda_m).
```

D0.6 fixes

```text
T_m f(z)=integral (Z_m f)(u) u^(-i*z) du/u.
```

The owner kernel has the opposite exponent. Its exact canonical translation is

```text
Fplus_(m,N)(z)
  := integral k1_(m,N)(u) u^(+i*z) du/u
   = T_m(k1_(m,N))(-z).                                (2.1)
```

It is not `T_m(k1)(z)`. The reflection is material away from zero and is
consistent with D0.6's project convention
`Xi(z)=F_mu(Half(g))(-z)` when `Mellin(g)=xi`. Compact support makes `Fplus`
entire.

Define the completed prefactor by the holomorphic continuation

```text
gammaC(s)=(1/2)s(s-1)pi^(-s/2)Gamma(s/2),
gammaC(0):=lim_(s->0) gammaC(s)=-1.
```

The only Gamma poles with real part greater than `-2` occur at `s=0`; the
factor `s` removes that pole. Hence `gammaC(1/2+i*z)` is holomorphic on

```text
Omega={z: |Im(z)|<5/2},
```

and

```text
Fhat_(m,N)(z):=gammaC(1/2+i*z) Fplus_(m,N)(z)
```

is holomorphic on `Omega`.

## 3. The central denominator is nonzero

The decimal value of `zeta(1/2)` is not used as proof. DLMF 25.2.3 gives the
alternating continuation

```text
eta(s)=(1-2^(1-s))zeta(s),    Re(s)>0.
```

At `s=1/2`, pair consecutive terms:

```text
eta(1/2)
 = sum_(k>=1) ((2k-1)^(-1/2)-(2k)^(-1/2)) > 0.
```

Since `1-sqrt(2)<0`, it follows that

```text
zeta(1/2)<0,
```

in particular `zeta(1/2)!=0`. Also `Gamma(1/4)>0`, so the completed prefactor
`gammaC(1/2)` is real and nonzero. DLMF 25.4.4 then gives

```text
Xi(0)=xi(1/2)=gammaC(1/2)zeta(1/2)!=0.               (3.1)
```

Thus the owner quotient is a genuine finite-cell definition, not division by
an assumed RH value.

## 4. Exact central calibration

Define on `TrialNonzero`

```text
bDet_(m,N):=Fhat_(m,N)(0)/Xi(0).                      (4.1)
```

Write

```text
k1_(m,N)=sum_(|n|<=N)c_n V_(n,m),
c0=<V_(0,m),k1_(m,N)>
```

with the project inner product antilinear in the first variable. Since
`V_(0,m)=L_m^(-1/2)`,

```text
Fplus_(m,N)(0)
 = integral k1_(m,N)(u)du/u
 = sqrt(L_m)c0.
```

Using (3.1), the common completed prefactor cancels exactly:

```text
bDet_(m,N)
 = Fplus_(m,N)(0)/zeta(1/2)
 = sqrt(L_m)c0/zeta(1/2)
 = sqrt(2 log(lambda_m))c0/zeta(1/2).                 (4.2)
```

This proves `D0.7e.2 FiniteCentralMellinCalibration` on `TrialNonzero`.

## 5. Dependent normalization, reality, and firewall

On the further locus

```text
BDetNonzero={(m,N) in TrialNonzero: bDet_(m,N)!=0},
```

define

```text
G_(m,N)(z)=Fhat_(m,N)(z)/bDet_(m,N).
```

Then exactly

```text
Fhat_(m,N)=bDet_(m,N)G_(m,N),
G_(m,N)(0)=Xi(0).                                     (5.1)
```

This proves a dependent interface; it does not prove that the locus is
cofinal. Because `k1` is real, its coefficients obey
`c_(-n)=conj(c_n)`, hence `c0` and `bDet` are real. The inherited trial phase
fixes the sign; no sign normalization is introduced.

The namespace firewall is exact:

```text
bDet is not bWeil_j;
bDet is not OCR xihat;
bDet is not automatically bPilot=||E(g04)||;
bDet is not automatically sTrial^(-1)=||gTrial||;
no H4d nonvanishing or growth bound is claimed.
```

## 6. Why the crosswalk remains open

The owner file gives a theorem shape, not a proof:

```text
WPrime_(m,N)^2=|bDet_(m,N)|^2 lambda_m alpha_(m,N)/DeltaE_(m,N)
```

together with a proposed compact-strip tracking inequality. The audited
repository does not yet define the cited canonical `alpha_(m,N)`, true
complementary distance `DeltaE_(m,N)`, or `delta_dict_(m,N)` on one exact
carrier. The cited `D0 draft F3.2/F4.4/F5.1/F5.2/F5.4` and destination
`docs/EXACT_OBJECT_FAMILY.md` do not exist.

The limit statement is also untyped: without a selected diagonal, product
filter, or iterated-limit convention, `eps_(m,N,K)->0` has no direction. The
owner I-b2 line gives `|bDet|sqrt(lambda)>=c_low`, while Contract v2 asks for a
single declared exponent `q_b` in its two-sided bound. They agree with the
suggested `q_b=-1/2` only if that exponent is proved; the input labels it
`FIT_NOT_LAW`, so no such identification is available.

Finally, D0.6's available evaluation estimate is

```text
sup_K |T_m f| <= sqrt(L_m) lambda_m^a ||f||,
a=max_(z in K)|Im(z)|.
```

It is explicitly nonuniform in `m`. Substitution of the proposed `WPrime`
leaves an uncompensated factor of the form
`sqrt(L_m)lambda_m^a/(|bDet|sqrt(lambda_m))`; the stated lower bound on
`|bDet|sqrt(lambda_m)` does not turn this into a constant `A_K`. A new weighted
evaluation/cancellation theorem or a stronger rate is required. This is
`D0_7E_XWALK_UNIFORM_CONSTANT_GAP`.

More decisively, the primary source `H8ULBMAL/fulltext.md:1240-1255` describes
the desired determinant/Xi convergence as an outlook, and lines 1293-1297 and
1469-1477 explicitly identify sufficiently accurate trial-to-ground tracking
as a main missing step. The source proves convergence of the prolate trial
transform to Xi, not the proposed spectral-error control for the selected Weil
ground object.

Therefore the following are only registered obligations:

```text
PO_B_NONVANISH
PO_B_BOUNDS
PO_D0_7E_XWALK
```

`PO_D0_7E_XWALK` has status `BLOCKED / THEOREM_SHAPE_ONLY`, not `PROVED` and
not a dependency-discharging `CONDITIONAL`. The active exact stop is
`D0_7E_XWALK_OPEN`, with secondary codes
`D0_7E_ALPHA_DELTAE_UNDEFINED`, `D0_7E_XWALK_LIMIT_QUANTIFIER_MISSING`,
`D0_7E_XWALK_UNIFORM_CONSTANT_GAP`, and
`D0_7E_B_BOUND_CONTRACT_MISMATCH`.

There is also a DAG-order problem. The proposed proof route explicitly consumes
H3c dictionary convergence and the H4 two-level ledger. In the current master,
H3 and H4 depend on D0, while D0 depends on D0.7e. Importing those downstream
nodes to prove D0.7e would create

```text
D0.7e -> D0 -> H3/H4 -> D0.7e.
```

This is `D0_7E_XWALK_DEPENDENCY_CYCLE`. It can be repaired only by proving the
needed ingredients independently inside this leaf, or by an owner-approved DAG
revision that moves the full tracking theorem downstream. Consequently
`D0.7e.6`, `D0.7f`, `D0.7`, `D0.8`, and D0 remain unclosed.

## PRO_REVIEW_REQUEST

Route: Route B Lamport closure, challenger / NOT_RH.

Current step: `D0.7e.5 ExactWPrimeZeoCrosswalk`.

Current theorem: the compact-strip inequality in owner input lines 78--98.

File: `D0_7E_CENTRAL_MELLIN_CALIBRATION.md`.

Blocker: the statement has undefined exact consumers, no joint limit, no
uniform `A_K`, and invokes downstream H3c/H4 ingredients, creating a dependency
cycle if imported.

Options:

A. Keep the full theorem in D0.7e.5 and supply independent, non-downstream
proofs of exact `alpha`, `DeltaE`, `delta_dict`, the limit filter, and the
uniform evaluation/cancellation estimate.

B. Revise the D0 contract so D0.7e closes only the finite central definition
and a typed algebraic consumer slot; move the full tracking theorem to D0.8/H3,
where the ground/trial and limit obligations already live.

C. Reorder the exact dictionary/crosswalk nodes before D0.7e and re-prove the
assembly contracts.

Codex recommendation: B. It preserves the new definition while keeping the
substantive tracking theorem at its natural downstream address.

Question for Louise: Is D0.7e intended to require only the non-circular
algebraic `bDet` consumer identity, or the full compact-strip tracking theorem?
If the latter, provide its acyclic prerequisite DAG and the missing uniform
estimate.

## 7. Lamport proof ledger

```text
<1>1. The immutable owner input authorizes a new definition and its exact name.
<1>2. D0.1 and D0.7b type that definition on TrialNonzero with both m and N.
<1>3. D0.6 proves the exact reflection Fplus(z)=T_m(k1)(-z).
<1>4. Compact support and the removable s=0 singularity prove holomorphy on
      Omega.
<1>5. The alternating eta series proves zeta(1/2)<0; the completed prefactor is
      nonzero, so Xi(0)!=0.
<1>6. The constant Fourier mode proves Fplus(0)=sqrt(L)c0 and (4.2).
<1>7. Division on BDetNonzero proves (5.1); conjugate symmetry proves reality.
<1>8. The owner theorem shape has no proof and depends on undefined exact
      consumers; the primary source names the central ground/trial bridge as
      missing.
<1>9. Hence D0.7e.1--D0.7e.4 are proved, D0.7e.5 is blocked, and the parent
      remains blocked by the definitional conjunction D0.7e.0.
```

## 8. Planted falsifiers

- `SIGN`: replacing `T_m(k)(-z)` by `T_m(k)(z)` must fail at a nonzero lattice
  frequency.
- `TRIAL_ZERO`: defining `k1` outside `TrialNonzero` must fail.
- `ZETA_DECIMAL`: deleting the eta-series proof and keeping only a decimal must
  fail the denominator lock.
- `C0_SCALE`: replacing `sqrt(L)c0` by `L*c0` must fail the constant-mode
  integral.
- `B_ZERO`: defining `G` when `bDet=0` must fail.
- `N_SELECTOR`: erasing `N` or using unspecified `kappa` must fail.
- `XWALK_SHAPE`: treating the theorem statement as its proof must fail.
- `SOURCE_ALIAS`: treating the outlook/missing-step paragraph as a proved
  ground-trial theorem must fail.

## 9. Explicit nonclaims

```text
NO_N_LAMBDA_SELECTOR
NO_UNCONDITIONAL_TRIAL_NONZERO
NO_UNCONDITIONAL_BDET_NONZERO
NO_COFINAL_BDET_NONZERO_SET
NO_BDET_TWO_SIDED_BOUNDS
NO_ALPHA_DEFINITION
NO_TRUE_COMPLEMENTARY_GAP
NO_DICTIONARY_CONVERGENCE
NO_WPRIME_ZEO_CROSSWALK
NO_D0_7E_ASSEMBLY
NO_D0_7_ASSEMBLY
NO_D0_ASSEMBLY
NO_RH
```
