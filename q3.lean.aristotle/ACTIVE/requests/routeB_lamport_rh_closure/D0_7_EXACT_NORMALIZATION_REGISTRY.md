# D0.7 — ExactNormalization registry

Status: `PARTIAL_MATH_PROVED / BDET_DEFINITION_LOCKED / XWALK_BLOCKED / LEAN_INTERFACE_UNPINNED / NOT_RH`

Progress class: `REPRESENTATION_PROGRESS`.

Partial exit: `D0_7_PARTIAL_NORMALIZATION_LOCKED`.

Canonical active leaf: `D0.7e.5a`.

Active stop: `D0_7E_WPRIME_CONSUMER_MISSING`.

No-stop sprint progress inside the nested slot:
`D0.7e.5b = PROVED_INTERFACE_TYPECHECK_ONLY` and
`D0.7e.5d = PROVED_MIGRATION_CORRECTNESS_ONLY`; 5a and 5c remain open, so no
parent closes.

The point of this leaf is to make every scalar, phase, boundary functional,
and `b` namespace exact before any asymptotic estimate is attempted. The
owner-ratified central calibration now supplies the finite detector definition.
Its theorem crosswalk to the exact spectral/ZEO consumers is still open. The
central calibration ratio cannot be silently aliased to the inverse ZEO
normalizing multiplier, and neither can be connected to `WPrime` before an
independent consumer definition is pinned.

## 1. Parameter and scalar convention

For every D0.1 pair `(m,N)`, put

```text
lambda_m=sqrt(m),
L_m=log(m)=2*log(lambda_m).
```

All objects in this leaf retain both indices. There is no `N(lambda)` and no
one-parameter abbreviation that hides `N`.

The D0.1 Hilbert inner product is antilinear in the first slot and linear in
the second. This convention determines which order makes a vector represent a
linear boundary functional.

## 2. D0.7a — Dirichlet boundary vector and functional

Define in `E_m_N`

```text
deltaVec_m_N := L_m^(-1/2) * sum_(n=-N)^N V_n_m,
deltaFun_m_N(f) := <deltaVec_m_N,f>_H_m.
```

Because the `V_n_m` are orthonormal,

```text
||deltaVec_m_N||^2=(2N+1)/L_m.                         (2.1)
```

For `f=sum_(n=-N)^N c_n V_n_m` in `E_m_N`, linearity in the
second slot and the endpoint values of the modes give

```text
deltaFun_m_N(f)=L_m^(-1/2)*sum c_n
                =f(lambda_m^(-1))=f(lambda_m).         (2.2)
```

The two endpoint values agree because a finite packet obeys the periodic
boundary condition. For general `f in Dom(Dlog_m)`, the primary source proves
only

```text
lim_(N->infinity) <deltaVec_m_N,f> = f(lambda_m).       (2.3)
```

Point evaluation is not a bounded functional on all of `H_m`. Also, for the
starred-sum packet `gTrial_m`, a midpoint representative can affect pointwise
endpoint statements while leaving its L2 class and projection unchanged.
Thus (2.2) applies exactly to the finite polynomial `P_m_N gTrial_m`; it is not
an automatic equality with a chosen pointwise representative of `gTrial_m`.

Exit: `D0_7A_DIRICHLET_VECTOR_FUNCTIONAL_LOCKED`.

## 3. D0.7b — Trial scalar and phase

D0.5 fixes the additive source phase by

```text
I_0_lambda=integral h_0_lambda>0,
I_4_lambda=integral h_4_lambda>0,
hTrial_m=(I_4_lambda*h_0_lambda-I_0_lambda*h_4_lambda)
         /sqrt(I_0_lambda^2+I_4_lambda^2).
```

Hence `hTrial_m`, its starred-sum image `gTrial_m`, and the finite projection
`gTrial_m_N` inherit an exact phase; no free unimodular scalar is silently
chosen here.

On the dependent locus

```text
TrialNonzero={(m,N): ||gTrial_m_N||>0},
```

define the positive scalar and normalized trial

```text
sTrial_m_N := ||gTrial_m_N||^(-1)>0,
kTrial_m_N := sTrial_m_N*gTrial_m_N,
||kTrial_m_N||=1.                                      (3.1)
```

This is a definition on `TrialNonzero`, not a proof that every projection is
nonzero. It does not identify the trial with a ground vector or with the
detector `b` below.

Exit: `D0_7B_TRIAL_SCALAR_PHASE_LOCKED`.

## 4. D0.7c — Conditional ground boundary normalization

Let `xi in GroundUnit_m_N` and set

```text
c_m_N(xi):=deltaFun_m_N(xi).
```

Define the dependent locus

```text
GroundDeltaNonzero
 := {(m,N,xi): xi in GroundUnit_m_N AND c_m_N(xi)!=0}.
```

Only on this locus define

```text
xiPhase_m_N
 := (conj(c_m_N(xi))/|c_m_N(xi)|)*xi,

xiBoundary_m_N
 := c_m_N(xi)^(-1)*xi.                                 (4.1)
```

Since `deltaFun` is linear,

```text
||xiPhase_m_N||=1,
deltaFun_m_N(xiPhase_m_N)=|c_m_N(xi)|>0,
deltaFun_m_N(xiBoundary_m_N)=1,
||xiBoundary_m_N||=|c_m_N(xi)|^(-1).                   (4.2)
```

Thus phase normalization and boundary normalization are different. The latter
is not generally a unit vector.

The primary source proves `c_m_N(xi)!=0` after assuming the shifted finite
Weil operator has a simple even ground state. D0.5 intentionally supplies
neither simplicity, parity, nor a canonical vector selection. Therefore (4.1)
is a correct dependent interface, not an unconditional Route B ground
normalization theorem.

Exit: `D0_7C_CONDITIONAL_GROUND_BOUNDARY_NORMALIZATION_LOCKED`.

## 5. D0.7d — `b` namespace firewall

Three symbols must not be aliased.

```text
bWeil_j(m,N):
    exact odd scalar sequence in the matrix identity
    tau_(i,j)=(bWeil_i-bWeil_j)/(i-j) and in beta=sum bWeil_j V_j;

bPilot_m_N:
    historical diagnostic scalar ||E(g04)|| from the superseded pilot node;

bDet(lambda) or bDet_m_N:
    scalar consumed by the detector identity W'^2=|b|^2*lambda*alpha/Delta_e.
```

The primary paper's OCR token `xib` denotes the Fourier transform
`xi-hat`, not multiplication of `xi` by a scalar named `b`.

The later canonical object-lock explicitly records detector `b_lambda` as
`MISSING`. Contract v2 requires a formula, carrier/index dependence, and a
crosswalk to the `W'` consumer. Neither the exact identity
`sTrial_m_N^(-1)=||gTrial_m_N||` nor the obsolete assignment
`bPilot=||E(g04)||` proves that crosswalk.

Exit: `D0_7D_B_NAMESPACE_FIREWALL_LOCKED`.

## 6. D0.7e — Central calibration locked; exact crosswalk open

The immutable owner input defines, on D0.7b's `TrialNonzero` locus,

```text
Fplus_m_N(z)=T_m(kTrial_m_N)(-z),
Fhat_m_N(z)=gammaC(1/2+i*z)Fplus_m_N(z),
bDet_m_N=Fhat_m_N(0)/Xi(0)
          =sqrt(L_m)c0(kTrial_m_N)/zeta(1/2).
```

The reflection is required by D0.6's frozen sign. The alternating eta series
proves `zeta(1/2)<0`, so the denominator is genuinely nonzero. On the further
`BDetNonzero` locus, `G=Fhat/bDet` satisfies
`Fhat=bDet*G` and `G(0)=Xi(0)`. Reality, phase, and all D0.7d namespace
firewalls are proved. The exact proof, source lock, decomposition, certificate,
and fail-closed validator are:

- `D0_7E_CENTRAL_MELLIN_CALIBRATION.md`;
- `D0_7E_CLASSICAL_SOURCE_LOCK.json`;
- `D0_7E_DECOMPOSITION_CONTRACT.md`;
- `D0_7E_CERTIFICATE.json`;
- `validate_d0_7e.py`.

The owner file labels the remaining inequality `THEOREM SHAPE to be proved`.
Its `alpha`, true `DeltaE`, `delta_dict`, limit direction, and uniform compact
constant are not proved on one exact carrier. The primary source itself names
sufficiently accurate trial-to-ground tracking as a main missing step.
The independent D0.7e.5a audit, now canonical under owner-ratified DAG
authority, further locks

```text
CentralValueNonzero=BDetNonzero=FhatAtZeroNonzero=BCalNonzero,
bCal=bDet,
bZeoMul=bCal^(-1),
G=bZeoMul*Fhat.
```

`TrialNonzero` does not imply the central nonzero locus. No independent
`FZeo` or `WPrime` consumer was found in the pinned audited tree/history
snapshot, so the historical WPrime `b` orientation remains unpinned. Therefore
`PO_D0_7E_XWALK` remains blocked at the canonical leaf `D0.7e.5a`. The nested
decomposition is owner-ratified and definitionally locked, but its first
mathematical child still lacks the independent consumer source.

Status: `BLOCKED`.

Partial exit: `D0_7E_CENTRAL_CALIBRATION_LOCKED`.

Stop: `D0_7E_WPRIME_CONSUMER_MISSING`.

## 7. Lamport proof and zoom-out

```text
<1>1. D0.1's ON modes and scalar convention prove (2.1) and (2.2); the
      primary Dirichlet-kernel theorem proves (2.3).
<1>2. D0.5's source-phase packet and dependent nonzero locus prove (3.1).
<1>3. Elementary complex scaling proves (4.2) on GroundDeltaNonzero; the
      hypotheses are not smuggled into the domain.
<1>4. Source formulas and provenance order separate bWeil, bPilot, xihat, and
      the owner-ratified bDet.
<1>5. D0.7e.1--D0.7e.4 prove the immutable provenance, finite central
      definition, dependent normalization, and reality/firewall components.
<1>6. Canonical D0.7e.5a audit evidence proves the central nonzero locus and
      inverse-normalizer identity. The owner-ratified decomposition is locked,
      but D0.7e.5a remains blocked because no independent `FZeo`/`WPrime`
      consumer in the pinned audited snapshot fixes the historical `b`
      orientation.
<1>7. D0.7a--D0.7d are PROVED and D0.7e is BLOCKED. By the exact conjunction
      D0.7.0, D0.7 and assembly D0.7f remain BLOCKED.
```

Conclusion: `D0.7 = BLOCKED / 4_OF_5_COMPONENTS_PROVED`. No
`EXACT_NORMALIZATION_DEFINED` exit is issued. QED.

## 8. Planted falsifiers

- `DELTA_SCALE`: use `L_m^(-1)` instead of `L_m^(-1/2)`; (2.1) fails.
- `INNER_PRODUCT_ORDER`: define `f -> <f,deltaVec>` under antilinear-first;
  the result is conjugate-linear, not the required linear functional.
- `ALL_H_EVALUATION`: claim bounded endpoint evaluation on all `H_m`; L2
  equivalence classes have no canonical point values.
- `GROUND_ZERO`: take `c_m_N(xi)=0`; both divisions in (4.1) are undefined.
- `PHASE_EQUALS_BOUNDARY`: when `|c|!=1`, the two normalized vectors have
  different norms.
- `BWEIL_ALIAS`: replace detector `b` by the matrix coefficient `bWeil_j`;
  the index and type disagree.
- `BPILOT_ALIAS`: set detector `b:=||E(g04)||`; it disagrees with the locked
  central calibration and has no crosswalk.
- `H4D_SMUGGLE`: assert a uniform lower/growth bound from mere dependent
  definability; no such estimate was proved.

## 9. Explicit nonclaims

```text
NO_UNCONDITIONAL_GROUND_SELECTION
NO_SIMPLE_EVEN_GROUND
NO_UNCONDITIONAL_DELTA_NONZERO
NO_UNCONDITIONAL_TRIAL_NONZERO
NO_BOUNDED_EVALUATION_ON_ALL_H
NO_ENDPOINT_REPRESENTATIVE_ALIAS
NO_UNCONDITIONAL_BDET_NONZERO
NO_WPRIME_ZEO_CROSSWALK
NO_BPILOT_BDET_CROSSWALK
NO_B_BOUNDS
NO_H4D
NO_N_LAMBDA_SELECTOR
NO_D0_ASSEMBLY
NO_RH
```
