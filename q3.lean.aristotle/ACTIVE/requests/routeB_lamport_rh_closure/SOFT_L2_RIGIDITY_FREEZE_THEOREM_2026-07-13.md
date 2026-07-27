# SOFT_L2_RigidityFreeze — theorem freeze

Status: `MAIN_RIGIDITY_LEAN_CHECKED / GLOBAL_ROOT_RECONSTRUCTION_TYPED_AND_PAPER_PROVED / O2_INTERTWINER_LOCKED / EVEN_FROM_SIMPLE_GROUND / ALL_PLANTS_LIVE / NOT_RH`

Authority:

- `SOFT_L2_EVEN_REAL_SOURCE_DETERMINATION_CLAIM_V2.md`;
- `SOFT_L2_PRO_VERDICT_ROUND12_2026-07-13.md`;
- `D0_4_EXACT_PARITY_SECTORS.md`;
- `D0_5_GROUND_AND_TRIAL_TYPES.md`;
- `D0_6_EXACT_TRANSFORM_CONVENTION.md`.

## 1. SOFT_L2_EvenRealFullAutocorrelationRigidity

### Types

Let `Q` be an additive source space and let `E` be a commutative transform
ring with no zero divisors.  The intended analytic instance of `E` is the
ring of entire transforms.  The unrestricted pointwise function ring is not
an admissible substitute because it has zero divisors.

Fix

```text
T       : Q ->+ E                         transform;
A       : Q -> E                          full autocorrelation transform;
Real    : Q -> Prop;
Even    : Q -> Prop;
Compact : Q -> Prop;
T_inj   : Injective(T);
square  : Real(q) -> Even(q) -> Compact(q) -> A(q)=T(q)^2.
```

Then

```text
SOFT_L2_EvenRealFullAutocorrelationRigidity

Real(p), Even(p), Compact(p),
Real(q), Even(q), Compact(q),
A(p)=A(q)
  ==> p=q or p=-q.
```

If a real additive anchor `ell:Q->R` satisfies `ell(p)>0` and `ell(q)>0`, then
the conclusion is `p=q`.

### Proof

The square law gives `T(p)^2=T(q)^2`, hence

```text
(T(p)-T(q)) (T(p)+T(q))=0.
```

The transform ring has no zero divisors, so `T(p)=T(q)` or
`T(p)=-T(q)`.  Injectivity and additivity of `T` give `p=q` or `p=-q`.
The positive anchor excludes the second alternative.  No zero-location
hypothesis and no square-root construction are used.  QED.

Lean authority:
`Q3/Proofs/RouteB/EvenRealAutocorrelationRigidity.lean`.
Theorems:

```text
eq_or_eq_neg_of_mul_self_eq_mul_self;
evenRealFullAutocorrelationRigidity;
evenRealFullAutocorrelationRigidity_of_positive_anchor.
```

Kernel result: `lake env lean` PASS; zero `sorry`, `admit`, or `exact?`.

Success:

```text
SOFT_L2_SOURCE_INJECTIVITY_LOCKED
```

## 2. SOFT_L2_AutocorrelationSquareRootReconstruction

### Strict input contract

Fix `R>=0`.  The input is not an arbitrary entire function; it is an
`EvenAutocorrelationTransform(R)`, so the semantic type already contains

```text
H(-z)=H(z).
```

This is the parity invariant inherited from `H=c_F^(-1) Fourier(A)` for a
full even autocorrelation.  It is not an optional estimate.  Without this
type invariant, the Round-12 scalar list would be insufficient: a translated
`sinc` square is nonnegative and integrable on `R`, has only even zeros and
order zero `0 in 4N`, but its inverse transform is not real-even.

The explicit Round-12 fields are:

```text
H:C->C is entire and not identically zero;
H(x)>=0 for x in R;
H|R is in L1(R);
type(H)<=2R;
every complex zero has a finite even multiplicity, certified by a local
  factorization H(w)=(w-z)^ord_H(z) g_z(w), g_z(z)!=0;
ord_H(0)=4k for some k in N.
```

The Lean-checked type is
`AutocorrelationSquareRootReconstructionInput` in
`Q3/Proofs/RouteB/AutocorrelationSquareRootReconstruction.lean`.  In
particular, the even-zero field is a local-factorization certificate, not a
boolean label.

### Output

There is a nonzero real-valued even `q in L2(R)` supported in `[-R,R]` whose
entire transform `F=T(q)` has type at most `R` and satisfies

```text
F(z)^2=H(z).
```

The complete candidate set is exactly `{q,-q}`.  This output type is the
Lean-checked proposition `AutocorrelationSquareRootReconstruction`.

### Paper proof

1. The certified even divisor of the nonzero entire `H` has a global entire
   half-divisor on the simply connected plane.  Therefore an entire `F` with
   `F^2=H` exists, and any other entire square root is `F` or `-F` by the
   no-zero-divisor argument.
2. Maximum-modulus growth halves under squaring, hence
   `type(F)<=R` from `type(H)<=2R`.
3. On the real axis, `F(x)^2=H(x)>=0`.  Choose the global sign so that `F` is
   real at one nonzero real point; analytic continuation across the discrete
   real zero set makes `F` real on all of `R`.
4. Since `H` is even, `F(-z)^2=F(z)^2`; hence `F(-z)=F(z)` globally or
   `F(-z)=-F(z)` globally.  The odd alternative makes `ord_0(F)` odd and thus
   `ord_0(H)=2 ord_0(F)=2 mod 4`.  The certificate `ord_0(H) in 4N` excludes
   it, so `F` is even.
5. `integral_R |F(x)|^2 dx = integral_R H(x) dx < infinity`; therefore
   `F|R in L2`.  Paley--Wiener at type `R` yields a source supported in
   `[-R,R]`.  Reality and evenness of `F` give a real-even source.
6. The first step gives uniqueness up to the two global signs.  QED.

Success:

```text
SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED
```

Scope statement: the theorem contract and analytic proof are frozen, and its
input/output structures typecheck in Lean.  The global analytic existence
proof itself has not been kernel-formalized; no fake Lean theorem is claimed.

## 3. O2 exact intertwiner

D0.6's printed map has direction

```text
kappa_D06 : L2([0,L],dx) -> H_m,
(kappa_D06 g)(u)=g(log(lambda*u)).
```

D0.4 gives `Gamma_m f(u)=f(u^-1)` and `x -> L-x`.  Thus the literal
uncentered source line is

```text
Gamma_m kappa_D06 = kappa_D06 R_L,
(R_L g)(x)=g(L-x).
```

Define

```text
C_L      : L2([0,L]) -> L2([-L/2,L/2]),
(C_L g)(y)=g(y+L/2);
kappaHat_m := C_L (kappa_D06)^(-1) : H_m -> L2([-L/2,L/2]);
(Jq)(y)=q(-y).
```

The first requested centered line is now type-correct and exact:

```text
kappaHat_m Gamma_m = J kappaHat_m.                         (O2.1)
```

For the centered D0.6 Fourier/ZEO convention

```text
(Tq)(z)=integral q(y) exp(-i z y) dy,
F^sharp_Z(z)=conj(F(conj(z))),
```

real-valued `q` gives

```text
T(Jq)(z)=Tq(-z)=conj(Tq(conj(z)))=(Tq)^sharp_Z(z).          (O2.2)
```

In a pre-rotation Mellin variable the sharp formula carries the corresponding
minus sign.  It may be transported to `(O2.2)` only through the explicit
rotation `G(z)=F(i z)`; the two sharp conventions are not aliases.

Conclusion:

```text
SOFT_L2_O2_INTERTWINER_LOCKED
```

## 4. Canonical-ground provenance verdict

The decisive D0.5 source line is:

```text
GroundUnit_m_N is generally a set, not a selected vector;
GroundSpace_m_N subset Eplus_m_N and a canonical phase remain open.
```

D0.4 proves only that the parity sectors reduce `Mfin_m_N` and explicitly
states `NO_SIMPLE_EVEN_GROUND`.  Therefore the canonical `q_(m,N)` is not
selected inside a real-even carrier before H2a.

Verdict:

```text
EVEN_FROM_SIMPLE_GROUND
```

This code records the dependency honestly; it does not assert that simplicity
alone proves evenness.  The existing Lean plant
`commute_simple_ground_does_not_force_even` exhibits a commuting involution
with a simple odd ground.  A sector-winner/even-selection theorem remains
necessary before project instantiation of either rigidity theorem.

## 5. Executed plants

Machine record: `SOFT_L2_RIGIDITY_FREEZE_PLANTS.json`.

```text
PL1_EVEN_REAL_RECONSTRUCTION_PASS
  relative error = 5.353301558149146e-16;

PL2_NON_EVEN_TWINS_AMBIGUITY_DETECTED
  [1,5,6] and [3,7,2] have the same full A=[6,35,62,35,6];

PL3_COMPLEX_EVEN_SHARP_SQUARE_MISMATCH_DETECTED
  |F F^sharp-F^2| at x=0.37 = 21.42703254155939;

PL4_POSITIVE_ANCHOR_SELECTS_GLOBAL_SIGN
  anchors = +/-2.152127051220663;

P5_PROSHKA_RECONSTRUCTOR_REFUSED
  H=(z^2+1)(sin(z)/z)^4;
  missing certificate -> EVEN_ZERO_CERTIFICATE_MISSING_OR_FALSE;
  forged certificate -> ODD_ZERO_MULTIPLICITY_DETECTED at +/-i, order 1.
```

Final:

```text
SOFT_L2_SOURCE_INJECTIVITY_LOCKED
SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED
SOFT_L2_O2_INTERTWINER_LOCKED
EVEN_FROM_SIMPLE_GROUND
ALL_PLANTS_LIVE
NOT_RH
BUS_010_CREATED=false
```
