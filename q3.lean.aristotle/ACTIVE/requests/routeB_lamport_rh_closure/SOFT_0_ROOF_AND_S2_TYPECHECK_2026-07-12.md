# SOFT_0 — RoofAndS2Typecheck

Status: `ABSTRACT_CLOSURE_PROVED / FINITE_ROOF_BODY_MISSING / S2_IDENTIFICATION_OPEN / NOT_RH`

Gate output: `SOFT_SUBSEQUENCE_CLOSURE_TYPED`.

This is a paper gate.  It proves the abstract subsequence theorem, audits the
finite roof against the physical DAG, locks the analytic completion unit, and
reclassifies two diagnostics.  It does not prove any missing project
hypothesis, close H1/H2/H3/H4, activate a mint, create Bus 010, or prove RH.

## 1. Typed theorem

Let

```text
S      := {z : C | abs(Im(z)) < 1/2},
Splus  := {z : C | 0 < Im(z) and Im(z) < 1/2},
Sminus := {z : C | -1/2 < Im(z) and Im(z) < 0}.
```

Write `Hol(S)` for the holomorphic functions on `S`, and write
`HolUnit(S)` for the functions `gamma in Hol(S)` satisfying
`gamma(z) != 0` for all `z in S`.  The project function is
`Xi := centeredXi`; the already Lean-checked classical interface is

```text
Q3.RH <-> (for all z, Xi(z)=0 and z in S implies Im(z)=0).
```

Fix, before selecting a cluster limit, an independently source-locked
`gamma in HolUnit(S)`.  For a holomorphic `F` on `S`, define
`Identified(F;Xi,gamma)` to mean that there are `c in C`, `c != 0`, a set
`E subset S`, and a point `q in S` such that `q` is an accumulation point of
`E` in `S` and

```text
for every z in E, F(z)=c*Xi(z)*gamma(z).
```

This definition forbids choosing `gamma := F/(c*Xi)` after seeing `F`.

### Theorem `SoftSubsequenceZeroEscape`

Let `(F_j)_(j>=1)` be a sequence of functions `S -> C`.  Assume:

```text
(HOL)    for every j, F_j is in Hol(S);
(RZERO)  for every j and z in S, F_j(z)=0 implies Im(z)=0;
(ANCHOR) for every j, F_j(0)=Xi(0), and Xi(0)!=0;
(LOCAL)  for every compact K compactly contained in S,
         sup_j sup_(z in K) abs(F_j(z)) < infinity;
(ID)     every locally-uniform cluster limit F of (F_j) on S satisfies
         Identified(F;Xi,gamma).
```

Then `Q3.RH`.

Only `(HOL)`, `(RZERO)`, `(ANCHOR)`, `(LOCAL)`, `(ID)`, the fixed
zero-freeness of `gamma`, and the classical Xi/RH interface are consumed.
There is no detector rate, gap estimate, H3, H4, S1, S2, or quantitative
convergence hypothesis hidden in the proof.

### Proof

1. `S` is open and convex, hence connected.  The sets `Splus` and `Sminus`
   are also open, convex, and connected.

2. By `(HOL)` and `(LOCAL)`, Montel's theorem gives a strictly increasing
   index sequence `j_k` and an `F in Hol(S)` for which

   ```text
   F_(j_k) -> F locally uniformly on S.                       (1)
   ```

3. Local uniform convergence at the singleton `{0}` and `(ANCHOR)` give

   ```text
   F(0)=lim_k F_(j_k)(0)=Xi(0)!=0.                            (2)
   ```

   Consequently `F` is not identically zero.

4. Apply `(ID)` to the cluster limit in (1).  There are `c!=0`, `E`, and an
   accumulation point `q in S` such that `F=c*Xi*gamma` on `E`.  Both sides
   are holomorphic on connected `S`.  Their difference has zeros accumulating
   at the interior point `q`, so the identity theorem yields

   ```text
   F(z)=c*Xi(z)*gamma(z) for every z in S.                    (3)
   ```

5. Each `F_(j_k)` is nonvanishing on `Splus` by `(RZERO)`.  Hurwitz's theorem
   on the connected domain `Splus` says that `F|Splus` is either everywhere
   nonzero or identically zero there.  The second alternative would make `F`
   zero on a nonempty open subset of connected `S`; the identity theorem would
   then give `F identically 0`, contradicting (2).  Thus `F` has no zero on
   `Splus`.

6. The identical argument on the separate connected component `Sminus`
   shows that `F` has no zero there.  It is essential not to call
   `S minus R` connected: the two Hurwitz applications are separate.  Hence

   ```text
   F(z)=0 and z in S implies Im(z)=0.                         (4)
   ```

7. Since `c!=0` and the independently fixed `gamma` is nowhere zero, (3)
   gives, for every `z in S`,

   ```text
   F(z)=0 iff Xi(z)=0.                                       (5)
   ```

   Combining (4) and (5), every Xi zero in `S` is real.  The Lean-checked
   theorem `rh_iff_centeredXi_zeros_real` converts this statement exactly to
   `Q3.RH`.  QED.

### Minimal-cluster corollary

If one assumes directly that a named subsequence converges locally uniformly
to a nonzero `F=c*Xi*gamma`, then `(LOCAL)` is not used and should be removed
from the minimal statement.  The theorem above deliberately uses the stronger
Montel formulation so that independent local boundedness is contentful rather
than decorative.

## 2. Finite-roof audit

Requested signature:

```text
H2a(j) => [F_j in Hol(S) and Z(F_j) intersect S subset R].
```

The dependency-cycle test passes in the narrow sense: the source-side finite
argument uses no H3, H4, S1, S2, convergence to Xi, or RH.  No
`SOFT_ROOF_H4_DEPENDENCY_CYCLE` was found.  The physical theorem body,
however, is not closed and the pass signature
`H2A_TO_REAL_ZERO_APPROXIMANT_POINTWISE` is therefore not issued.

Line-by-line ledger:

| line | required fact | physical owner | current status | forbidden downstream dependency |
|---:|---|---|---|---|
| 1 | select one exact master family and crosswalk it to D0 | `D0.8`, `H1c3` | OPEN | none |
| 2 | exact selected `F_j` is holomorphic | `H1c1`, `H1c2`, `H1c3`, `H1` | generic/source pieces PROVED; same-family assembly OPEN | none |
| 3 | its exact ground state is simple, isolated, and even | `H2a` | OPEN at exact sector ordering | none |
| 4 | source boundary normalization is nonzero and equals one | `D0.7`/Theorem-5.10 crosswalk | OPEN on exact family | none |
| 5 | Hermitian determinant/factorization gives only real zeros | `H2b` | generic Lean transfer PROVED; exact factorization CONDITIONAL/OPEN | none |
| 6 | assemble the same-family real-zero approximant | `H2c: H2a AND H2b => H2` | OPEN | none |

The primary H8 source does contain the intended mathematical route:
Proposition 5.9 gives entirety, and Theorem 5.10 gives real zeros from the
simple-even and boundary-normalized finite ground.  The repository has not yet
proved the exact same-object and boundary-normalization instantiation.  Thus:

```text
FINITE_ROOF_CYCLE_AUDIT: PASS_NO_H3_H4_S1_S2_IMPORT
FINITE_ROOF_CLOSURE:     SOFT_ROOF_BODY_MISSING
H2A_ONLY_SIGNATURE:      TYPE_ERROR_H1_H2B_SILENTLY_IMPORTED
```

The abstract theorem in section 1 consumes an already supplied `(HOL,RZERO)`
package; it does not pretend that the current project `H2a` supplies it.

## 3. Source-locked analytic unit

For fixed Route-B scale `lambda>1`, define unambiguously

```text
lambda^(-i*z) := exp((-i*z)*Real.log(lambda)),
gamma_soft(lambda,z)
  := gammaC(1/2+i*z)*exp((-i*z)*Real.log(lambda)).
```

For `z in S`, put `s=1/2+i*z`.  Then `0<Re(s)<1`.  Therefore `s` and `s-1`
are nonzero; `Gamma(s/2)` is holomorphic and nonzero; the positive-base
pi-cpower is holomorphic and nonzero; and the exponential phase is entire and
nonzero.  Hence `gamma_soft(lambda,-)` is in `HolUnit(S)`.

This fact is source-locked in `SOFT_GAMMA_COMPLETION_SOURCE_LOCK.json` to
NIST DLMF section 5.2 (Gamma has no zeros), DLMF section 4.2(iii) (the complex
exponential is entire and zero-free), and the local D0/H8 transform pins.  It
is also kernel-checked in `Q3/Proofs/RouteB/GammaSoftZeroFree.lean` by
`gammaC_centered_ne_zero` and `gammaSoft_ne_zero`.

Operand firewall:

```text
B --multiply by lambda^(-iz)--> Fplus
Fplus --multiply by gammaC(1/2+iz)--> Fhat
B --multiply by gamma_soft(lambda,z)--> Fhat.
```

Multiplying an already centered `Fplus` by `gamma_soft` would count the phase
twice.  The lock proves an analytic unit only; it does not prove that a cluster
limit equals `c*Xi*gamma_soft`, and it never permits a post-hoc quotient.

Intermediate exit: `GAMMA_SOURCE_LOCKED_ZERO_FREE`.

## 4. Off-axis probe recoding and normalization policy

The numerical data are unchanged:

```text
d log R(0.3;m) / d L_m = 0.0029166181315253155.
```

The old label `SOFT_ROUTE_ALIVE` is retired.  The only lawful interpretation
is

```text
OFF_AXIS_PROBE_NONDECISIVE_FALSIFIER_PASS.
```

It means only that the registered raw sampled blow-up threshold did not fire.
It is not normality, compact-substrip control, S2, or RH evidence.  The probe
depends on the completion representative: multiplication by the zero-free
gauge `lambda^(-i*c*z)` changes `R(y;m)` by `lambda^(c*y)` and shifts the fitted
slope versus `L_m=log m` by `c*y/2`.  At `y=0.3`, one extra phase changes the
slope from `0.0029166181` to `0.1529166181`, while the inverse phase changes it
to `-0.1470833819`, without changing any zero.

The next theorem-facing normalization is the fixed central anchor

```text
F_j(z) := Xi(0)/Ghat_j(0) * Ghat_j(z),
```

on the proved locus `Ghat_j(0)!=0`, so `F_j(0)=Xi(0)!=0`.  It is never a
per-compact or strip-sup normalization.  The current D0 object `G=Fhat/bDet`
already has this central calibration on `BDetNonzero`.

## 5. Mint menu revision R3

The R2 falsifier battery closes the menu, not the node:

```text
MINT_MENU_FALSIFIED.
```

- Variant A: the proposed exact 5c equality is false for the registered
  natural two-level Rayleigh-alpha interpretation.  The closure ratios are
  `6.9411616936599094e-102`, `4.907478950456342e-102`, and
  `2.50509212816158e-112`, rather than one.  The successful `|bCal|^4` check
  is an algebraic orientation identity and does not rescue the mint.
- Variant B: the planted `SLOT_VACUITY` fires; after substitution there is no
  independent WPrime degree of freedom.

Consequently no owner-mint variant is activated.  `D0.7e.5a` remains
`BLOCKED / ACTIVE`, with the additional scheduling marker
`NON_CRITICAL_PENDING_SOFT_0`; its historical stop is preserved.  This paper
gate does not close `5a` and does not create Bus 010.

## 6. Exact remaining wall

The abstract logic is now typed and proved, and `gamma_soft` is independently
an analytic unit.  What remains is not another Hurwitz lemma: one must still
prove, unconditionally and on an accumulating set, that a cluster limit of the
same centrally normalized real-zero finite family equals
`c*Xi*gamma_soft` (or another independently pinned fixed unit).  This is an
OPEN S2 identification obligation, not a result hidden in the definition of
gamma.

Final route status: `CHALLENGER / NOT_RH`.  Bus 010: `NOT_CREATED`.

```text
SOFT_SUBSEQUENCE_CLOSURE_TYPED
```
