# Goal 058 full-source trial-line / Schur preflight

Date: 2026-08-13

Target: `GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT`

Outcome: **STOPPED honestly at two exact source boundaries**

```text
GOAL058_SOURCE_COMPLEX_REAL_GROUND_CROSSWALK_MISMATCH
LAG_SOURCE_TAUTOLOGICAL_ZERO
```

The success code `GOAL058_FULL_SOURCE_TRIAL_LINE_SCHUR_PREFLIGHT_PROVED` is
not emitted. G1 and G3 remain open. No cofinal floor, schedule, Route-B
promotion, or RH statement is proved here.

## Pin and relock

- canonical checkout: `/Users/emalam/GitHub/rh_lean_01_2026`
- branch: `rh_clean`
- execution HEAD = `origin/rh_clean`:
  `6d7437e257c5101b06df9f5aff53dc8ff4984cc8`
- judge pin:
  `08a2db998f2b5467d70effdfd135d3846189999c`
- `git diff --name-only 08a2db99..HEAD -- <seven declared Lean inputs>`:
  empty

The execution commit differs from the captured judge pin only outside the
declared Lean input set. The seven inputs are therefore source-relocked at the
current equal bytes:

| input | SHA-256 |
|---|---|
| `CCMFiniteWeilSourceMatrix.lean` | `282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89` |
| `CCMFiniteWeilSourceCommutator.lean` | `d0bb820651c81ac6971985cb705bd3191584108f5d90ea19411e9a0884c11190` |
| `D0PstarCCMFiniteSourceResidual.lean` | `c11fe72d9df1e7a81d73cdcb1beebfc016be82cb1d0bcc8ffc371fc748cfb497` |
| `D0ProlateKTrialSource.lean` | `7597910a8cf2160c4ab9786144d25595a6c519395f64fc0846d84a249a96c016` |
| `Proposition59EntireTransform.lean` | `a5a6c7bb08f7d8e75ac583dfcf25a7060eaff1060e755142d1456ea94d73ab9b` |
| `Proposition59GroundLagrangeZeroSetBridge.lean` | `bb9383bebfcd5d01423ff5e944a28545e835e2e03c8609ec69fde73dce5ab2c5` |
| `CCMFiniteWeilParity.lean` | `a79c30cdc11cc936838e7963eff1a3de1f2c9290cf5ce5ca516b9bbf093b5f90` |
| `/tmp/Goal058CommutatorGapCollapse.lean` | `6da72ad35c6659f39cfa8a41171e89b3bc374ed991db2ec34660dfe5a237cb8d` |

Strict startup was `P9_STRICT_PASS`; Route-B status was `CHECK: OK` before
execution.

## Knowledge preflight receipt

All three exact queries exited zero and returned `no hits`:

```text
Goal 058 exact phase realification sourceCCMComplexRow reflection even source trial
Goal 058 Proposition59 complex source trial phase transform connector
Goal 058 full trial line four block Feshbach Schur commutator tautological non-eigenvector
```

The report and Lean file therefore preserve their own source-addressed
receipt rather than claiming an existing catalog supplier.

## Task 1 — exact source row: typed stop

The literal row has type

```lean
D0Pstar.sourceCCMComplexRow S i : CCMModeFinite i.N -> Complex
```

and has exact unit norm through
`D0Pstar.sourceCCMComplexRow_unit`. The source package does **not** contain a
theorem producing a unit `phase : Complex` and a real row `q` with

```lean
phase * sourceCCMComplexRow S i j = (q j : Complex)
```

for every coordinate, much less exact reflection-evenness of that same `q`.
`ProlatePair.h0` and `ProlatePair.h4` are complex-valued; their stored facts
assert ordinary evenness, support, integrability, normalization, and real
integrals, but do not assert pointwise reality or a common global phase.
`E_star` also remains complex-valued. None of the seven declared inputs adds
the missing phase theorem.

The Lean preflight records the required proposition exactly as
`sourceCCMHasRealEvenPhase`, without assuming it. It proves two necessary
consequences:

1. a unit phase transports the existing complex unit norm to `q dot q = 1`;
2. if the resulting real row were reflection-even, the original complex
   source row would be exactly reflection-even as well.

It also proves `phaseOne_realPart_requires_exact_reality`: choosing phase one
and taking `Re(row)` works only if the original row was already exactly real.
Thus the P5 mutation is not admitted as a construction.

The independent M1C finite-cell certificate reported a strictly positive
saved-row odd mass near `2.9556506e-60` and explicitly recorded that no exact
source trial-evenness theorem was found. That finite numerical fact is not
used as a Lean impossibility proof; it is retained only as additional evidence
against silently replacing the source row by a symmetrized proxy.

Typed result:

```text
GOAL058_SOURCE_COMPLEX_REAL_GROUND_CROSSWALK_MISMATCH
```

## Task 2 — exact P59 connector: conditionally proved

The Lean file defines the complex-row analogue on the same exact carrier and
mode order:

```text
CCMModeFinite N  <->  Icc (-N) N
source mode n    ->   P59 pole -n
```

It proves:

```lean
proposition59CCMTransform L N q z =
  phase * proposition59CCMComplexTransform L N row z
```

under the exact coordinate equality `phase * row i = (q i : Complex)`, and
then specializes it to `sourceCCMComplexRow`. The existing P59 definitions
preserve the source-locked coordinate `-L*z/(2*pi)`; downstream uses may set
`L = log m`. No eta normalization is changed.

This closes the algebraic connector **conditional on Task 1**. It does not
create the missing phase-realification supplier.

## Task 3 — full trial-line block identity: proved

The Lean file exports exact definitions:

- `trialRayleigh`
- `trialCoupling`
- `evenComplementBlock`
- `oddSectorBlock`
- `oddTrialMass`

It defines the trial-line matrix `P = vecMulVec q q`, its complement
`Q = 1 - P`, proves `P*P=P` from `q dot q=1`, and proves the exact four-block
identity

```text
K = P*K*P + P*K*Q + Q*K*P + Q*K*Q.
```

`ccmWeilMatFinite_full_trialLine_four_block_identity` specializes the result
to the literal matrix `ccmWeilMatFinite mProject N`. No positivity, spectral
gap, complement coercivity, decay, or cofinal statement is introduced.

## Task 4 — exact commutator classification

The proposed scalar observable was made explicit as

```text
q dot ((D*K - K*D) * q).
```

Lean proves it is exactly zero for every real `q` whenever `D` and `K` are
symmetric. Therefore the literal CCM specialization with
`D = ccmModeDiagFinite N` and `K = ccmWeilMatFinite mProject N` is identically
zero, without any eigenvector premise.

The same-carrier `CCMModeFinite 1` plant supplies an exact real-even row
`q = (1,1,1)` and an exact symmetric centrosymmetric matrix for which:

- the source-shaped rank-two commutator identity holds;
- `q` is reflection-even;
- `q` is not an eigenvector;
- the scalar commutator observable is exactly zero.

Classification:

```text
LAG_SOURCE_TAUTOLOGICAL_ZERO
```

No numerical tolerance selects this outcome.

## Mandatory plants

| plant | outcome | evidence |
|---|---|---|
| P1 wrong-family proxy | PASS / rejected | production specializations name only `sourceCCMComplexRow`, `proposition59CCMTransform`, and `ccmWeilMatFinite`; the algebraic plant is explicitly a falsifier, not substituted into production |
| P2 circular gap premise | PASS / rejected | no positive gap, simplicity, ground-trial convergence, RH, global positivity, or off-line-zero premise occurs in any new theorem |
| P3 non-eigenvector tautology | PASS / killed observable | exact even non-eigenvector plant plus general symmetric-matrix theorem yields `LAG_SOURCE_TAUTOLOGICAL_ZERO` |
| P4 pinned 3x3 gap collapse | PASS | pinned SHA matches and direct `lake env lean /tmp/Goal058CommutatorGapCollapse.lean` succeeds |
| P5 phase/real-row mutation | PASS / rejected | `phaseOne_realPart_requires_exact_reality`; no `Re(sourceCCMComplexRow)` substitution |
| P6 second diagonal | PASS / rejected | no schedule or diagonal is created in this bounded preflight |

## Validation

The final validation transaction records:

```text
lake env lean Q3/Proofs/RouteB/CCMProposition59SourceTrialFeshbachPreflight.lean
  PASS

lake env lean /tmp/Goal058CommutatorGapCollapse.lean
  PASS

lake build
  PASS (7817 jobs)

./scripts/q3_check.sh
  PASS via repository-root `bash scripts/q3_check.sh <target>`
  (the script is not executable and is not located under q3.lean.aristotle)

forbidden-token scan
  PASS for proof-hole tokens; declaration-anchored axiom/opaque scan PASS
  (`#print axioms` audit commands retained intentionally)

git diff --check
  PASS

routeb_status.py --check
  CHECK: OK
```

All printed public theorem axiom sets observed so far are within
`[propext, Classical.choice, Quot.sound]`; the two classification equalities
use no axioms. No `sorryAx` appears after successful elaboration.

## Decision

The bounded algebra got smaller and cleaner, but the proposed new architecture
does not survive its decisive local tests:

1. the literal complex source trial still lacks an exact real-even P59 carrier;
2. the scalar commutator expectation is tautologically zero even on an exact
   real-even non-eigenvector.

The four-block identity is valid representation progress only. It cannot be
promoted into the missing G1 gap or G3 leakage/rate supplier.

`ARSENAL_USED: C04 · C07 · C09 · C10`

```text
GOAL058_SOURCE_COMPLEX_REAL_GROUND_CROSSWALK_MISMATCH
LAG_SOURCE_TAUTOLOGICAL_ZERO
```
