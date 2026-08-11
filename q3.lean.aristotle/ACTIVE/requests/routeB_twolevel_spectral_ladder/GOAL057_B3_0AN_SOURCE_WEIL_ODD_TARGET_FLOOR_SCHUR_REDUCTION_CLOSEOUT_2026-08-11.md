# GOAL 057 · B3.0AN closeout — exact target-floor Schur reduction

Date: 2026-08-11
Route: `CHALLENGER_NOT_RH`
Result: `GOAL057_B3_0AN_SOURCE_WEIL_ODD_TARGET_FLOOR_SCHUR_REDUCTION_PROVED`

## What closed

The production file
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTargetFloorSchurReduction.lean`
removes the large auxiliary graph shift from the actual odd-tail block and
works at the pre-registered target floor
`sourceWeilOddTargetFloor = 1 / 10^58`.

For a general `0 ≤ c₀ < μ` it proves the exact graph-norm lower bound

```text
((μ - c₀) / (sourceWeilLowerBoundConstant i + μ + 1)) * ‖x‖²
  ≤ Re ⟪C_c₀ x, x⟫.
```

The proof combines two independent exact estimates: B3.0AK ambient
coercivity `Q ≥ μ a`, and the shifted weighted-energy inequality
`Q ≥ b - L a`.  Their convex combination controls the full graph norm
`a + b` without retaining the auxiliary shift.

At `μ = 1/2` and `c₀ = 10^-58` the file then constructs and proves:

1. the actual positive, continuously invertible infinite odd-tail operator;
2. the literal target-floor head-to-tail residual;
3. the actual inverse-weighted correction `R† C_c₀⁻¹ R`;
4. the exact finite target-floor head operator and Schur complement;
5. the exact head = Schur + correction operator identity;
6. completion of the square for every literal head coefficient and every
   vector in the actual closed infinite odd tail.

No scalar inverse, sampled cutoff, finite `N=480/960`, profile optimization,
or numerical floor is used.

## Why this child was selected

B3.0AM left open whether subtracting the target floor would destroy tail
invertibility.  The existing ambient coercivity and independent weighted
lower bound contain complementary halves of the graph norm.  Combining them
first proves the exact target-floor tail is invertible; only then is the Schur
reduction lawful.  This removes the suspected infinite-tail obstruction and
isolates the remaining sign as a finite exact certificate problem.

## Validation

```text
Lean SHA-256:
  71703cfc566d9f3e6556e8888285b723b26c698036f820b6329c38c59167756c
Shape:
  23084 bytes, 516 newline-terminated lines, final LF
Public surface:
  12 definitions + 16 theorems
Private surface:
  2 theorems
Proof DB:
  30 / 30 declarations proven; 202 / 202 Route B files registered
Direct Lean:
  PASS
External production-import consumer:
  PASS for target-tail invertibility, exact c0 pairing and block completion
Negative scope judge:
  finite Schur positivity export absent
Target build:
  PASS, 7817 jobs
Full build:
  PASS, 7817 jobs
Direct Q3/Main.lean:
  PASS
scripts/q3_check.sh:
  PASS
Orchestrator tests:
  102 / 102 PASS
SQLite integrity:
  knowledge.db, aristotle_proofs.db, observability.db all OK
Public axiom profile:
  propext, Classical.choice, Quot.sound
Forbidden tokens:
  no sorry, admit, axiom, unsafe, or native_decide
```

## Exact boundary

This child does **not** prove
`sourceWeilOddTargetFloorSchurComplement i` positive.  It proves that this
finite exact operator is the only sign left in the target-floor block after
the positive infinite tail has been completed away.  Its dimension is the
symbolic source cutoff, not a substituted diagnostic `N`.

Therefore the exact finite Schur positivity certificate, the literal odd
form-core/density bridge, the whole odd-space `10^-58` floor, selected
`kTrial` operator-domain membership, projection-leakage decay and the
continuum numerator remain open.  The first coarse checkpoint and the
ten-checkpoint ledger remain open at `0 / 10`.

## Decision record

- Chosen: the exact `c₀`-shifted graph operator, convex combination of ambient
  and weighted lower bounds, actual infinite tail inverse, and exact finite
  Schur completion.
- **What was rejected and why:** directly subtracting the large shift without
  graph coercivity could lose invertibility; a scalar inverse destroys the
  block operator; `N=480/960` changes the object; and declaring the finite
  Schur sign from completion alone would assume precisely the missing fact.
- Feared failure: a second hidden shift, a sign error in the corrector, or
  silently replacing the symbolic cutoff by a sampled matrix size.
- Source of decision: local Codex proof and direct Lean verification; no new
  Proshka call and no Aristotle submission.
- Next minimal step: obtain a source-locked exact positivity certificate for
  `sourceWeilOddTargetFloorSchurComplement`, then prove the literal odd
  head-plus-tail form-core bridge before claiming a whole-space floor.

## ACTIONS LOG

- reused B3.0AK ambient coercivity and the independent shifted weighted lower;
- proved one source-locked production Lean module and exact completion;
- validated direct Lean, target/full builds, direct main, q3_check, external
  consumer, negative scope guard, proof registry, 102 tests, SQLite and
  forbidden-token/axiom audits;
- preserved the unrelated PDF and dependency-local package state;
- made no Proshka call, Aristotle submission, N=480/N=960 run, route
  promotion, Bus 010 action, Goal 055 release, PX claim, or RH claim.

## Standing boundaries

`CHALLENGER_NOT_RH` · `BUS_010 VOID` · `GOAL_055 HOLD` · `H4a1b OPEN` ·
`N480 HOLD` · `PX_RH_CLAIM NOT_MADE`.
