# Codex task — Goal 058 Arch-Prime floor on the explicit even tail

Date: 2026-09-01
Status: `KERNEL_GREEN_SOURCE_PACKAGE`
Parent: Goal 058 / selected reflection-even Arch-Prime shifted floor

## Exact outcome

Isolate the part of the admitted explicit even-tail estimate that is actually
consumed by the selected reflection-even reduction.  On every finite
nonzero-even synthesis beginning at `sourceWeilEvenTailCutoff i`, prove that
the Arch-Prime form alone has lower margin

```text
‖sourceW02AmbientContinuousSesquilinearForm i‖ + 1/2.
```

The proof reuses the existing production Archimedean lower bound and the
global operator-norm estimate for the Prime form.  It introduces no new
definition, cutoff, hypothesis, source object, or abstraction.

Implementation path:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilEvenTailExplicitCoercivity.lean
```

## Exact theorem

```text
Q3.RouteB.D0Pstar.sourceArchPrimeSesquilinearForm_re_self_lower_evenGraphFinsuppShift
```

For every `PairIndex i` and finitely supported coefficient family `c`, it
proves

```text
(‖W02_i‖ + 1/2) ‖v‖² ≤ Re (ArchPrime_i(v,v))
```

for the exact algebraic even-tail synthesis `v` at the existing explicit
cutoff.

## Dependency effect

This is one narrow `DEPENDENCY_EDGE_REMOVED`: a separate retained-Prime
decay/rate theorem is no longer needed on the coarse algebraic even tail.
Prime is already absorbed by its global form norm in the production cutoff
ledger.

```text
CLOSES:
  D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_EXPLICIT_ALGEBRAIC_FLOOR

OPENS:
  ADAPTIVE_SELECTED_FINITE_TAIL_TO_LITERAL_TOBLOCKS22_CROSSWALK
  ADAPTIVE_SELECTED_CUTOFF_DOMINATION_R_LE_N
  FINITE_EVEN_HEAD_CORRECTED_SCHUR_MARGIN_AT_EXACT_RAYLEIGH_SHIFT
```

## Exact downstream boundary

The theorem does not close
`SELECTED_N_EVEN_RETAINED_PRIME_SHIFTED_QUADRATIC_FLOOR`.
The exact selected consumer still requires all of the following:

- the finite carrier `CCMModeFinite i.N` and its reflection-even row
  complement;
- a cutoff whose retained high modes lie inside the selected finite carrier;
- subtraction of exactly `selectedFerrersFiniteCCMRayleigh P k`;
- one eventual uniform positive margin;
- a positive corrected finite-head Schur margin including the head-tail
  coupling.

At the fixed cutoff the shifted tail margin is only

```text
‖W02_i‖ + 1/2 - selectedFerrersFiniteCCMRayleigh P k.
```

No upper envelope making this positive is proved here.

## Strong guard

An abstract block form

```text
B = (-M) I_head ⊕ alpha I_tail
```

can satisfy the new tail theorem for arbitrary `M` while failing every
positive head or full selected-sector floor.  Even on the tail, shifting by
`alpha` makes the shifted form zero.  Therefore no selected floor follows
without the carrier/cutoff crosswalk, Rayleigh gap, and Schur margin.

## Non-goals

This task does not assert:

- a closed-tail Arch-Prime theorem;
- `sourceWeilEvenTailCutoff i ≤ i.N`;
- an adaptive cutoff comparison;
- a selected Rayleigh upper bound;
- a finite-head or full-sector floor;
- a selected complement floor, Route promotion, or RH.

## Verification

```text
direct Lean: PASS
target build: PASS (7817/7817 jobs)
source scan: no sorry, admit, exact?, native_decide, or new axiom
public axioms: [propext, Classical.choice, Quot.sound]
git diff --check: PASS
independent semantic reviews: ADMIT / PRODUCTION_THEOREM
```

## Semantic quarantine

Kernel acceptance is not semantic admission.  Register one new
`KERNEL_GREEN` entry bound to the exact task blob, source commit/blob, theorem
ID, consumer, scope, normalization, domain, and quantifiers.  Do not consume
the theorem in a later selected-shift proof until an independent
`q3_semantic_attestation.v1` receipt admits this exact scope.

Route B remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
