# Codex task — Goal 058 explicit source-Weil even-tail coercivity

Date: 2026-09-01
Status: `KERNEL_GREEN_SOURCE_PACKAGE`
Parent: Goal 058 / selected even-sector exact-shift coercivity or Feshbach route

## Exact outcome

Transport the already proved source-Weil high-frequency argument from the
normalized odd mode pairs to the literal normalized nonzero-even mode pairs:

- expose the parity-independent closure transport for an explicit graph
  generator;
- prove the exact Fourier representative of the normalized symmetric pair;
- prove the same inverse-frequency low-band envelope and finite Parseval
  estimate as in the odd sector;
- integrate the low-band estimate and absorb the bounded W02 and Prime forms;
- prove algebraic and closed graph-tail coercivity with margin `1/2`.

The primary implementation path is:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilEvenTailExplicitCoercivity.lean
```

The supporting reusable changes are in:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailCoercivityClosure.lean
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailExplicitCoercivity.lean
```

## Exact theorem

```text
Q3.RouteB.D0Pstar.sourceWeilEvenTailAmbientCoercive_explicit
```

For every `PairIndex i`, it proves unshifted source-Weil coercivity with
margin `1/2` on the exact closed nonzero-even graph tail beginning at
`sourceWeilEvenTailCutoff i`.

## Exact downstream boundary

The selected finite consumer eventually needs a positive reflection-even
complement floor at the literal scalar
`selectedFerrersFiniteCCMRayleigh`.  This source theorem does not close that
consumer:

- `sourceWeilEvenTailCutoff` is the same explicit coarse cutoff as the odd
  theorem, while the finite CCM crosswalk splits at `i.N`;
- no theorem proves that the selected schedule reaches the explicit cutoff;
- the theorem is unshifted and supplies no upper envelope for the selected
  Rayleigh scalar;
- it supplies no finite-head coupling or positive Schur margin.

The next smallest source-faithful target is therefore a direct perturbation
floor on the nonzero-even tail beginning at the selected `i.N`, or an exact
cutoff comparison strong enough to reuse this theorem, followed separately by
the selected-shift and finite-head Schur ledgers.

## Exact scope

```text
CLOSES:
  D0PSTAR_SOURCE_WEIL_EVEN_TAIL_EXPLICIT_UNSHIFTED_COERCIVITY

OPENS:
  SELECTED_CUTOFF_SCHEDULE_DOMINATION_OR_DIRECT_SELECTED_N_EVEN_TAIL_COERCIVITY
  SELECTED_RAYLEIGH_UPPER_ENVELOPE
  FULL_ROW_RAYLEIGH_TO_EVEN_PROBE_LEDGER
  FINITE_EVEN_HEAD_SCHUR_MARGIN
```

## Non-goals

This task does not assert:

- `sourceWeilEvenTailCutoff i ≤ i.N`;
- a floor for the whole tail beginning at `i.N`;
- a floor after subtracting `selectedFerrersFiniteCCMRayleigh`;
- equality of the full-row and normalized-even-probe Rayleigh scalars;
- a finite-head Feshbach or Schur margin;
- a selected complement floor, G1, G3, Route promotion, or RH.

## Verification

```text
direct Lean: PASS (all three touched modules)
target build: PASS (7817/7817 jobs)
q3_check: PASS (all three touched modules)
source scan: no sorry, admit, exact?, native_decide, or new axiom
public axioms: [propext, Classical.choice, Quot.sound]
git diff --check: PASS
independent Lean review: GO, 0 CRITICAL/HIGH/MEDIUM/LOW findings
```

The independent review confirmed the even sign, `1/sqrt 2` normalization,
Parseval ledger, inverse-square tail summation, graph closure topology, and the
strictly unshifted scope.  It independently rejected any inference to the
selected Rayleigh-shift consumer.

## Semantic quarantine

Kernel acceptance is not semantic admission.  Register exactly one
`KERNEL_GREEN` entry bound to the task blob, source commit/blob, theorem IDs,
consumer, scope, normalization, domain, and quantifiers.  Do not consume the
new theorem in a selected-shift proof until an independent
`q3_semantic_attestation.v1` receipt admits this exact source package.

Route status remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
