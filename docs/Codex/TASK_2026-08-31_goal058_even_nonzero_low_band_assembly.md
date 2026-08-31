# Codex task — Goal 058 source-Weil even low-band/head assembly pre-gate

Date: 2026-08-31
Status: `KERNEL_GREEN_SOURCE_PACKAGE`
Parent: Goal 058 / fixed-shift even head-tail Feshbach route

## Exact outcome

Close the local synthesis pre-gate downstream of the admitted source-even
nonzero-tail carrier:

- prove ambient orthonormality of the normalized nonzero-even modes;
- define the finite nonzero-even low-band synthesis;
- define the zero-plus-low-band even head;
- prove the literal ambient formulae for both syntheses;
- prove exact ambient orthogonality of the low band and full head to the
  closed nonzero-even tail at cutoff `R`.

The implementation path is:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceEvenNonzeroLowBandAssembly.lean
```

## Downstream consumer

The next consumer is an exact selected-row/head-tail theorem sufficient for a
positive even-tail coercivity bound or positive Schur/Feshbach margin at the
literal selected Rayleigh shift on the production cofinal schedule.

## Shelf and supplier preflight

The repository-wide query

```text
./ask.sh "source Weil even nonzero low band synthesis orthonormal head tail orthogonal"
```

found the admitted low-frequency cancellation supplier but no exact existing
head-orthogonality theorem.  Fresh direct type comparison correctly rejected
the lower-level cancellation theorem as the exact consumer type.  The new
assembly theorem then passed a fresh exact-type harness as `EXACT_FIT`.

## Exact scope

```text
CLOSES:
  D0PSTAR_SOURCE_EVEN_NONZERO_ORTHONORMAL_SYNTHESIS_LOW_BAND_ASSEMBLY

OPENS:
  SELECTED_FERRERS_EVEN_HEAD_TAIL_EXACT_SHIFT_COERCIVITY_OR_FESHBACH
```

## Non-goals

This task does not assert:

- graph-inner-product orthonormality;
- an exhaustive even-sector direct sum;
- compatibility with the selected production row;
- a Rayleigh-shift floor or positive Schur margin;
- G1, G3, Route promotion, or RH.

## Proof obligations

The source package passed:

```text
lake env lean Q3/Proofs/RouteB/D0PstarSourceEvenNonzeroLowBandAssembly.lean
lake build Q3.Proofs.RouteB.D0PstarSourceEvenNonzeroLowBandAssembly
bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceEvenNonzeroLowBandAssembly.lean
lake build Q3.Main
python3 scripts/supplier_preflight.py --query <exact-query> --candidate <exact-target> --target <exact-target>
bash specs_docs/session_start.sh
```

The complete Route B environment index covers 373/373 current source modules
and 3390 declarations.  The public declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; the source contains no `sorry`, `admit`,
`exact?`, `native_decide`, or new axiom.

## Semantic quarantine

Kernel acceptance is not semantic admission.  Register exactly one
`KERNEL_GREEN` entry bound to the task blob, source commit/blob, theorem IDs,
consumer, scope, normalization, domain, and quantifiers.  Do not consume the
new declarations in the selected-shift node until an independent
`q3_semantic_attestation.v1` receipt admits that exact entry.

Route status remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
