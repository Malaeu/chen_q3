# Codex task — Goal 058 finite reflection-even CCM/head-tail crosswalk

Date: 2026-09-01
Status: `KERNEL_GREEN_SOURCE_PACKAGE`
Parent: Goal 058 / selected even-sector exact-shift coercivity or Feshbach route

## Exact outcome

Close the carrier/interface gap between the exact finite CCM consumer and the
already admitted source-Weil even head/tail assembly:

- define the positive finite CCM index carrying physical mode `r+1`;
- define normalized symmetric coefficient pairs in the literal order
  `-N, ..., 0, ..., N`;
- prove that the explicit coefficient embedding is reflection-even;
- prove that every reflection-even finite CCM vector is reconstructed from its
  center coefficient and normalized positive-pair coefficients;
- prove that its literal `ccmFiniteSynthesis` is exactly the ambient image of
  the existing source-Weil zero-plus-low-even head;
- adapt the consumer's matrix condition `J *ᵥ x = x` to that crosswalk;
- conclude exact ambient orthogonality to the closed nonzero-even tail after
  cutoff `N`.

The implementation path is:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceEvenFiniteHeadCrosswalk.lean
```

## Exact downstream consumer

The downstream finite consumer is

```text
Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
```

and its even-sector input is an eventual uniform positive floor for every
reflection-even finite CCM vector orthogonal to the even part of the selected
row at the literal `selectedFerrersFiniteCCMRayleigh` shift.

This task supplies only the exact finite-CCM-to-source-head carrier crosswalk
and tail orthogonality needed before that estimate.  It does not supply a
positive lower bound.

## Supplier preflight

After refreshing the complete Route B Lean environment to 374/374 modules and
3402 declarations:

- the new final theorem against its exact interface contract returned
  `EXACT_FIT` in a fresh Lean harness;
- the same theorem against the full selected complement-floor consumer returned
  `REJECTED`, correctly localizing the remaining quantitative gap.

The exact next gap is:

```text
SELECTED_FERRERS_EVEN_TAIL_COERCIVITY_AND_SCHUR_MARGIN_AT_EXACT_RAYLEIGH_SHIFT
```

## Exact scope

```text
CLOSES:
  D0PSTAR_FINITE_CCM_REFLECTION_EVEN_TO_SOURCE_WEIL_HEAD_TAIL_CROSSWALK

OPENS:
  SELECTED_FERRERS_EVEN_TAIL_COERCIVITY_AND_SCHUR_MARGIN_AT_EXACT_RAYLEIGH_SHIFT
```

## Non-goals

This task does not assert:

- graph-inner-product orthogonality;
- an even-tail lower bound or inverse;
- a positive Schur/Feshbach margin;
- a selected Rayleigh-shift sector floor;
- the odd-sector floor, odd-mass rate, or weighted-residual rate;
- a complement floor, G1, G3, Route promotion, or RH.

## Proof obligations

The source package passed:

```text
lake env lean Q3/Proofs/RouteB/D0PstarSourceEvenFiniteHeadCrosswalk.lean
lake build Q3.Proofs.RouteB.D0PstarSourceEvenFiniteHeadCrosswalk
bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceEvenFiniteHeadCrosswalk.lean
python3 docs/cartographer/lean_env/envdump.py --timeout 3600
python3 scripts/supplier_preflight.py --candidate <new-final-theorem> --target <exact-interface>
python3 scripts/supplier_preflight.py --candidate <new-final-theorem> --target <selected-consumer>
```

The complete environment index covers 374/374 source modules and 3402
declarations.  The public declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; the source contains no `sorry`, `admit`,
`exact?`, `native_decide`, or new axiom.

## Semantic quarantine

Kernel acceptance is not semantic admission.  Register exactly one
`KERNEL_GREEN` entry bound to the task blob, source commit/blob, theorem IDs,
consumer, scope, normalization, domain, and quantifiers.  Do not consume the
new declarations in a later selected-shift theorem until an independent
`q3_semantic_attestation.v1` receipt admits this exact entry.

Route status remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
