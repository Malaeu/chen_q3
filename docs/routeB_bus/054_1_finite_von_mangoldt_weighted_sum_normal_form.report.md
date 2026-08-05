# Goal 054.1 — CCM cell 13/2 finite von-Mangoldt weighted normal form

```yaml
STATUS: G2_CCM_054_1_FINITE_VON_MANGOLDT_WEIGHTED_SUM_NORMAL_FORM_PROVED
PROGRESS_CLASS: REPRESENTATION_PROGRESS
LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2VonMangoldtNormalForm.lean
LEAN_FILE_SHA256: 0742f31a45714def1965773e833efd9fef30ab6daa5dce0f8613e22706fc8fc3
PRIMARY_THEOREM: Q3.RouteB.ccmVonMangoldt_sum_Icc_2_13
PUBLIC_THEOREMS: 1
PUBLIC_DEFINITIONS: 0
PRIVATE_VALUE_HELPERS: 12
PRIVATE_LITERAL_PRIME_SPECIALIZATION_CHECK: PASS
PRIVATE_PLANTS: 3
PLANT_FATE: ALL_FIRED
DIRECT_LEAN: PASS
TARGET_BUILD: PASS_7747_JOBS
FULL_BUILD: PASS_7817_JOBS
Q3_CHECK: PASS
TAINT: NONE
AXIOMS:
  - propext
  - Classical.choice
  - Quot.sound
ARISTOTLE_SUBMISSION: NONE
GOAL_055: HOLD_055_RATIFIED
H2A_CLOSED: false
G2_CLOSED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
```

## Result

The single public theorem proves the exact weighted von-Mangoldt identity on
`Finset.Icc 2 13`.  The right-hand side retains every supported evaluation
point and factors only equal coefficients:

- `2, 4, 8` have coefficient `Real.log 2`;
- `3, 9` have coefficient `Real.log 3`;
- `5, 7, 11, 13` have their corresponding prime logarithms;
- `6, 10, 12` contribute zero.

Twelve point-value lemmas remain private.  A separate private theorem
specializes the public functional to the literal `ccmPrimeEntryN1 13 n m`.
That check unfolds only the outer prime-sum definition and never unfolds or
numerically estimates `ccmQKernel`.

## Validation

- Direct `lake env lean` — PASS.
- Target build — PASS, 7747 jobs.
- Full build — PASS, 7817 jobs.
- `bash scripts/q3_check.sh ...` — PASS.
- Taint scan — no `sorry`, `admit`, `exact?`, `native_decide`, declared
  axiom, opaque certificate, Float, or surrogate decision proof.
- Public surface scan — one theorem, zero public definitions.
- `#print axioms Q3.RouteB.ccmVonMangoldt_sum_Icc_2_13` — exactly
  `[propext, Classical.choice, Quot.sound]`.

## Plant fate

- `P-VM-1` — FIRED: deleting `f 8` from the `log 2` class produces a
  substantive type mismatch.
- `P-VM-2` — FIRED: adding a false nonzero `f 6` coefficient produces a
  substantive type mismatch.
- `P-VM-3` — FIRED: replacing the equal `log 3` coefficients by an
  exponent-weighted `2 * f 9` coefficient produces a substantive type
  mismatch.

The finite support/value enumeration wall is now closed as a reusable Lean
functional.  Kernel numerics, W02, WR, the archimedean integral, the final
cancellation ledger, and `ccmCell13N2_wr_enclosures` remain open.  This result
does not release Goal 055 or close H2a/G2.

## ACTIONS LOG

1. Ran four local `q3_docs` embedding queries; all returned no hit.
2. Audited the current official Mathlib von-Mangoldt and prime-power APIs.
3. Obtained and archived Proshka's fail-closed selection of the generic
   weighted-sum theorem.
4. Proved all twelve exact values privately and the single public functional.
5. Compiled a private literal `ccmPrimeEntryN1 13` specialization check.
6. Ran the three required semantic mutants; all failed for the intended
   mathematical mismatch.
7. Ran direct, target, full, q3-check, taint, surface, SHA, and axiom gates.
8. Did not modify existing Lean files, submit Aristotle, materialize Goal 055,
   create Bus 010, promote Route B, or claim RH.
