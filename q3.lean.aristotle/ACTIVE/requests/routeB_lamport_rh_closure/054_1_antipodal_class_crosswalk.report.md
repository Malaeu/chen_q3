# Goal 054.1 — CCM cell 13/2 antipodal class crosswalk

```yaml
STATUS: G2_CCM_CELL13N2_ANTIPODAL_CLASS_CROSSWALK_PROVED
PROGRESS_CLASS: REPRESENTATION_PROGRESS
LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilCell13N2ClassCrosswalk.lean
LEAN_FILE_SHA256: e8417922c3b7df7ea17d2e0b859b647a82e4a911f330e8aa0c713da04e55b02f
PRIMARY_THEOREM: Q3.RouteB.ccmWeilTauN1_neg_self_eq_neg_zero
AXIOMS:
  - propext
  - Classical.choice
  - Quot.sound
TAINT: NONE
ARISTOTLE_SUBMISSION: NONE
GOAL_055: HOLD_RATIFIED_DRAFT_OUTSIDE_BUS
H2A_CLOSED: false
G2_CLOSED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
```

## Theorem

```lean
theorem ccmWeilTauN1_neg_self_eq_neg_zero
    (mProject : ℕ) (r : ℤ) :
    ccmWeilTauN1 mProject (-r) r =
      ccmWeilTauN1 mProject (-r) 0
```

The theorem uses only the literal production definitions.  It proves the
missing exact `(-2,2)=(-2,0)` identity required to justify the seven A–G
classes.  It does not use the Arb artifact, endpoint matrices, 054.1b, or any
numeric enclosure.

## Validation

- Direct: `lake env lean Q3/Proofs/RouteB/CCMFiniteWeilCell13N2ClassCrosswalk.lean` — PASS.
- Target: `lake build Q3.Proofs.RouteB.CCMFiniteWeilCell13N2ClassCrosswalk` — PASS, 7745 jobs.
- Full: `lake build` — PASS, 7817 jobs.
- Q3 check: direct executable form was unavailable because the script lacks
  execute permission; `bash scripts/q3_check.sh ...` — PASS.
- Broad SectorCell taint scan for `sorry/admit/exact?/native_decide/opaque/Float/of_decide_eq_true/axiom` — no matches.
- `#print axioms` — `[propext, Classical.choice, Quot.sound]`.

## Plant fate

- `P-054-ANTI-1` — FIRED.  Replacing the first mode `-r` by `r` at
  `r=2` was rejected by Lean with an exact type mismatch.
- `P-054-ANTI-2` — FIRED.  Replacing the second mode `r` by `2*r` at
  `r=2` was rejected by Lean with an exact type mismatch.
- `P-054-ANTI-3` — INERT AS STATED.  Globally reversing the off-diagonal
  denominator from `n-m` to `m-n` preserves the antipodal identity; a
  Lean stdin proof of the mutant identity compiled.
- Replacement control `P-054-ANTI-3R` — FIRED.  At
  `L=1, r=2, x=1/8`, Lean proves the production and reversed-denominator
  kernels are unequal, so source orientation is still detected pointwise.

The inert third prediction is a defect in the proposed plant, not in the
production theorem.

## ACTIONS LOG

1. Audited the general theorem against the existing literal `r=1` source chain.
2. Ran four local embedding queries; all returned no hits.
3. Checked current Mathlib trigonometric/integral APIs.
4. Implemented exactly one new production Lean file.
5. Ran direct, target, full, q3-check, taint, axiom, and mutation controls.
6. Did not submit Aristotle, materialize Goal 055, touch endpoint matrices, or
   create Bus 010.
