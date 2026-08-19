# STATUS: FATAL — THE CURRENT MINIMUM-EIGENPAIR THEOREM CANNOT SUPPLY COFINAL RAYLEIGH PROXIMITY; NO LEAN SOURCE WRITTEN

```yaml
PRIMARY: KILL_SOURCE_RAYLEIGH_PROXIMITY_FROM_MINIMUM_EIGENPAIR
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: cf579226c102d7aa2be50b9f3d294245ebfc9d1d
  DATE: 2026-08-19

TARGET:
  NAME: SOURCE_RAYLEIGH_PROXIMITY_TO_FIXED_SHIFT
  REQUIRED_FORM: |
    one precommitted aStar : Real,
    one precommitted betaStar > 0,
    and for every production k,
      abs(sourceCCMFiniteRayleigh S (selectedPairIndex S k) - aStar)
        <= betaStar / 2

CLOSES: []
OPENS:
  - DIRECT_COFINAL_SOURCE_RAYLEIGH_FIXED_SHIFT_BOUND

NODE_ADMISSION:
  OPENS_NONEMPTY_AND_CLOSES_EMPTY: true
  LEAN_SOURCE_WRITE: FORBIDDEN
  SOURCE_RECORD_WRITE: NOT_APPLICABLE
  KILL_RECORD_WRITTEN: true

KILL_SCOPE:
  DERIVATION_FROM_HERMITIAN_MINIMUM_EIGENPAIR: FATAL
  CURRENT_REPOSITORY_SUPPLIER: ABSENT
  ACTUAL_CCM_PROXIMITY_STATEMENT: NOT_REFUTED
  WHOLE_ROUTE_B: NOT_REFUTED

SOURCE_FACTS:
  sourceCCMFiniteRayleigh_defined_exactly: true
  sourceCCMFiniteMatrix_hermitian: true
  sourceCCMComplexRow_unit: true
  hermitian_exists_unit_minimum_eigenpair_proved: true
  one_fixed_aStar_supplied: false
  one_fixed_betaStar_supplied: false
  cofinal_rayleigh_bound_supplied: false
  rayleigh_tendsto_theorem_supplied: false

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

NEXT_ORDERED_FRONT:
  CANONICAL_FIXED_SHIFT_TAIL_POSDEF_FAMILY: BLOCKED_BY_ORDER
  CANONICAL_FIXED_SHIFT_CORRECTED_HEAD_PSD_FAMILY: BLOCKED_BY_ORDER

PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
```

## ROUTE MAP

The constructor consumes one fixed pair `(aStar, betaStar)` twice:

1. the fixed-shift floor is proved at `aStar` with floor `betaStar`;
2. the literal Rayleigh values remain within `betaStar / 2` of that same
   `aStar` on every production cell.

The theorem

```lean
hermitian_exists_unit_minimum_eigenpair
```

proves a different statement.  For each single finite Hermitian matrix it
produces some minimum eigenvalue `epsilon` and some unit minimum eigenvector.
It does not produce one scalar shared by a family.  It also does not relate the
cellwise minimum eigenvalue to the source trial Rayleigh value by a two-sided
estimate, and it supplies no rate on `parent (extract k)`.

The exact source file states this boundary itself: the theorem is generic and
supplies no project-specific spectral floor or source estimate.

`[FINITE_CELL][LEAN]`

The current source objects do provide:

```text
sourceCCMFiniteRayleigh;
sourceCCMFiniteRayleigh_coe;
sourceCCMComplexRow_unit;
sourceCCMFiniteMatrix_isHermitian;
sourceCCMComplexRow_inner_residual_eq_zero.
```

These are identities for one cell.  No declaration on the pinned branch proves
`Tendsto`, an eventual bound, or a uniform bound for
`sourceCCMFiniteRayleigh` on the production schedule.

`[COFINAL_FAMILY][PAPER]`

## DECISIVE FALSIFIER

The proposed implication already fails for the simplest Hermitian family.
For `k : Nat`, let

```text
K_k = k I
q_k = e_0.
```

Then for every `k`:

```text
K_k is Hermitian;
q_k is unit;
q_k is an exact minimum eigenvector;
the minimum eigenvalue is epsilon_k = k;
the Rayleigh value of q_k is k.
```

Thus the conclusion of `hermitian_exists_unit_minimum_eigenpair` holds in every
cell, in the strongest possible form: the chosen trial is already the exact
ground vector.

Now fix arbitrary real `aStar` and arbitrary `betaStar > 0`.  Choose a natural
`k` with

```text
k > abs(aStar) + betaStar / 2.
```

Then

```text
abs(k - aStar) >= k - abs(aStar) > betaStar / 2.
```

Therefore no fixed `(aStar, betaStar)` controls this family.

This plant does not claim that the literal CCM sequence behaves this way.  It
kills only the attempted derivation from the minimum-eigenpair theorem.  That
is enough to forbid the proposed Lean source.

`[ABSTRACT][PAPER]` **[C04]**

## WHY A SOURCE WOULD VIOLATE THE NEW RULE

Any honest theorem written now would have to add at least one hypothesis of the
following kind:

```text
Tendsto of the literal source Rayleigh values;
an eventual fixed-shift inequality;
a uniform source-form estimate;
an explicit asymptotic formula with a certified remainder.
```

Such a theorem would have:

```text
CLOSES: []
OPENS:  [a new cofinal analytic input]
```

It would be another bridge around the wall.  The node-admission rule forbids it.
A generic theorem saying `Tendsto -> eventually abs(...) <= betaStar/2` is
therefore also forbidden.

## FINAL PROPOSAL

Do not start the tail PosDef family.  The ordered first supplier remains
unclosed.

The only admissible future source at this position is a direct source theorem
whose conclusion is already the final numerical input:

```text
DIRECT_COFINAL_SOURCE_RAYLEIGH_FIXED_SHIFT_BOUND

exists explicitly precommitted aStar and betaStar > 0 such that
for every production k,
  abs(sourceCCMFiniteRayleigh S (selectedPairIndex S k) - aStar)
    <= betaStar / 2.
```

It must derive the bound from the literal `W02 - WR - Prime` evaluation on the
exact normalized projected prolate trial.  It may not assume convergence,
choose `aStar` after inspecting cells, fit `aStar`, replace the production
schedule, or import the future complement floor. **[C09] [C10]**

If the exact source analysis cannot prove this final inequality without new
premises, kill the fixed-shift representation before attempting either spectral
sign.

## STRONGEST ATTACK

A reviewer may object that the actual CCM Rayleigh values could converge even
though the scalar-matrix plant does not.

Correct.  The kill is not a mathematical negation of CCM proximity.  It is a
source-admission verdict:

```text
the current theorem does not imply the required cofinal statement,
and the pinned repository contains no independent supplier.
```

That is exactly the distinction between failure of a sufficient route and proof
of the negation.

## CODEX DIRECTIVE

```text
NO LEAN EXECUTION.
NO NEW SOURCE FILE.
NO TAIL OR CORRECTED-HEAD WORK.

Permitted next action only after a new source argument exists:
  prove DIRECT_COFINAL_SOURCE_RAYLEIGH_FIXED_SHIFT_BOUND
  with CLOSES=[SOURCE_RAYLEIGH_PROXIMITY_TO_FIXED_SHIFT]
  and OPENS=[].
```

## META CLOSEOUT

**What became smaller?**

The supposedly cheap Rayleigh input is now identified as a genuine cofinal
source estimate.  It is not a consequence of finite Hermitian spectral
existence.

**What was killed?**

```text
per-cell minimum eigenpair
  => one fixed cofinal Rayleigh shift.
```

**What must not be tried again?**

```text
cellwise epsilon_k as a fixed aStar;
fitted or moving shifts;
a generic Tendsto receiver;
a theorem that assumes the desired Rayleigh rate;
starting tail/head signs before the ordered first input closes.
```

**Current smallest named gap:**

```text
DIRECT_COFINAL_SOURCE_RAYLEIGH_FIXED_SHIFT_BOUND
```

**Next cheapest decisive test:**

Expand the exact scalar source Weil value of the normalized projected prolate
trial and determine whether a source-level fixed limit and one-sided remainder
estimate are derivable.  This is a paper/source audit, not a new bridge and not
numerical proof.

**Fate of prior registered predictions:**

No probability was explicitly registered before this audit.  None is invented
retroactively.

```yaml
iteration:
  target: SOURCE_RAYLEIGH_PROXIMITY_TO_FIXED_SHIFT
  status: FATAL
  failed_strategy: derive_cofinal_fixed_shift_from_cellwise_minimum_eigenpairs
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: DIRECT_COFINAL_SOURCE_RAYLEIGH_FIXED_SHIFT_BOUND
  invariant_learned: one fixed aStar and betaStar must be precommitted for the same production schedule
  forbidden_future_move: replace a cofinal scalar estimate by per-cell spectral existence
  next_decisive_test: direct source evaluation and remainder audit for the literal trial Rayleigh value
```
