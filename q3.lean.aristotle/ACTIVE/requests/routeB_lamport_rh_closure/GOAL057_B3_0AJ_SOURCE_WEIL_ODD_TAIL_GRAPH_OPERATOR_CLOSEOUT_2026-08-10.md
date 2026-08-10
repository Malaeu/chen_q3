# GOAL 057 · B3.0AJ closeout — literal source-Weil odd-tail graph operator

Date: 2026-08-10  
Route: `CHALLENGER_NOT_RH`  
Result: `GOAL057_B3_0AJ_SOURCE_WEIL_ODD_TAIL_GRAPH_OPERATOR_AND_CONDITIONAL_INVERTIBILITY_PROVED`

## What closed

The production file
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddTailGraphOperator.lean`
constructs the first literal infinite source outer block for the surviving
inverse-weighted odd-tail route.

It proves:

1. the closed graph of the exact shifted square-root-weight map is a complete
   Hilbert carrier after transport to the `WithLp 2` product;
2. the complete shifted source-Weil form has an exact bounded Riesz operator
   on that carrier;
3. the normalized physical pairs `±(n+1)` generate a literal infinite odd
   tail, defined as a closed span after cutoff `R`;
4. the exact outer block is the orthogonal compression of that graph Riesz
   operator, and is positive without a finite-dimensional argument;
5. the source predicate `SourceWeilOddTailAmbientCoercive i R mu` is the exact
   missing Yoshida-style ambient `L²` supplier;
6. this supplier and the independently available weighted graph bound combine
   to the graph-norm estimate
   `min mu 1 / 2 * ‖x‖² ≤ re ⟪C_out x, x⟫`;
7. the estimate makes `C_out` continuously invertible through Mathlib's
   strict-inner-bound theorem;
8. the literal block instantiates the B3.0AI `R† C_out⁻¹ R` data interface for
   every separately supplied bounded residual.

The actual inverse remains visible. No scalar-floor surrogate was introduced.

## Why this child was selected

B3.0AI had already isolated the lawful generic correction, but its `Tail` and
`outerBlock` were abstract. Local cartography found that the exact closed
square-root-weight graph already supplies a canonical complete Hilbert carrier,
while Mathlib supplies both orthogonal compression and the strict lower-bound
criterion for invertibility.

The narrow honest next child was therefore the literal carrier/operator plus a
source-shaped coercivity seam. This turns the previous vague stop
`SOURCE_ODD_OUTER_BLOCK_POSITIVE_INVERTIBLE_SUPPLIER_MISSING` into one explicit
analytic proposition with the correct quantifiers.

## Validation

```text
Lean SHA-256:
  6f1f83e79eb49b83fa2e5266286a3586933213b61f88bbadf1000bdb101a98d5
Shape:
  22613 bytes, 514 newline-terminated lines, final LF
Public surface:
  39 named definitions/abbreviations/theorems + 4 named instances
Proof DB:
  43 / 43 declarations proven after registered backfill; drift check clean
Direct Lean:
  PASS
External production-import consumer:
  PASS
Target build:
  PASS, 7810 jobs
Full build:
  PASS, 7817 jobs
Direct Q3/Main.lean:
  PASS
scripts/q3_check.sh:
  PASS
Orchestrator tests:
  102 / 102 PASS
Strict Spine:
  P9_STRICT_PASS; semantic index PASS; tool manifest PASS
Public axiom profile:
  propext, Classical.choice, Quot.sound
Forbidden tokens:
  no sorry, admit, axiom, unsafe, or native_decide
```

Three semantic guards fired:

- removing `SourceWeilOddTailAmbientCoercive` does not prove invertibility;
- replacing the closed span by the raw algebraic span does not supply the
  complete-space/orthogonal-projection instance;
- replacing the literal source outer block by identity is rejected by the
  public B3.0AI-data equality.

## Exact boundary

This child does **not** prove:

- `SourceWeilOddTailAmbientCoercive i R mu` for any explicit `R` and `mu`;
- the Yoshida/Suzuki source-domain and normalization crosswalk needed for that
  proposition;
- a bounded literal source residual into the tail;
- source residual summability or a source beta envelope;
- `OddTailGradedResolventBound13` or a bound on the resulting
  `R_out† C_out⁻¹ R_out`;
- a literal odd form-core theorem or the constant odd floor;
- selected `kTrial` operator-domain membership, projection-leakage decay, the
  continuum numerator, `H4a1b`, or RH.

Finite `N = 960` evidence was not used. The coarse checkpoint ledger remains
`0 / 10`.

## Decision record

- Chosen: the closed graph `WithLp 2` carrier, literal closed odd span, exact
  compressed shifted source-Weil Riesz block, and explicit ambient-coercivity
  seam.
- **What was rejected and why:** the plain product was rejected because its max
  norm is not the graph Hilbert norm; the raw algebraic span was rejected
  because it is not known complete; an identity/scalar outer block and the
  finite `N = 960` floor were rejected because both erase the actual infinite
  source operator.
- Feared failure: silently proving invertibility in the wrong norm, or hiding a
  finite-to-infinite extrapolation inside an instance.
- Source of decision: local Codex cartography and direct Lean/Mathlib proof; no
  new Proshka call.
- Next minimal step: prove an explicit source-locked
  `SourceWeilOddTailAmbientCoercive ⟨13,N,...⟩ R mu` supplier from the
  Yoshida/Suzuki theorem chain, with cutoff and normalization visible. The
  residual supplier remains a separate later node.

## ACTIONS LOG

- queried the canonical knowledge base before creating the production object;
- constructed and compiled the exact graph carrier/operator locally;
- materialized one production Lean file and removed the scratch path;
- ran direct Lean, external consumer, three negative semantic guards, target
  and full builds, direct main, project check, proof-DB import/backfill,
  102 orchestration tests, strict Spine and semantic-index validation;
- preserved the unrelated PDF and made no N=480/N=960 run;
- made no Proshka call, Aristotle submission, route promotion, Bus 010 action,
  Goal 055 release, PX claim, or RH claim.

## Standing boundaries

`CHALLENGER_NOT_RH` · `BUS_010 VOID` · `GOAL_055 HOLD` · `H4a1b OPEN` ·
`N480 HOLD` · `PX_RH_CLAIM NOT_MADE`.
