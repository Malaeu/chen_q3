# GOAL 057 B3.0AG SOURCE WEIL FORM-CORE TOPOLOGY CLOSEOUT

Date: 2026-08-10
Route: `CHALLENGER_NOT_RH`
Status: `CLOSED_CHILD_PARENT_B3_0_OPEN`
Child: `B3.0AG`

SEARCH_FLAGS: `WHOLE_REPO_NO_IGNORE`, `PRIMARY_SOURCE_PREFLIGHT`,
`EXCLUDE_Q3_PROOFS_PRIMECERT`

ARSENAL_USED: `C04,C07,C09,C10`

## Outcome

The complete shifted source-Weil energy topology on the exact form domain is
now reduced to the graph topology of the already-closed
`sourceArchimedeanShiftedWeightedLpLinearMap`.  The bounded W02/Prime
diagonal is continuous in the ambient Hilbert norm and therefore creates no
additional form-core obstruction.

This is a topology reduction only.  It does not prove that the literal odd
mode span is a form core, does not extend Suzuki Proposition 3.1 from its
smooth source class to the project form domain, and does not prove any
infinite tail coercivity or resolvent-weighted Schur bound.

## Post-pull strategic evidence

The 29 commits pulled from `origin/rh_clean` contain the later Phase-4 audit
chain:

- `PROSHKA_VERDICT_PHASE4_CODE_AUDIT_2026-08-10.md` kills the
  constant-floor surrogate `d⁻¹ R*R` and selects
  `OddTailGradedResolventBound13`;
- `REPORT_NESTED_SCHUR_AUDIT_2026-08-10.md` verifies the finite
  `480 -> 960` nested identity and reports the exact resolvent correction
  alive, while explicitly leaving `infinite_constant_floor` open;
- therefore B3.0AG is retained as useful domain/topology infrastructure, but
  the next selected proof object is the graded resolvent theorem rather than
  an unqualified generic density theorem.

No finite numerical result is promoted here to an infinite theorem.

## Production artifact

- Lean file:
  `q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilFormCoreTopology.lean`
- SHA-256:
  `a3c5b1e2c629df6f6e652f944f8ceec765c535e1e830c3889894a0f034e20d7a`
- Shape: 7,473 bytes, 185 newline-terminated lines, final LF.
- Exact direct import:
  `D0PstarSourceWeilClosedForm`.

## Exact public surface

Exactly five public declarations:

1. `sourceWeilShiftedExtendedQuadraticForm_toReal_eq_weighted_norm_sq_add`;
2. `tendsto_sourceWeilShifted_energy_zero_iff_weighted_graph_zero`;
3. `IsSourceWeilFormCore`;
4. `IsSourceArchimedeanShiftedWeightedGraphCore`;
5. `isSourceWeilFormCore_iff_isShiftedWeightedGraphCore`.

The first theorem gives the exact energy decomposition.  The second proves the
two convergence criteria equivalent on ambient-null sequences.  The two
predicates expose the exact form-core and graph-core contracts.  The final
theorem identifies them.

## Validation

- direct Lean: pass;
- target build: pass, 7,806 jobs;
- full `lake build`: pass, 7,817 jobs;
- direct `Q3/Main.lean`: pass;
- `bash scripts/q3_check.sh`: pass;
- orchestrator unit tests: 90/90 pass;
- external production-import consumer: pass;
- public axiom chain for all five declarations:
  `propext`, `Classical.choice`, `Quot.sound` only;
- proof database: 5/5 declarations imported as proven; repeat import
  idempotent;
- SQLite integrity: `ok` for `knowledge.db`,
  `aristotle_proofs.db`, and `observability.db`;
- no `sorry`, `admit`, `native_decide`, new `axiom`, or `unsafe`;
- the 29 pulled remote commits contain no Lean-tree delta, and all validations
  were rerun after the rebase.

## Mandatory judges

- Exact decomposition consumer: PASS.
- Ambient-null energy/graph equivalence consumer: PASS.
- Form-core/graph-core equivalence consumer: PASS.
- Drop bounded diagonal: FIRED with an unsolved bounded term.
- Drop ambient convergence hypothesis: FIRED because continuity of the bounded
  diagonal can no longer be consumed.
- Replace form-core by Hilbert density: FIRED by a type mismatch.
- All mutations were removed; the production source recompiled afterwards.

## Decision record

- Chosen: isolate the exact topology reduction already forced by the closed
  square-root-weight map and the continuous bounded source-Weil diagonal.
- What was rejected and why: ordinary Hilbert-space density was rejected
  because it does not control the weighted graph norm; direct promotion of
  Suzuki Theorem 4.3 was rejected in this child because its published proof is
  existential and still needs the exact endpoint-zero/domain and explicit
  constant crosswalk; the finite `N=960` nested-Schur PASS was rejected as an
  infinite conclusion because modes above 960 are absent.
- Risk guarded: silently dropping W02/Prime bounded terms, conflating ambient
  density with form-core density, importing a neighboring Suzuki domain by
  resemblance, and replacing the transformed outer resolvent by
  `d⁻¹ I`.

## Preserved boundary

```text
PARENT_B3_0_OPEN
B3_0AG_SOURCE_WEIL_FORM_CORE_TOPOLOGY_REDUCTION_CLOSED
ODD_MODE_SPAN_FORM_CORE13_OPEN
SUZUKI_ODD_WEIL_TAIL_COERCIVITY13_EXPLICIT_OPEN
ODD_TAIL_GRADED_RESOLVENT_BOUND13_OPEN
INFINITE_CONSTANT_FLOOR_OPEN
CONSTANT_FLOOR_RESIDUAL_GRAM_CERTIFICATE_KILLED
FINITE_NESTED_SCHUR_480_960_AUDIT_PASS_ONLY
SOURCE_WEIL_ASSOCIATED_OPERATOR_GRAPH_OPEN
SELECTED_KTRIAL_OPERATOR_DOMAIN_OPEN
NO_PROJECTION_LEAKAGE_DECAY
NO_CONTINUUM_NUMERATOR
COARSE_CHECKPOINTS_CLOSED_0
COARSE_CHECKPOINTS_REMAINING_10
H4A1B_OPEN
CHALLENGER_NOT_RH
BUS_010_VOID
GOAL_055_HOLD
N480_PROOF_EXTRAPOLATION_FORBIDDEN
PX_RH_CLAIM_NOT_MADE
```

## Next real boundary

`OddTailGradedResolventBound13`: formulate and prove a source-faithful
infinite outer-block resolvent estimate that preserves the odd
divided-difference cancellation and bounds
`R_out* C_out⁻¹ R_out`, not the killed surrogate
`d⁻¹ R_out* R_out`.  Its domain leg must remain compatible with the exact
form/graph topology isolated here.

## ACTIONS LOG

- safely rebased three local commits over 29 remote commits;
- preserved the exact foreign staged patch SHA
  `291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b`;
- merged both independent Progress Log histories and regenerated no false
  theorem claim;
- read and adopted the later Phase-4 code-audit ranking;
- proved the exact source-Weil energy/weighted-graph topology reduction;
- ran direct/target/full Lean builds, direct main, q3_check, 90 tests,
  external API and three negative judges;
- imported 5/5 declarations twice without row growth and checked all three
  project databases;
- made no Proshka call, Aristotle submission, checkpoint decrement, route
  promotion, Bus 010 creation, Goal 055 release, PX claim, or RH claim.

PROSHKA_CALL: NONE_LOCAL_FIRST
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PX_RH_CLAIM: NOT_MADE

