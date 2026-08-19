# STATUS: CONDITIONAL — KERNEL-GREEN COMPOSER RATIFIED; UNCONDITIONAL N0/N1 SUPPLIER CLOSURE REFUTED BY ITS ARGUMENTS

```yaml
PRIMARY: G6_N1_GREEN_EXACT_ASSEMBLY_RECOUNT
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: 51a92c593326dd3a761da0f78993f2df9129da70
  GREEN_GATE_PATH: docs/routeB_bus/LINUX_GATE_G6N1_PREANCHOR_GREEN_2026-08-20.md
  GREEN_GATE_BLOB: 8a78c30c84d6fd0fe62bf127d14926c3c5c66a12
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  LEAN_BLOB: c552654e2666eafa6bdbe5eac453ac7bdc7a4c67
  LEAN_SHA256: 88cfc9dea2fa24a1f3a93531d402d3d6a95e7c348cffb9d944b1840bc1f94636

KERNEL_GATE:
  STATUS: GREEN
  ERROR_TRAJECTORY: [36, 5, 2, 0]
  WARNINGS: 0
  Q3_CHECK: ok
  AXIOMS_ALL_NINE: [propext, Classical.choice, Quot.sound]

EXACT_THEOREM_SHAPE:
  CONSTRUCTOR: selectedProlateCofinalSourceDataOfPreAnchorPort
  INPUT_1: D : SelectedProlatePreAnchorData
  INPUT_2: P : CCMLemma73PreAnchorPort D
  OUTPUT: SelectedProlateCofinalSourceData
  PAPER_LIMIT_FIELD: P.convergence
  CONCRETE_INPUT_INHABITANT_PROVED_HERE: false
  OLD_ALL_INDEX_PROLATE_CANONICAL_SOURCE_DATA_CONSTRUCTED: false

CLOSES:
  - preAnchorGwin_zero_eq_sqrtL_mul_innerV0
  - trialNonzero_of_preAnchorGwin_zero_ne
  - preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero
  - eventually_preAnchorGwin_zero_ne_of_CCMLemma73PreAnchorPort
  - selectedProlateCofinalSourceDataOfPreAnchorPort
  - finite_prefix_tail_shift_preserves_m_and_N_cofinality
  - selected_shell_anchor
OPENS: []

REMAINS_OPEN:
  - SELECTED_PROLATE_PREANCHOR_DATA_INHABITANT
  - CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT
  - SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY
  - D0PSTAR_TO_MUNTZ_SAME_FAMILY_LOCALLY_UNIFORM_CROSSWALK
  - SLOT_S2_OF_FIXED_SELECTED_LIMIT

ASSEMBLY_ROW_ADJUDICATION:
  REALZERO_STEP_0_EXACT_OBJECT_COORDINATE_NORMALIZATION:
    status: OPEN_PARTIAL
    reason: selected trial shell and its anchor are typed, but the exact finite ground-family object and normalization are not supplied
  REALZERO_STEP_1_COFINAL_SIMPLE_EVEN_GROUND:
    status: OPEN_UNCHANGED
  REALZERO_STEP_6_CCM_LEMMA_7_3:
    status: OPEN_PROJECT_INHABITANT
    reason: convergence is a field of CCMLemma73PreAnchorPort, not a theorem constructing that port
  GOAL057_STEP_12_CCM_LEMMA_7_3_SELECTED_LIMIT:
    status: OPEN_PROJECT_INHABITANT
  G5_PAIRS_COFINAL:
    status: OPEN_AS_INPUT_TO_SELECTED_PROLATE_PREANCHOR_DATA
    conditional_derivation_after_D: READY
  SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING:
    status: READY_CONDITIONAL_ON_PORT
    independent_rope_after_port_exists: false
  SIMPLE_EVEN_STEP_15_DEDUP_WITH_N1:
    status: REJECT_IMMEDIATE_DEDUP
    reason: N1 concerns the source/Muntz main term; finite or ground canonical-family convergence still requires N2 and the value crosswalk

COUNTER:
  COUNTING_RULE: unique_unconditional_open_suppliers_only
  PRE_GREEN_CLASSICAL: 14
  POST_GREEN_CLASSICAL: 14
  PRE_GREEN_ROUTE058: 14
  POST_GREEN_ROUTE058: 14
  DELTA_CLASSICAL: 0
  DELTA_ROUTE058: 0
  CONDITIONAL_COMPOSER_ROWS_MAY_BE_MARKED_READY: true
  CONDITIONAL_ROWS_MAY_DECREMENT_ROOF_ROPE_COUNT: false

COUNTER_REPLACEMENT_LINES:
  - "G6_N1_PREANCHOR: kernel GREEN; conditional composer proved; concrete D and Lemma-7.3 port inhabitants remain OPEN"
  - "G5 (1) + G6 (8) are still required in both routes at unconditional-supplier level"
  - "+ G2 (0) + G3 (5) = 14 classical"
  - "+ Goal058 (5) = 14 through 058"
  - "Do not print: ProlateCanonicalSourceData witness exists"
  - "Print instead: SelectedProlateCofinalSourceData is constructible from SelectedProlatePreAnchorData and CCMLemma73PreAnchorPort"

COUNTER_FILE_WRITE:
  TARGET: specs_docs/session_start.sh
  AUTHORIZED_FOR_PROSHKA: false
  OWNER_OR_LINUX_PATCH_REQUIRED: true

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT

NEXT_LOAD_BEARING_GAP:
  CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT

SCOPE: COFINAL_FAMILY
VERIFIER: LEAN_PLUS_SOURCE_TYPE_AUDIT
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 4
```

## ROUTE MAP

The Linux gate is fully ratified as a kernel result.  The source now contains nine clean printed declarations, including the exact zero-mode identity, the transfer from a nonzero pre-anchor central value to `TrialNonzero`, finite-prefix extraction, a selected cofinal shell, its anchor, and transport of a supplied locally uniform limit.

The assembly promotion stated in the green closeout is stronger than the theorem types.

The public constructor is

```lean
selectedProlateCofinalSourceDataOfPreAnchorPort
    (D : SelectedProlatePreAnchorData)
    (P : CCMLemma73PreAnchorPort D) :
    SelectedProlateCofinalSourceData
```

and `CCMLemma73PreAnchorPort` stores the locally uniform convergence as the field `P.convergence`.  No declaration in this file constructs an inhabitant of `SelectedProlatePreAnchorData`, and no declaration proves the paper convergence needed to construct `P`.  The file's own source records also state that the paper analytics were not reproved in Lean.

Thus the proved implication is

```text
pre-anchor source packet
+ exact CCM-Lemma-7.3 port
-> selected cofinal source shell
   with TrialNonzero, central nonvanishing, anchor and main-term limit.
```

It is not

```text
exists a concrete source packet and paper port.
```

This distinction is load-bearing.  A structure carrying a theorem as a field is a typed supplier interface, not an inhabitant of that interface.  Treating it as an unconditional supplier is a C10 surrogate error.  Calling the output the old all-index `ProlateCanonicalSourceData` is also a C04 object mismatch: the produced type is the new selected-only `SelectedProlateCofinalSourceData`.

## Exact assembly effects

### REALZERO step 0

Only its trial-side selected shell and anchor are advanced.  The route's exact ground family, ground normalization and ground-to-trial object lock remain open.  Therefore step 0 stays `OPEN_PARTIAL`.

### REALZERO step 1

No finite ground eigenvector, bottom Rayleigh inequality, simple eigenspace or ground normalization appears in the transaction.  Step 1 is untouched.

### REALZERO step 6 and GOAL057 step 12

Both ask for the project-level CCM Lemma 7.3 supplier.  The source defines its exact interface and proves all downstream consequences, but it takes the convergence field as input.  These rows remain open until an inhabitant of `CCMLemma73PreAnchorPort D` is produced from the source-locked paper theorem.

### G5 `PairCofinal`

The selected shell preserves cofinality supplied by `D.mCofinal` and `D.nCofinal`.  It does not produce those facts without `D`.  Hence the shared rope becomes free after the pre-anchor data inhabitant exists, but is not currently discharged.

### Central nonvanishing

This part is genuine progress: it no longer needs an independent hypothesis after the Lemma-7.3 port exists.  `eventually_preAnchorGwin_zero_ne` derives it from the nonzero target and `P.convergence`, and the tail constructor makes it pointwise on the selected tail.  This reduces arity but does not remove the still-open port itself.

## FINAL PROPOSAL

Keep the Lean file and green gate frozen.  Do not edit or weaken them.

Correct only the assembly interpretation:

```text
KERNEL:
  GREEN.

CONDITIONAL COMPOSER:
  PROVED.

CONCRETE N0/N1 SUPPLIERS:
  OPEN.
```

The next source-bearing transaction must construct, rather than assume, one exact `CCMLemma73PreAnchorPort D` and its source packet.  It must have:

```yaml
CLOSES:
  - SELECTED_PROLATE_PREANCHOR_DATA_INHABITANT
  - CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT
OPENS: []
```

Until then both route counts remain `14`.

## STRONGEST ATTACK

The strongest objection is that CCM Lemma 7.3 is already proved on paper, so a Lean structure field is a legitimate import.

The paper theorem may indeed be ratified as `[COFINAL_FAMILY][PAPER]`.  That does not make the project crosswalk automatic.  The missing inhabitant must still bind the paper's exact source function, scalar normalization, centered coordinate, compact-substrip quantifiers and cofinal schedule to `D.index`, `D.pair` and `preAnchorGwinTransformCoordinate`.  Those are precisely the facts encoded by `CCMLemma73PreAnchorPort D`; the current file assumes rather than proves them.

Therefore the repaired statement is not that the paper theorem is false or unusable.  It is:

```text
paper supplier accepted;
exact project inhabitant still open.
```

## CODEX DIRECTIVE

```text
NO LEAN EXECUTION FROM THIS VERDICT.

Next admissible source target:
  construct one source-locked inhabitant
    D : SelectedProlatePreAnchorData
  and
    P : CCMLemma73PreAnchorPort D
  from the exact Ferrers/prolate source and CCM Lemma 7.3.

Forbidden:
  - define P by restating desired convergence without the paper crosswalk;
  - call SelectedProlateCofinalSourceData the old all-index ProlateCanonicalSourceData;
  - decrement roof counts from a conditional theorem;
  - choose a post-hoc schedule.
```

## META CLOSEOUT

**What became smaller?**  The N0/N1 interface is now exact, and central nonvanishing is a theorem-generated consequence rather than an independent supplier.

**What was killed?**  The interpretation that a kernel-green constructor with `D` and `P` arguments proves existence of `D` and `P`.

**What must not be tried again?**  Do not count structure fields as supplied theorems or merge the selected-only shell with the old all-index object by name.

**Current smallest named gap:** `CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT`.

**Next cheapest decisive test:** write the exact paper/project crosswalk statement and verify that no field in its conclusion is merely repeated as a premise.

**Prior predictions:** round-4 kernel predictions are confirmed by the green gate.  The assembly-closure prediction is refuted by source-type audit; this is a new post-gate finding, not a retroactive edit.

```yaml
iteration:
  target: G6_N1_GREEN_ASSEMBLY_RECOUNT
  status: PROGRESS
  failed_strategy: count_kernel_green_constructor_as_unconditional_supplier
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT
  invariant_learned: an interface carrying convergence is not an inhabitant of the interface
  forbidden_future_move: decrement roof counts from conditional structure constructors
  next_decisive_test: exact CCM paper-to-project port inhabitant
```
