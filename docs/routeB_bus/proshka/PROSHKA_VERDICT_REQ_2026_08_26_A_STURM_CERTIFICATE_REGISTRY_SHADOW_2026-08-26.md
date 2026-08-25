# STATUS: CONDITIONAL — FREEZE THE FOUR STURM RATE INPUTS, ADMIT A NON-EXCLUSIVE COERCIVE-SPLIT RECEIVER, MAP THE FOUR OPERATOR ALIASES, AND RUN THE V2.1 SHADOW BACKTEST
```yaml
PRIMARY: RUN_WEIGHTED_CONSUMER_WITH_FROZEN_STURM_RATE_LEDGER
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-A
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_THE_UNNUMBERED_2026-08-26_BATCH
  SOURCE_ENTRY: docs/routeB_bus/PROSHKA_QUEUE.md
  SOURCE_HEAD: ec5176835f9163a5c7648e8fec4b641eb2c26712
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  STURM_COMMIT: a3c84e453192507b7e96f6c5f670b761e1dea1d5
  STURM_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmDefectTruncatedEnergy.lean
  STURM_BLOB: 0ce87ceab417e5eea9b376917168187057f1fd6e
  TRANSPORT_RECORD: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_W_TRANSPORT_L1_2026-08-25.md
  FINITE_CERTIFICATE_DOC: docs/FINITE_CERTIFICATE_PRINCIPLE.md
  FINITE_CERTIFICATE_DOC_BLOB: 0144650aea77bbd63e85db259468597d152d2f57
  OPERATOR_REGISTRY: q3.lean.aristotle/COGNITIVE_OPERATORS.md
  OPERATOR_REGISTRY_BLOB: 87901e6920257a45467127d38aa4f263a3932a5b
  SHADOW_PROPOSAL: docs/routeB_bus/PROPOSAL_PROSHKA_V2_1_SHADOW_2026-08-26.md
  SHADOW_PROPOSAL_BLOB: 06019a0cf3e810bf88c27573321c94d6596cbd15
  SUPPLIER_CONTRACT_BLOB: 0c595527b3a35bf9598a7bd1465dcc74b55c3e76
  READ_OUTSIDE_ROUTE_B_BUS:
    - docs/FINITE_CERTIFICATE_PRINCIPLE.md

ITEM_1_STURM_NODE1:
  CODE: STURM_NODE1_FOUR_RATE_INPUTS_RATIFIED_WITH_STRUCTURAL_PACKAGE_LOCK
  DECISION: RATIFY_WITH_SCOPE_REPAIR
  RATE_INPUTS_FROZEN:
    Cd:
      meaning: uniform C0 defect envelope on the physical window
      required_rate: O(lambda^-2)
      supplier: F72.6
    Ce:
      meaning: abs(theta-m*mu) eigenvalue-defect envelope
      required_rate: O(lambda^-2)
      supplier: F72.3B
    Cphi:
      meaning: L1 mass envelope of the scaled physical mode
      required_rate: O(1)
      supplier: F72.6 plus the committed mode-envelope row
    D:
      meaning: L1 mass envelope of u^2*Wdd+2*u*Wd
      required_rate: O(1)
      supplier: W_TRANSPORT_L1_NODE / ctT0 / ctT4
  STRUCTURAL_PACKAGE_NOT_COUNTED_AS_RATE_SUPPLIERS:
    - S and the fixed mode parameters mProject, K, Lambda, c
    - hm, hK, hsep, hLambda
    - W, Wd, Wdd and their derivative/continuity facts
    - mu with 0 < mu
    - the exact cylinder eigenrelation Wdd=(4*pi^2*u^2-mu)*W
    - 0 <= Cd
  MU_CLASSIFICATION: SOURCE_DEFINED_CYLINDER_PARAMETER_NOT_A_RATE_SUPPLIER
  MISSING_RATE_INPUT: NONE
  NODE1_INPUTS_FROZEN: true
  NODE3_WEIGHTED_CONSUMER_AUTHORIZED: true
  SCOPE: COFINAL_FAMILY
  VERIFIER: LEAN_PLUS_PINNED_SOURCE_AUDIT

ITEM_2_FINITE_CERTIFICATE_RECEIVER:
  CODE: COERCIVE_SPLIT_CERTIFICATE_RECEIVER_ADMITTED_NONEXCLUSIVE
  DECISION: ADMIT_AS_NAMED_SUFFICIENT_RECEIVER
  ROUTE_ALIAS: FINITE_CERTIFICATE_RECEIVER
  CANONICAL_MATHEMATICAL_NAME: COERCIVE_SPLIT_CERTIFICATE_RECEIVER
  CONTRACT:
    tail_floor: Q(w) >= mu*norm(w)^2 on V_perp, mu > 0
    interaction: norm(P*T*(1-P)) <= B
    core_floor: Q(v) >= nu*norm(v)^2 on V
    discriminant: B^2 <= nu*mu
    conclusion: Q(h) >= 0 for every h
  FINITE_DIMENSION_REQUIRED_BY_RECEIVER: false
  FINITE_DIMENSION_ENTERS_AT: supplier_of_nu
  EXCLUSIVE_ROOF_SHAPE: false
  ACCEPTED_STRONGER_ALTERNATIVE:
    - exact Schur/Feshbach complement certificate
    - operator-valued interaction certificate retaining cancellation
  PRECOMMIT_GUARD: V_and_T_must_be_source_fixed_before_budget_search
  CATALOG_PREFLIGHT_BEFORE_LEAN: required
  PILLAR_TYPING_POLICY: expose_mu_B_nu_when_lossless_but_do_not_force_scalar_B_when_it_destroys_structure
  SCOPE: ABSTRACT
  VERIFIER: CONDITIONAL

ITEM_3_OPERATOR_REGISTRY:
  CODE: MAP_NONCANONICAL_OPERATOR_TOKENS_DO_NOT_EXTEND_M2_ENUM
  DECISION: CROSSWALK_TO_EXISTING_CANONICAL_OPERATORS
  LIVE_FIELD_RULE: COGNITIVE_OPERATOR_must_use_the_canonical_PROSHKA_M2_token
  HISTORICAL_FILES_MUTATED: false
  MAPPINGS:
    CONSUMER_STRENGTH_REDUCTION:
      canonical: MINIMAL_LEMMA
      relation: RELATED_NOT_EQUIVALENT
      meaning: reduce the requested output to the weakest named theorem the exact consumer can spend
    ENERGY_REPRESENTATION:
      canonical: REPRESENTATION_SHIFT
      relation: RELATED_NOT_EQUIVALENT
      meaning: move the same source-faithful target into an energy or quadratic-form representation
    TYPE_BOUNDARY:
      canonical: UNIT_AUDIT
      relation: RELATED_NOT_EQUIVALENT
      meaning: audit carrier, source family, category, normalization, and shared dependent parameters at an application boundary
    FUNCTIONAL_AUDIT:
      canonical: UNIT_AUDIT
      relation: RELATED_NOT_EQUIVALENT
      meaning: verify that the proved form or functional is the consumer's exact object in the same units and direction
  PARSER_POLICY: retain_original_token_in_alias_or_legacy_field_and_validate_the_canonical_field
  SCOPE: ABSTRACT
  VERIFIER: CONDITIONAL

ITEM_4_V2_1_SHADOW:
  CODE: RUN_PROSHKA_V2_1_POLICY_SHADOW_BACKTEST
  CHOICE: A
  DECISION: RUN_SHADOW_BACKTEST_NO_LIVE_PROMOTION
  LIVE_PROMPT_EDIT: false
  LIVE_SUPPLIER_CONTRACT_EDIT: false
  LIVE_PARSER_EDIT: false
  DATASET_POLICY: reuse_the_frozen_12_checkpoint_Q3_AMDL_V0_historical_dataset_and_add_a_separate_v2_vs_v2_1_policy_score
  HOLDOUT_POLICY: checkpoint_manifest_and_scoring_schema_frozen_before_history_reveal
  SHADOW_BLOCKS:
    - decision_changing_VOI_CLASS
    - certificate_first_gate
    - frontier_hardness_W9_exception
    - ROLE_MODE_JUDGE_AUTHOR
    - prompt_drift_and_runtime_source_locks
  PROMOTION_GATES:
    - PARSER_COMPATIBLE
    - NO_LOST_SAFETY_RULES
    - WRONG_OBJECT_ESCAPE_COUNT_0
    - FALSE_STOP_COUNT_0
    - ZERO_VOI_PROBES_REDUCED
    - NO_POST_HOLDOUT_TUNING
    - OWNER_RATIFIED
    - SUPPLIER_CONTRACT_SYNCHRONIZED
  CERTIFICATE_FIRST_ADVERSARIAL_CHECK: any_load_bearing_local_theorem_false_stopped_by_the_mandatory_cascade_blocks_promotion_of_that_delta
  W9_ADVERSARIAL_CHECK: every_exception_requires_a_literal_compression_witness_and_no_hidden_quantifier_or_assumption_growth
  ROLE_MODE_ADVERSARIAL_CHECK: judge_may_write_the_verdict_but_may_not_semantically_admit_the_source_object_it_authored
  DYNAMIC_CARD_COUNT_DRIFT:
    status: VERIFIED_BUG
    treatment: owner_only_nonbehavioral_maintenance_not_evidence_for_promoting_the_other_deltas
  SCOPE: ABSTRACT
  VERIFIER: CONDITIONAL

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CLOSES:
  - STURM_NODE1_RATE_INPUT_FORK
  - FINITE_CERTIFICATE_RECEIVER_ADMISSION_FORK
  - FOUR_TOKEN_COGNITIVE_OPERATOR_DRIFT
  - PROSHKA_V2_1_IMMEDIATE_ADOPTION_FORK
OPENS: []
CARRIES_OPEN:
  - WEIGHTED_CONSUMER_NODE
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED
  - CONCRETE_MU_B_NU_OR_STRONGER_SCHUR_SUPPLIERS
  - PROSHKA_V2_1_SHADOW_BACKTEST

NEXT_LOAD_BEARING_GAP: WEIGHTED_CONSUMER_NON_TOP_LATTICE_BOUND
DISCRIMINATOR: WEIGHTED_CAUCHY_SCHWARZ_WITH_TOP_LATTICE_EXPLICIT

ROLE_MODE: JUDGE
KERNEL_GATE: NOT_APPLICABLE
SEMANTIC_ADMISSION: CONDITIONAL
VOI_CLASS: POSITIVE
HARDNESS_DELTA: SHRUNK
SCOPE: MIXED_ABSTRACT_AND_COFINAL_FAMILY
VERIFIER: LEAN_PLUS_PINNED_SOURCE_AUDIT_PLUS_CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. STURM node 1

The public theorem `sturm_defect_energy_rate_ledger` proves exactly the requested weighted-energy inequality from four quantitative envelope hypotheses: `hC0`, `hEps`, `hPhi`, and `hWtr`. The source also has structural hypotheses for the fixed mode and cylinder profile. Therefore the literal sentence “nothing else enters” is false if read as the entire Lean signature, but correct after splitting the contract into:

```text
fixed structural data
+
four quantitative rate suppliers.
```

The four quantitative suppliers are now frozen. No fifth rate estimate is missing. In particular, `mu` is part of the fixed cylinder object; it must stay explicit in the bound but is not a new asymptotic supplier. Node 3 may consume the weighted-energy theorem as a black box.

`[COFINAL_FAMILY][LEAN]`

### 2. Finite-certificate receiver

For `h=v+w`, self-adjointness and orthogonality give

\[
Q(h)\ge \nu\lVert v\rVert^2-2B\lVert v\rVert\lVert w\rVert+\mu\lVert w\rVert^2.
\]

The right-hand side is nonnegative exactly under `B^2 <= nu*mu`. Thus the proposed theorem is mathematically sound and is worth naming before the concrete G-budgets exist. It fixes a spendable assembly interface and opens no new analytic supplier.

The name needs one guard: the receiver itself is not finite-dimensional. Finiteness belongs to the supplier of `nu`. More importantly, the scalar interaction norm `B` is only one sufficient representation. An exact Schur/Feshbach certificate may preserve cancellation that the scalar norm destroys. Therefore this receiver is admitted as a named sufficient node, not as the sole legal roof shape. This avoids turning a cheap theorem into a certificate-language prison. `[C10]`

Before any Lean source is written, the executor must query the capability catalog for an existing coercive-split or Schur receiver. The decomposition `V` and the exact operator `T` must be fixed before budget inspection; a post-hoc subspace is a weaker theorem. `[C09]`

`[ABSTRACT][CONDITIONAL]`

### 3. Operator vocabulary

Do not expand the canonical `PROSHKA_M2` enum. All four tokens are narrower descriptions of existing operations. The strict parser should validate the canonical token and retain the historical spelling in an alias/provenance field. Existing verdicts are append-only and must not be rewritten.

The crosswalk is:

```text
CONSUMER_STRENGTH_REDUCTION -> MINIMAL_LEMMA
ENERGY_REPRESENTATION       -> REPRESENTATION_SHIFT
TYPE_BOUNDARY               -> UNIT_AUDIT
FUNCTIONAL_AUDIT            -> UNIT_AUDIT
```

`[ABSTRACT][CONDITIONAL]`

### 4. Proshka v2.1 shadow

Select option **(a)**. Do not adopt the behavioral deltas directly. The proposal changes stopping rules, W9 admission, role separation, headers, and scoring; those can create false stops or process bloat even when each sounds locally sensible.

Run the delta as a policy layer on the already mandated blinded historical dataset rather than creating a second post-hoc corpus. The current live prompt, parser, supplier contract, and mathematical route remain unchanged during the test. The verified stale `C01..C12` count is a factual maintenance bug and may be repaired by the owner independently; it is not evidence that the other policy deltas are safe.

The strongest risk is the universal certificate-first cascade. Some load-bearing work is genuinely a local identity or transport theorem before a global certificate is visible. One such false stop kills promotion of that block. Likewise, the W9 exception survives only with a literal frontier-compression witness and no hidden strengthening of quantifiers or assumptions.

`[ABSTRACT][CONDITIONAL]`

## FINAL PROPOSAL

Proceed on the mathematical mainline now:

```text
frozen node-1 structural package
+ frozen rate suppliers Cd, Ce, Cphi, D
+ kernel-green transport node 2
-> node 3 WEIGHTED_CONSUMER
-> exact top-lattice functional remains isolated.
```

In parallel, Linux may prepare the frozen shadow-policy backtest pairs. That sidecar does not block node 3 and has no authority over the live route.

The coercive-split receiver is admitted to the assembly vocabulary now, but its Lean implementation waits for the mandatory catalog preflight. Pillars may export `(mu,B,nu)` when this loses no structure; exact Schur/Feshbach certificates remain first-class.

## STRONGEST ATTACK

The strongest attack on Item 1 is that the theorem has more than four hypotheses. Correct: it has a fixed structural package. The repaired claim is only that there are exactly four quantitative rate suppliers. No hidden edge or integrability hypothesis remains.

The strongest attack on Item 2 is scalarization. A finite-dimensional interaction can have large operator norm while an exact Schur complement remains positive through cancellation. Therefore “all pillars must feed a scalar triple” is rejected; the receiver is sufficient, not complete.

The strongest attack on Item 4 is process inflation. If the shadow adds fields and reviews but does not change a decision, suppress a zero-VOI probe, catch a semantic counterfeit, or correctly relax a false W9 stop, it has no value and must remain archived.

## CODEX DIRECTIVE

```text
TASK_ID: GOAL058_NODE3_WEIGHTED_CONSUMER
MODE: AUTHOR

TARGET_PATH:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmWeightedConsumer.lean

TARGET_THEOREM:
  sturm_weighted_energy_nonTop_consumer_bound

OBJECTIVE:
  Convert the kernel-green weighted defect-energy bound into the exact W5
  defect Q-comb bound for every active lattice contribution except the
  uppermost edge contribution. Keep the companion factor and the exact top
  functional explicit.

READ_FIRST:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmDefectTruncatedEnergy.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CylinderTransportL1Budget.lean
  docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_STURM_WEIGHTED_ENERGY_AND_EDGE_CONSUMER_2026-08-25.md
  docs/routeB_bus/SUPPLIER_CONTRACT.md

INPUT CONTRACT:
  fixed structural package of sturm_defect_energy_rate_ledger;
  Cd, Ce, Cphi, D and their four envelope inequalities;
  the exact committed W5 cell/lattice decomposition;
  no new analytic supplier.

PROOF ROUTE:
  use weighted Cauchy-Schwarz on the non-top cells in the same physical
  variable and normalization as W5;
  compute the finite companion-factor budget exactly;
  separate the uppermost lattice point before any estimate;
  expose its remaining functional in the conclusion or a named carry-open.

FORBIDDEN:
  replace weighted energy by a whole-window unweighted H1 bound;
  assume a derivative sup norm on the edge sliver;
  hide the top lattice point in a divergent companion sum;
  change the source family, normalization, or downstream consumer;
  add a new analytic hypothesis;
  touch Q3.Main or promote Route B.

CLOSES:
  WEIGHTED_CONSUMER_NODE

OPENS:
  []

CARRIES_OPEN:
  W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED

VALIDATION:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SturmWeightedConsumer.lean
    lake build Q3.Proofs.RouteB.G6N1SturmWeightedConsumer
  WORKDIR repo root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SturmWeightedConsumer.lean

EXPECTED_AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  the non-top W5 contribution is bounded at consumer strength with no new
  supplier, and the top-edge functional remains literal and separately named.

FAILURE_CODE:
  GOAL058_WEIGHTED_CONSUMER_COMPANION_OR_TOP_EDGE_MISMATCH
```

## META CLOSEOUT

**What became smaller?** The Sturm front is no longer “source the derivative.” It is four frozen rate envelopes feeding one weighted-energy theorem and one exact non-top consumer.

**What was killed?** The literal claim that the whole Lean theorem has only four hypotheses; the exclusive scalar-triple roof; four new live cognitive operators; direct v2.1 promotion without evidence.

**What must not be tried again?** Reopen node-1 endpoint analysis, force every certificate through a scalar interaction norm, rewrite immutable verdicts to repair tokens, or tune the shadow after holdout reveal.

**Current smallest named gap:** `WEIGHTED_CONSUMER_NON_TOP_LATTICE_BOUND`.

**Next cheapest decisive test:** compile node 3 while keeping the top lattice point explicit.

**Prior prediction fates:** `P_DERIV_STURM_1` is confirmed, stronger than registered; the exact top-edge consumer prediction remains untested. No retroactive repair.

```yaml
iteration:
  target: 2026_08_26_four_item_batch
  status: PROGRESS
  failed_strategy: exclusive_scalar_receiver_and_unregistered_operator_vocab
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: WEIGHTED_CONSUMER_NON_TOP_LATTICE_BOUND
  invariant_learned: separate_fixed_structural_data_from_quantitative_rate_suppliers
  forbidden_future_move: reopen_sturm_node1_or_force_scalar_B_when_exact_Schur_structure_is_available
  next_decisive_test: kernel_gate_G6N1SturmWeightedConsumer
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
