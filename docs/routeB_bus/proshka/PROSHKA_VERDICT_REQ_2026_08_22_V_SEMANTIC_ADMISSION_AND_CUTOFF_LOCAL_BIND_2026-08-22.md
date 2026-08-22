# STATUS: PROVED — U2.3–U2.5 SEMANTICALLY ADMITTED; U2.1 RETIRED; CUTOFF-LOCAL PRODUCTION BIND SELECTED
```yaml
PRIMARY: ADMIT_REQ_V_FORWARD_RANGE_AND_MODULAR_CONSUMER
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REQUEST_COMMIT: 42fd2b6de8ff99d478e4ff9064ba489f8e425762
  REVIEW_HEAD: 3cd0b58b538150f442a70eea894a6ecc49ef076b
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_BLOB: 2ecac60b219e0e520c138d1eaa7dd8665315da5a

ARTIFACTS:
  PREFLIGHT:
    COMMIT: 3c03d408800e319dab79eead5a30b9f5af97feaf
    PATH: docs/routeB_bus/litreview/DLMF_3035_FORWARD_MEMBERSHIP_PROJECT_CROSSWALK_2026-08-22.md
    BLOB: 50bcfaee03c810c28f89a521d8c38c8a9b229941
    STATUS: SOURCE_LOCK_ACCEPTED
  FORWARD:
    COMMIT: 3c348a65c432828588c66d4f94eff1946c59e1a7
    PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SpheroidalCrosswalkForward.lean
    BLOB: b295a7aec703f14b7c84d0b2268dd524c8b1adc8
    STATUS: SEMANTICALLY_ADMITTED
  RANGE:
    COMMIT: a4ceb33a8c9fc482c69c0ce9f03da255920e5623
    PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SpheroidalCharacteristicRange.lean
    BLOB: 015085dfc944ed84542c0dc7cb2c8ad3d0510ce7
    STATUS: SEMANTICALLY_ADMITTED
  CONSUMER:
    COMMIT: eb8aea9ead1dc74a9b205edf6f21fe71cd1e7db0
    PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedThetaEqualityDegreeZeroFourModular.lean
    BLOB: 158290e734cf2eed8656f665ea67429ac32ee0e7
    STATUS: SEMANTICALLY_ADMITTED_AS_CONDITIONAL_RECEIVER

KERNEL_GATE:
  LINUX_REPORTED_FULL_BUILD_JOBS: 7817
  LINUX_REPORTED_BUILD_RESULT: PASS
  LINUX_REPORTED_Q3_CHECK: PASS
  LINUX_REPORTED_SORRY: 0
  LINUX_REPORTED_ADMIT: 0
  LINUX_REPORTED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound
  JUDGE_RERAN_LAKE_BUILD: false
  SOURCE_AND_PROOF_TERM_AUDIT: PASS

V1_SEMANTIC_ADMISSION:
  U2_3_FORWARD:
    status: PROVED
    direction: REGULAR_EVEN_SOURCE_EIGENVALUE_TO_CHARACTERISTIC
    exact_source_predicate_preserved: true
    G_equals_gamma_squared_preserved: true
    Lambda_equals_DLMF_lambda_preserved: true
    split_equals_two_mul_K_minus_one_preserved: true
    reverse_crosswalk_used: false
    paper_verifier_remaining: false
    cutoff_role: DOMAIN_ONLY_NOT_SELECTOR
  U2_4_RANGE:
    status: PROVED
    forward_and_reverse_inclusions_separately_named: true
    mixed_structure_created: false
    source_package_exhaustiveness_used_only_in_reverse: true
  U2_5_CONSUMER:
    status: PROVED_AS_CONDITIONAL_RECEIVER
    range_equality_is_theorem_not_hypothesis: true
    middle_rank_one_is_load_bearing: true
    source_degree_not_confused_with_split_degree: true
    exact_current_hypotheses_are_stronger_than_production_needs: true
    semantic_defect: false

V2_U2_1:
  code: U2_1_RETIRED_BY_NATIVE_REPRESENTATION_SHIFT
  status: ELIMINATED_FROM_CRITICAL_PATH
  proved_as_literal_DLMF_index_crosswalk: false
  DLMF_named_family_materialized_in_Lean: false
  required_for_U2_3_U2_5: false
  paper_card_retained_as_provenance_and_optional_nomenclature: true
  future_literal_claim_evenBranch_eq_lambda_2r_requires_separate_source_crosswalk: true

V3_PRODUCTION_BIND:
  canonical_project_branch: mode4ClassicalEvenEigenvalue
  projectBranch_equals_source_evenBranch: FORBIDDEN_C10_TAUTOLOGY
  project_global_StrictMono_required: false
  project_cutoff_local_strict_order_available: true
  project_first_three_below_twenty_available: true
  source_hsrcCut_independent_numeric_wall: false
  source_hsrcCut_derivable_from_low_range_and_order: true
  numeric_probe_role: FALSIFIER_ONLY_NOT_PREMISE
  selected_repair: CUTOFF_LOCAL_ORDERED_ENUMERATION_LOCK

NEXT_FLOORS:
  V3_0:
    code: MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE
    character: ASSEMBLY
    closes:
      - PROJECT_BRANCH_LOW_RANGE_PROPERTY
    opens: []
    cost: 1/10
  V3_1:
    code: CUTOFF_LOCAL_ORDERED_ENUMERATION_LOCK
    character: ABSTRACT_ORDER_LEMMA
    closes:
      - GLOBAL_PROJECT_STRICTMONO_OVERSTRENGTH
      - HSRC_CUT_AS_SEPARATE_INPUT
    opens: []
    cost: 2/10
  V3_2:
    code: FINITE_LIMIT_SELECTED_THETA_MODULAR_BIND
    character: PRODUCTION_ASSEMBLY
    closes:
      - PROJECT_BRANCH_INHABITANT
      - SOURCE_RANK_TWO_CUTOFF
      - W13_7_SELECTED_THETA_EQUALITY_DEGREE_ZERO_FOUR
    opens: []
    cost: 1/10

DOWNSTREAM_AFTER_V3_2:
  ordering_front: CLOSED
  next_existing_source_front:
    - SATZ9_FIRST_KIND_SOURCE_DATA_PHYSICAL_LIFT
    - F72_1C_SELECTED_PHYSICAL_WINDOW_UNIFORM_RATE
  analytic_wall: L73_2_SELECTED_FERRERS_LEMMA72_RATE
  roof_moved_elsewhere: false

CLOSES:
  - REQ_V_SEMANTIC_ADMISSION
  - U2_3_EVEN_BRANCH_FORWARD_MEMBERSHIP
  - U2_4_MODULAR_CHARACTERISTIC_RANGE
  - U2_5_SELECTED_THETA_MODULAR_CONSUMER
  - U2_1_CRITICAL_PATH_REQUIREMENT
OPENS: []

NEXT_LOAD_BEARING_GAP: MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_PROJECT_FINITE_LIMIT_LOW_RANGE_EQUALITY

REGISTERED_PREDICTIONS:
  P_V_NEXT_1:
    claim: finite_limit_characteristic_low_range_is_a_direct_composition_of_two_existing_iffs
    probability: 0.94
  P_V_NEXT_2:
    claim: cutoff_local_order_lock_closes_without_any_numeric_hsrcCut_or_global_project_StrictMono
    probability: 0.87
  P_V_NEXT_3:
    claim: after_selected_theta_bind_the_next_substantive_wall_is_the_source_fixed_mode_rate_not_ordering
    probability: 0.90
  RETROACTIVE_REPAIR: false

PREDICTION_FATE:
  P_U_FIRST_OBSTRUCTION_PRINTED_CF_VS_LIMUNDER_AT_POLES:
    fate: REFUTED_AS_IMPLEMENTATION_BLOCKER
    source_convention_question: RESOLVED_BY_PRIMARY_SOURCE
    retroactive_repair: false

FAILURE_CODES_FOR_NEXT_TRANSACTIONS:
  - V3_0_FINITE_LIMIT_CHARACTERISTIC_RANGE_API_GAP
  - V3_1_LOCAL_ORDER_LOCK_FALSE_OR_TOO_WEAK
  - V3_2_PROJECT_BRANCH_SOURCE_BRANCH_TAUTOLOGY_C10
  - V3_2_NUMERIC_HSRCCUT_USED_AS_PROOF
  - V3_2_GLOBAL_STRICTMONO_OVERSTRENGTH_REINTRODUCED
  - V3_2_SOURCE_DEGREE_SPLIT_DEGREE_CONFUSION

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE
SECOND_AND_THIRD_FLOORS_AUTHORIZED_NOW: false
ARISTOTLE_AUTHORIZED: false
QUEUE_STATUS_MUTATED: false

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: PROOF_PROGRESS_AND_REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
SCOPE: ABSTRACT
VERIFIER: LEAN_PLUS_SOURCE_AUDIT
```

## ROUTE MAP

### V1 — semantic admission

All three kernel-green modules are **semantically admitted**.

#### U2.3 — the native forward theorem

The theorem acts on the exact source predicate
`RegularEvenSpheroidalEigenvalue`.  It preserves the differential equation

\[
-(1-x^2)f''+2xf'+Gx^2f=(\Lambda+G)f,
\]

and therefore preserves the project convention `G = gamma^2` and project
`Lambda =` DLMF `lambda`.  Pairing this equation against `P_{2k}` gives the
exact `(1-x^2)` moment recurrence; the endpoint flux kills the Lagrange
boundary term. `[ABSTRACT][LEAN]`

The first serious plant is that every even moment could vanish.  The proof does
not assume this away: Stone--Weierstrass plus parity and nontriviality produces
a nonzero even moment, and recursion then forces the normalized head coefficient
to be nonzero. `[ABSTRACT][LEAN]`

The second plant is the pole/continued-fraction ambiguity.  The proof does not
divide through a possibly vanishing finite denominator.  It compares the
polynomially bounded moment solution with the contraction-selected backward
tail by a transported determinant.  The determinant's absolute value is
nondecreasing because `Lower >= Upper`, while an independent polynomial-times-
`(1/2)^n` bound forces it to zero.  This gives the cross-multiplied pair identity
at `K`, hence `mode4RootFunction = 0`, without trichotomy and without a paper
proof term. `[ABSTRACT][LEAN]`

The final theorem uses the source package only through
`P.evenBranch_regular r`; it does not use the reverse crosswalk.  Its hypothesis
`P.evenBranch r < 20` is only the certified contraction-domain guard.  It does
not select the rank or infer a mode number from the cutoff. `[ABSTRACT][LEAN]`

#### U2.4 — modular range equality

The composition keeps the two provenances separate:

```text
source branch -> characteristic     native U2.3 proof;
characteristic -> source branch     project root-to-solution + source exhaustiveness.
```

Both inclusions are named, and the equality is a theorem rather than a field in
a mixed source/project structure.  This passes the C04 category audit.
`[ABSTRACT][LEAN]`

#### U2.5 — modular consumer

The consumer is a correct sufficient theorem.  It receives one proved range
equality, two ordered sequences and cutoff data, then applies the abstract
ordered-enumeration lock at ranks `0,1,2`.  The middle rank remains present and
is what makes the third value identifiable.  No theorem field identifies the
DLMF split degree with an eigenvalue degree. `[ABSTRACT][LEAN]`

Its current hypotheses are stronger than production needs: it asks for global
`StrictMono projectBranch` and a separate `hsrcCut`.  That is an interface-cost
finding, not a semantic defect.  Failure to inhabit a sufficient receiver would
not certify the negation of its conclusion. `[ABSTRACT][PAPER]`

### V2 — U2.1 is eliminated, not proved

The native proof never constructs the named family
`lambda_(2r)^0(G)` as a Lean object.  Therefore the literal statement

```text
P.evenBranch r = DLMF lambda_(2*r)^0(G)
```

has **not** become a Lean theorem. `[ABSTRACT][PAPER]`

It is also no longer load-bearing.  The route now needs only:

```text
source branch values satisfy the characteristic equation;
characteristic solutions exhaust the source branch;
strict order identifies corresponding ranks.
```

Those are exactly U2.3, U2.4 and the ordered lock.  Thus U2.1 is classified as
`ELIMINATED_FROM_CRITICAL_PATH` by a representation shift, not silently
relabeled `PROVED`. `[ABSTRACT][LEAN]`

The preflight/source card remains useful for provenance, printed notation and
publication.  If a future paper-facing theorem literally names the DLMF branch,
that optional crosswalk must still be source-locked.  It may not be obtained by
defining the DLMF family to be the already constructed source branch. **[C04]
[C10]**

### V3 — the two apparent obligations collapse to one exact production bind

The canonical project-side sequence already exists:

```text
mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) : Nat -> Real.
```

It is independent of `BookRegularEvenSpectrumEven`: it is the fixed-index limit
of the literal finite DLMF/Jacobi spectra.  The repository already proves:

1. below `20`, square summability of the normalized DLMF left row is equivalent
   to membership in this finite-limit carrier;
2. the characteristic predicate is equivalent to the same square-summability
   condition;
3. whenever the upper carrier value is below `20`, the carrier is strictly
   increasing between the two indices;
4. the first three carrier values are below `20`. `[ABSTRACT][LEAN]`

Therefore `projectBranch := P.evenBranch` is forbidden.  It would make the
project/source comparison tautological and erase the independent project
carrier. **[C10]**

The added numerical `hsrcCut` probe is consistent with the exact theory, but it
occupies no quantifier.  It stays a falsifier/calibration artifact only.
`[FINITE_CELL][CONDITIONAL]`

#### Why `hsrcCut` follows structurally

Let `a` be the project finite-limit carrier and `b` the source branch.  Assume:

```text
range a below C = range b below C;
b is strictly increasing;
a is strictly increasing whenever its upper value is below C;
a(0), a(1), a(2) are below C.
```

Induct on `j`.

- Since `a(j)` is in the common low range, write `a(j)=b(m)`.  If `m<j`, the
  induction hypothesis and local strictness of `a` contradict this equality.
  Hence `j<=m`, so `b(j)<=a(j)<C`.
- Now `b(j)` is also in the common low range, so write `b(j)=a(n)`.  If `n<j`,
  strictness of `b` contradicts the induction hypothesis.  Hence `j<=n`; local
  strictness of `a` gives `a(j)<=a(n)=b(j)`.

Thus `a(j)=b(j)` and `b(j)<C`.  The source cutoff is an output of the order
lock, not a separate analytic estimate. `[ABSTRACT][PAPER]`

## NEXT FLOORS

| Floor | Exact role | CLOSES / OPENS | Cost | Tags |
|---|---|---|---:|---|
| `V3.0 MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE` | Compose the two existing iff theorems into the low-range equality for `mode4ClassicalEvenEigenvalue`. | `CLOSES=[PROJECT_BRANCH_LOW_RANGE_PROPERTY]`, `OPENS=[]` | 1/10 | `[ABSTRACT][LEAN_READY]` |
| `V3.1 CUTOFF_LOCAL_ORDERED_ENUMERATION_LOCK` | Replace global project `StrictMono` and separate `hsrcCut` by the exact cutoff-local order contract proved above. | `CLOSES=[GLOBAL_PROJECT_STRICTMONO_OVERSTRENGTH, HSRC_CUT_AS_SEPARATE_INPUT]`, `OPENS=[]` | 2/10 | `[ABSTRACT][LEAN_READY]` |
| `V3.2 FINITE_LIMIT_SELECTED_THETA_MODULAR_BIND` | Instantiate the project carrier, local order, source package and range equalities; export ranks `0` and `2` and the source cutoff. | `CLOSES=[PROJECT_BRANCH_INHABITANT, W13_7_SELECTED_THETA_EQUALITY_DEGREE_ZERO_FOUR]`, `OPENS=[]` | 1/10 | `[ABSTRACT][LEAN_READY]` |

Control-v9 sequencing remains in force: execute and semantically admit these
one at a time.  Do not stack V3.1 on a merely kernel-green V3.0.

After V3.2 the ordering/branch-identification front is closed.  The route does
not jump to another roof.  It returns to the existing source-rate chain:

```text
independent Satz-9 source data + physical lift
  -> selected project/source theta bind
  -> F72.1C physical-window O(lambda^-2) rate
  -> L73.2 selected Ferrers Lemma-7.2 rate.
```

The exact `D_0/D_4` polynomial-Gaussian identities are already kernel-proved;
the remaining substantive content is the source witness/physical lift and the
uniform rate port. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

Execute **V3.0 only**.

Registered prediction:

```text
P_V_NEXT_1:
  The proof is a direct extensional composition of
  characteristic <-> l2 row
  and
  l2 row <-> finite-limit carrier membership.
  Probability 0.94.
```

Cheapest decisive test: compile the exact low-range set equality without
importing the source spectrum package.  Success proves that the project branch
is already present and independently characterized.  The likeliest failure is
only a set-normal-form or `.mp/.mpr` orientation mismatch.

Do not run a separate numeric `hsrcCut` proof.  Do not prove global strict
monotonicity of the project carrier.  Both are stronger and more expensive than
the consumer needs.

## STRONGEST ATTACK

The strongest attack on U2.3 is:

> A regular even source eigenfunction may have a bounded moment sequence that
> solves the recurrence, but why must it be the contraction-selected recessive
> branch rather than another bounded solution?

The determinant argument answers this directly.  The moment sequence has a
polynomial bound, the project tail solution has geometric decay, and the
Wronskian transport has amplification factor `Lower/Upper >= 1`.  A nonzero
initial determinant would therefore be simultaneously bounded below and decay
to zero.  No paper uniqueness theorem or reverse inclusion is imported.
`[ABSTRACT][LEAN]`

The strongest attack on the proposed production instantiation is different:

> Set `projectBranch := P.evenBranch`; then every consumer hypothesis is easy.

That is fatal.  It proves an enumeration agrees with itself and does not bind
the independently constructed project carrier.  This is the exact C10
surrogate/tautology kill.  The repaired object is
`mode4ClassicalEvenEigenvalue`. **[C10]**

Finally, the numerical cutoff table cannot close a universal theorem.  The
structural local-order proof makes the table unnecessary; using it as a premise
would be a K7 finite-to-universal violation.

## CODEX DIRECTIVE

```yaml
TASK: MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE
EXECUTOR: CODEX_OR_LINUX_BODY
MODE: ONE_GOAL_ONE_COMMIT

BASE_HEAD: 3cd0b58b538150f442a70eea894a6ecc49ef076b

CREATE_EXACTLY_ONE_LEAN_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1FiniteLimitCharacteristicRange.lean

CREATE_SOURCE_RECORD_SAME_COMMIT:
  docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_V3_0_FINITE_LIMIT_CHARACTERISTIC_RANGE_2026-08-22.md

IMPORT:
  - Q3.Proofs.RouteB.D0Mode4ClassicalCarrierToDLMF3035EvenL2

TARGET_THEOREM: mode4FiniteLimitCharacteristicRangeEquality

TARGET_SHAPE: |-
  theorem mode4FiniteLimitCharacteristicRangeEquality
      (mProject K : Nat)
      (hm : 2 <= mProject)
      (hK : 3 <= K)
      (hsep : forall q >= K,
        (31 / 24 : Real) * mode4JacobiG mProject <=
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
      Set.range
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject))
          ∩ Set.Iio 20
        =
      {Lambda : Real | Lambda < 20 and
        mode4DLMF3035EvenCharacteristicEquation
          (mode4JacobiG mProject) Lambda (2 * (K - 1))}

PROOF_ROUTE:
  - ext Lambda
  - normalize membership in range/intersection/setOf
  - use mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable
  - use mode4DLMF3035EvenLeftCoefficient_sqSummable_iff_exists_finiteLimitSpectrum
  - preserve Lambda < 20; pass Lambda <= 20 only where the characteristic/l2 iff requires it

CLOSES:
  - PROJECT_BRANCH_LOW_RANGE_PROPERTY
OPENS: []

FORBIDDEN:
  - importing BookRegularEvenSpectrumEven
  - defining the project branch from the source branch
  - adding a DLMF paper axiom or typed hole
  - using the hsrcCut numerical probe
  - proving global StrictMono
  - editing any of the three semantically admitted U2.3-U2.5 files
  - sorry
  - admit
  - theorem weakening

PUBLIC_SURFACE:
  - mode4FiniteLimitCharacteristicRangeEquality

EXPECTED_AXIOM_PROFILE:
  mode4FiniteLimitCharacteristicRangeEquality:
    - propext
    - Classical.choice
    - Quot.sound

VERIFICATION_HANDOFF:
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake env lean Q3/Proofs/RouteB/G6N1FiniteLimitCharacteristicRange.lean
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake build Q3.Proofs.RouteB.G6N1FiniteLimitCharacteristicRange
  - WORKDIR: repository_root
    COMMAND: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1FiniteLimitCharacteristicRange.lean

SUCCESS_CODE: V3_0_MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE_LEAN
FAILURE_CODE: V3_0_FINITE_LIMIT_CHARACTERISTIC_RANGE_API_GAP
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: CUTOFF_LOCAL_ORDERED_ENUMERATION_LOCK
```

## META CLOSEOUT

**What became smaller?**

U2.3, U2.4 and U2.5 moved from kernel-green quarantine to semantic admission.
The two apparent downstream obligations became one exact project-carrier
instantiation plus a small local order lemma.

**What was killed?**

- the named DLMF family as a load-bearing Lean object;
- `projectBranch := P.evenBranch`;
- numerical `hsrcCut` as proof;
- global project strict monotonicity as a prerequisite.

**What must not be tried again?**

Do not revive the deprecated mixed interface.  Do not infer a literal DLMF
index equality merely because two objects have the same low characteristic
range.  Do not let the cutoff select a rank.

**Current smallest named gap:**

```text
MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE
```

**Next cheapest decisive test:**

Compile the low-range equality from the two existing iff theorems.

**Fate of prior prediction:**

The U-verdict prediction that the printed continued fraction versus project
`limUnder` at poles would be the first blocker is **refuted as an implementation
blocker**.  The source reading resolved the convention, and the native proof
then avoided importing the paper uniqueness proof.  No retroactive repair is
made.

```yaml
iteration:
  target: REQ-V semantic admission and next production bind
  status: PROGRESS
  failed_strategy: literal_DLMF_family_materialization_on_the_critical_path
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: MODE4_FINITE_LIMIT_CHARACTERISTIC_LOW_RANGE
  invariant_learned: source and project enumerations meet through one exact low solution set, never by aliasing branches
  forbidden_future_move: projectBranch_equals_source_evenBranch_or_numeric_hsrcCut_as_proof
  next_decisive_test: compile_the_low_range_set_equality
  progress_class: PROOF_PROGRESS_AND_REPRESENTATION_PROGRESS
  route_score: 5
```
