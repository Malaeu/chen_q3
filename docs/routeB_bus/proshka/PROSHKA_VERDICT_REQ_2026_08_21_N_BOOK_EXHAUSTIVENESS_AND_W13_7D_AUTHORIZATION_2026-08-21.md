# STATUS: CONDITIONAL — BOOK EXHAUSTIVENESS ROUTE RATIFIED; W13.7D AUTHORIZED
```yaml
PRIMARY: RATIFY_DLMF_CHARACTERISTIC_PLUS_MEIXNER_SCHAEFKE_EXHAUSTIVENESS
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-21-N

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: 3dd126a4a9929d376e8f4a92b2514552fa1844cb
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_BLOB: 2928a4e778bc614e561ef682a30cce4e91093146
  PRIOR_M_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_21_M_W13_7_FIXED_G_BRANCH_IDENTIFICATION_2026-08-21.md
  PRIOR_M_VERDICT_BLOB: 6c19e62c4d99d8500689254a2511ee0fd73682f1
  MS_USAGE_CARD_PATH: docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md
  MS_USAGE_CARD_BLOB: 4b079a010cf8299fad124c874870e66be5a71c61
  CHARACTERISTIC_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenCharacteristicSource.lean
  CHARACTERISTIC_BLOB: fb7f7ad7b9286ee0faaf03056376245306599728
  PROJECT_SPECTRAL_IFF_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4ClassicalCarrierToDLMF3035EvenL2.lean
  PROJECT_SPECTRAL_IFF_BLOB: fc1322f45e9eded5b92ed98895e9bc93b5d28b46
  REGULAR_SOLUTION_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersRegularEvenProlateSolution.lean
  REGULAR_SOLUTION_BLOB: 62de75f6aa29e5f83c0a2beef79bf7f8bf297ecc
  SOURCE_PACKAGE_INTERFACE_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1Satz9SourcePackageInterface.lean
  SOURCE_PACKAGE_INTERFACE_BLOB: be80f839c969397f7d8307bf517a525d99be24d1

QUEUE_DISCIPLINE:
  OLDER_REQ_M_QUEUE_FLAG: OPEN_AWAITING_LINUX_HARVEST
  OLDER_REQ_M_VERDICT_ALREADY_MATERIALIZED: true
  QUEUE_STATUS_MUTATED: false

DIRECT_ANSWER:
  proposed_third_route_legal: true
  book_replaces_all_DLMF_inputs: false
  selected_route: HYBRID_DLMF_EQUATION_PLUS_BOOK_REGULAR_SPECTRUM
  book_alone_closes_project_characteristic_range: false
  book_plus_existing_project_root_to_regular_solution_bridge: sufficient
  DLMF_30_4_COMPLETENESS_ROUTE_REQUIRED: false
  project_G_zero_continuation_required: false
  W13_7D_ABSTRACT_ORDERED_ENUMERATION_AUTHORIZED: true
  W13_7B_LEAN_CLOSED: false
  W13_7E_CLOSED: false

SOURCE_CARGO:
  preserved:
    - order_m_equals_zero
    - project_G_equals_source_gamma_squared
    - project_Lambda_equals_source_lambda
    - literal_DLMF_30_3_5_30_3_7_characteristic_normalization
    - regular_endpoint_boundary_class
    - even_parity
    - real_simple_spectrum
    - fixed_G_strict_order
  not_claimed:
    - same_parameter_implies_same_eigenvalue
    - cutoff_twenty_selects_degree_four
    - book_branch_is_definitionally_project_carrier
    - paper_theorem_is_Lean_proved

TWO_INCLUSIONS:
  SOURCE_TO_CHARACTERISTIC:
    source: DLMF_30_3_5_one_way_solution_statement
    status: PAPER_PROVED_PORT_OPEN
  CHARACTERISTIC_TO_SOURCE:
    chain:
      - project_characteristic_iff_root
      - root_supplies_nonzero_even_closed_window_regular_solution
      - Meixner_Schaefke_exhausts_regular_endpoint_eigenvalues
      - simplicity_and_parity_force_even_source_degree
    status: PAPER_PLUS_LEAN_CROSSWALK_OPEN

W13_7:
  A_PARAMETER_AND_CHARACTERISTIC_LOCK: CLOSED_LEAN
  B_SOURCE_EVEN_SOLUTION_SET_AND_CUTOFF:
    status: PAPER_PROVED_PORT_OPEN
    chosen_source_for_exhaustiveness: MEIXNER_SCHAEFKE_3_22_SATZ_1
    DLMF_role: CHARACTERISTIC_NORMALIZATION_AND_FORWARD_MEMBERSHIP
    BOOK_role: REVERSE_EXHAUSTIVENESS_REALITY_SIMPLICITY_PARITY
  C_PROJECT_EVEN_SOLUTION_SET_BELOW_TWENTY: CLOSED_LEAN
  D_FIXED_G_ORDERED_ENUMERATION_LOCK:
    status: AUTHORIZED_LEAN_READY
    mathematical_cost: 1_of_10
  E_SELECTED_THETA_EQUALITY_AND_PACKAGE_TRANSPORT:
    status: OPEN_MECHANICAL_AFTER_B_AND_D

MINIMAL_MISSING_IDENTITY:
  name: W13_7B_BOOK_REGULAR_SPECTRUM_TO_DLMF3035_CHARACTERISTIC_RANGE
  statement: >-
    For every production k, with G_k > 0 and the source-locked even split s_k,
    the real numbers Lambda < 20 satisfying the literal DLMF 30.3.5 even
    characteristic equation are exactly the values lambda_(2*r)^0(G_k), r in Nat.
  forward_source: DLMF_30_3_5
  reverse_source: MEIXNER_SCHAEFKE_3_22_SATZ_1_PLUS_PROJECT_REGULAR_SOLUTION

PREDICTION_FATE:
  P_M_NEXT_1_DLMF_EXHAUSTIVE_INTERFACE: REFUTED
  M_REGISTERED_MOST_LIKELY_ONE_WAY_FAILURE: CONFIRMED
  P_M_NEXT_2_W13_7D_IS_BOOKKEEPING: SUPPORTED_NOT_YET_KERNEL_TESTED
  retroactive_repair: false

REGISTERED_PREDICTIONS:
  P_N_NEXT_1:
    claim: W13_7D_generic_ordered_enumeration_compiles_with_standard_axioms
    probability: 0.88
  P_N_NEXT_2:
    claim: first_W13_7B_port_failure_is_interface_or_provenance_shape_not_new_analysis
    probability: 0.78
  most_likely_first_failure: LEAN_SET_RANGE_INITIAL_SEGMENT_NORMAL_FORM

CUTOFF_TWENTY:
  role: ADMISSION_ONLY
  selector_role: REJECTED
  numerical_table_role: FALSIFIER_ONLY
  proof_role: NONE

CLOSES:
  - REQ_N_SOURCE_SELECTION_ADJUDICATION
  - W13_7B_EXHAUSTIVENESS_SOURCE_SELECTION
  - W13_7D_EXECUTION_AUTHORIZATION
OPENS: []

NEXT_LOAD_BEARING_GAP: W13_7B_BOOK_REGULAR_SPECTRUM_TO_DLMF3035_CHARACTERISTIC_RANGE
NEXT_CHEAPEST_DECISIVE_TEST: COMPILE_W13_7D_GENERIC_ORDERED_ENUMERATION

FAILURE_CODES:
  - W13_7_BOOK_ENUMERATES_REGULAR_SPECTRUM_NOT_ARBITRARY_ROOTS
  - W13_7_PROJECT_ROOT_TO_REGULAR_ENDPOINT_CLASS_GAP
  - W13_7_PARITY_WITHOUT_SIMPLICITY_CANNOT_SELECT_EVEN_BRANCH
  - W13_7_DLMF_ONE_WAY_MEMBERSHIP_USED_AS_IFF
  - W13_7_CUTOFF_ADMISSION_USED_AS_MODE_SELECTOR
  - W13_7_SPLIT_DEGREE_CONFUSED_WITH_SOURCE_DEGREE
  - W13_7D_ORDERED_RANGE_INDUCTION_API_GAP

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: W13_7D_FIXED_G_ORDERED_ENUMERATION_LOCK
ARISTOTLE_AUTHORIZED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
SCOPE: ABSTRACT
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
```

## ROUTE MAP

### Direct verdict

The proposed third route is admissible, with one correction:

```text
Do not replace DLMF by the book.
Use DLMF for the exact characteristic equation and the forward inclusion.
Use Meixner–Schäfke for the reverse exhaustion of the regular endpoint spectrum.
```

This is a source decomposition, not a source substitution.

The DLMF wording found by the request is one-way: the characteristic equation
"has the solutions" `lambda_(m+2*j)^m`. That supplies

```text
lambda_(2*r)^0(G)
  -> literal even characteristic equation.
```

It does not supply the reverse implication.

Meixner–Schäfke §3.22 Satz 1 supplies the missing reverse spectral statement:
all eigenvalues of the regular endpoint problem are real and simple, and all
real eigenvalue pairs lie on the curves `lambda_n^m(gamma^2)`. At `m=0`, the
parity clause identifies the even branches as the degrees `n=2*r`.
`[ABSTRACT][PAPER]`

### The hidden category bridge

The book enumerates **regular endpoint eigenvalues**. It does not enumerate
arbitrary algebraic roots of a project predicate. Therefore the definite
article in the book is not, by itself, W13.7B.

The missing category change is already available on the project side:

```text
literal characteristic equation
  <-> project root function = 0
  -> nonzero even Ferrers solution
     continuous on [-1,1]
     C2 on (-1,1)
     satisfying the exact prolate ODE.
```

That is a member of the regular endpoint boundary class consumed by the book.
Consequently every project characteristic root below the production cutoff is
one of the book eigenvalues. Since the project solution is even, while the
book's solution parity is the parity of `n-m`, simplicity excludes an odd `n`:
an odd and an even nonzero solution at the same simple eigenvalue cannot coexist.
Thus `n=2*r`.

This closes the mathematical reverse inclusion without DLMF 30.4 completeness
and without constructing a project analytic branch from `G=0`.
`[ABSTRACT][PAPER_PLUS_LEAN]`

### Exact repaired W13.7B contract

For each precommitted production `k`, let

```text
G_k = gamma_k^2 > 0;
s_k = the source-locked even split.
```

The source interface must state:

```text
{Lambda | Lambda < 20 and
  mode4DLMF3035EvenCharacteristicEquation G_k Lambda s_k}
=
{Lambda | Lambda < 20 and
  exists r, lambda_(2*r)^0(G_k) = Lambda}.
```

The two directions have different provenance and must remain visibly separate:

```text
right -> left: DLMF 30.3.5;
left -> right: project root-to-regular-solution + Meixner–Schäfke Satz 1.
```

Collapsing them into one citation would hide the exact object mismatch caught by
C04.

### W13.7D is authorized

The generic ordered-enumeration theorem is independent of the paper port and may
now be implemented. A suitable semantic statement is:

```text
For strictly increasing a,b : Nat -> Real, cutoff C and rank R,
if
  range(a) intersect (-infinity,C)
    = range(b) intersect (-infinity,C),
and a(j), b(j) < C for every j <= R,
then a(j) = b(j) for every j <= R.
```

Production uses `R=2`:

```text
project ordinal j = 0,1,2;
source degree n = 2*j = 0,2,4.
```

The intermediate ordinal `j=1` is load-bearing for the order argument even
though the final packet consumes only `j=0` and `j=2`.
`[ABSTRACT][LEAN_READY]`

### The cutoff is not a selector

The request's table confirms the already registered structural warning:
`Lambda < 20` admits the selected branches but does not isolate them. Higher
even branches enter below the cutoff as `G` grows. The table is a useful
falsifier, but it is based on leading asymptotics and must not become a proof
premise.

Therefore the selected branch is determined by fixed-`G` order, not by the
cutoff. Any theorem that infers `r <= 2` merely from `Lambda < 20` is rejected.

## FINAL PROPOSAL

Use the hybrid source route:

```text
DLMF exact characteristic + forward membership
  + project root-to-regular endpoint solution
  + Meixner–Schäfke exhaustive real simple spectrum and parity
  -> exact even source/project solution-set equality below 20
  + W13.7D strict-order enumeration
  -> selected theta equality for degrees 0 and 4.
```

The cheapest next action is the unconditional abstract W13.7D theorem. It is a
small independent proof, closes one named floor, opens no supplier, and does not
pretend that the paper source has been formalized.

After W13.7D is kernel-green, materialize W13.7B as a source interface with the
two inclusions separated by provenance. Do not encode Meixner–Schäfke as a fake
Lean axiom.

## STRONGEST ATTACK

### Attack — the book classifies a different object

A reviewer can correctly object:

> Meixner–Schäfke classifies eigenvalues admitting regular endpoint solutions.
> Your project predicate is a continued-fraction equation. Why must each root of
> that predicate be a book eigenvalue?

Without the project theorem producing a nonzero even closed-window regular
Ferrers solution, this objection is fatal. The book would close only one half of
the crosswalk.

The repair is already present and source-locked: the project characteristic
predicate is equivalent to the root function, and a root constructs the regular
solution. Therefore the objection does not kill the selected route, but it must
remain an explicit edge in the theorem graph. **[C04]**

A second objection is parity:

> An even project solution does not by itself prove that the source label is
> even if the same eigenvalue has a multidimensional eigenspace.

This is why the book's word `einfach` is load-bearing. Simplicity converts the
parity of the project solution into the parity of the source branch. Dropping
simplicity invalidates the branch selection.

Finally, the cutoff calculation cannot repair either issue. It is not exact and
it does not isolate the branch.

## CODEX DIRECTIVE

```text
TASK: W13_7D_FIXED_G_ORDERED_ENUMERATION_LOCK

Create exactly one Lean file:
  Q3/Proofs/RouteB/G6N1FixedGOrderedEvenSpectrumEnumeration.lean

Prove one generic theorem, with an equivalent Lean signature allowed only if it
preserves all quantifiers:

  theorem strictMono_eq_on_Iic_of_range_inter_Iio_eq
      (a b : Nat -> Real) (C : Real) (R : Nat)
      (ha : StrictMono a) (hb : StrictMono b)
      (hrange : Set.range a ∩ Set.Iio C = Set.range b ∩ Set.Iio C)
      (haCut : forall j <= R, a j < C)
      (hbCut : forall j <= R, b j < C) :
      forall j <= R, a j = b j

Proof route:
  induction on j;
  use equality of the sublevel ranges to obtain the matching ordinal;
  use strict monotonicity and the induction hypothesis to exclude every ordinal
  below or above j.

Required plant:
  remove either strict-monotonicity hypothesis and exhibit two different
  enumerations of the same sublevel range. The plant is documentation/test only;
  it must not enter the theorem assumptions.

Forbidden shortcuts:
  - no source eigenvalue, project carrier, ODE or paper axiom in this file;
  - no finite cutoff cardinality assumption;
  - no identification of split degree with source degree;
  - no `sorry`, `admit`, new axiom or theorem weakening;
  - do not touch Q3.Main or Route state.

Validation:
  WORKDIR: q3.lean.aristotle
    lake env lean Q3/Proofs/RouteB/G6N1FixedGOrderedEvenSpectrumEnumeration.lean
    lake build Q3.Proofs.RouteB.G6N1FixedGOrderedEvenSpectrumEnumeration

  WORKDIR: repository root
    scripts/q3_check.sh \
      Q3/Proofs/RouteB/G6N1FixedGOrderedEvenSpectrumEnumeration.lean

Expected axioms:
  [propext, Classical.choice, Quot.sound]

Success code:
  W13_7D_FIXED_G_ORDERED_ENUMERATION_LEAN

Failure code:
  W13_7D_ORDERED_RANGE_INDUCTION_API_GAP

Return:
  exact theorem name;
  exact commands and stdout;
  axiom profile;
  whether the plant fails as registered;
  next gap unchanged as
    W13_7B_BOOK_REGULAR_SPECTRUM_TO_DLMF3035_CHARACTERISTIC_RANGE.
```

## META CLOSEOUT

**What became smaller?**

W13.7 no longer needs DLMF 30.4 completeness or a project branch-continuation
theory. The analytic content is compressed to one exact source-range identity
with two separately sourced inclusions.

**What was killed?**

- DLMF 30.3.5 as an exhaustive iff by itself;
- the cutoff `20` as a branch selector;
- same parameter / same equation as automatic eigenvalue identity;
- project continuation from `G=0` as the default repair.

**What must not be tried again?**

Do not infer exhaustiveness from `has the solutions`. Do not infer selected mode
from the cutoff. Do not define the book branch by the project carrier. Do not
hide the root-to-regular-solution edge.

**Current smallest named gap:**

```text
W13_7B_BOOK_REGULAR_SPECTRUM_TO_DLMF3035_CHARACTERISTIC_RANGE
```

**Next cheapest decisive test:**

Compile the generic W13.7D ordered-enumeration theorem.

**Fate of prior predictions:**

`P_M_NEXT_1` is refuted. The separately registered likely one-way failure is
confirmed. `P_M_NEXT_2` remains supported but untested by the kernel. No
prediction was retroactively repaired.

**Memory entry:**

```yaml
iteration:
  target: W13.7 fixed-G branch identification
  status: PROGRESS
  failed_strategy: DLMF_30_3_5_EXHAUSTIVE_READING
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: W13_7B_BOOK_REGULAR_SPECTRUM_TO_DLMF3035_CHARACTERISTIC_RANGE
  invariant_learned: regular_endpoint_spectrum_and_characteristic_roots_need_an_explicit_bridge
  forbidden_future_move: use_cutoff_or_one_way_membership_as_branch_selection
  next_decisive_test: compile_W13_7D_generic_ordered_enumeration
```
