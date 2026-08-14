# STATUS: CONDITIONAL — DLMF 30.3.5 CLOSES THE MATHEMATICAL ROOT SET; ONE SOURCE THEOREM IS STILL UNMATERIALIZED
```yaml
PRIMARY: REPAIR_LITERAL_ROOT_CROSSWALK_TO_DLMF3035_SOURCE_IMPORT
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PACKET_COMMIT: 3bff86eeae438c94c6a034a19f089d55db723d0e
  PACKET_SHA256_EXPECTED: 003ef3c0d2849fa006815786eb759c8ffb301364afa7740f13d6460c7325b00a
  CURRENT_HEAD_OWNER_REPORTED: 9eaa0f748f5e967fa7f6af71913cce6e66108da6
  PACKET_BYTES_REHASHED_BY_THIS_RUNTIME: false
  PACKET_FETCH: CACHE_MISS
  INDEPENDENT_SOURCE_REAUDIT:
    DLMF_30_3_5: PASS
    CURRENT_ROOT_FUNCTION_OBJECTS: PASS
    CURRENT_DETERMINANT_CROSSWALK: PASS
    CURRENT_INTERNAL_FINITE_LIMIT_CARRIER: PASS

RULING:
  LITERAL_ROOT_CROSSWALK_MISSING_AS_MATHEMATICAL_MECHANISM: false
  LITERAL_ROOT_CROSSWALK_MISSING_IN_LEAN: true
  DLMF_30_3_5_CLOSES_ROOT_SET_NONCIRCULARLY: true
  DLMF_30_16_3_REQUIRED_FOR_INTERNAL_CARRIER_NAME: true
  ENDPOINT_COUNT_OR_ROOT_BRACKET_USED: false
  FINITE_NUMERICS_USED: false

SMALLEST_MISSING_SOURCE_OBJECT:
  NAME: mode4DLMF3035EvenCharacteristicEquation
  ROLE: exact_external_equation_in_project_units
  STATUS: NOT_IN_CURRENT_TREE

SOURCE_THEOREM:
  NAME: mode4DLMF30163_3035_evenCharacteristicSolutions
  STATUS: PAPER_PROVED_NOT_LEAN_MATERIALIZED

LOCAL_ADAPTER_AFTER_SOURCE_THEOREM:
  NAME: mode4HermitianSchurMatrix_det_eq_zero_iff_exists_classicalEvenEigenvalue
  STATUS: THEOREM_HEAD_READY_AFTER_SOURCE_IMPORT

ARISTOTLE: NOT_AUTHORIZED
ARISTOTLE_REASON:
  - missing_content_is_the_external_DLMF_solution_set_theorem
  - adding_the_solution_set_as_a_binder_would_create_a_receiver
  - current_imports_do_not_prove_the_source_theorem
  - Aristotle_may_be_used_only_for_the_local_adapter_after_source_materialization

G1: OPEN
G3: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
RH_CLAIM: false
BUS_010: VOID

SUCCESS: G3_DLMF3035_LITERAL_ROOT_CROSSWALK_SOURCE_MATERIALIZED
STOP: G3_DLMF3035_SOURCE_THEOREM_NOT_LEAN_MATERIALIZED

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: LITERATURE_BRIDGE
ROUTE_SCORE: 5
```

## ROUTE MAP

| Object | Ruling | Scope / verifier |
|---|---|---|
| DLMF 30.3.5 solution set | Exact source supplier: for even split index, the continued-fraction equation has precisely the even spheroidal eigenvalues. | `[ABSTRACT][PAPER]` |
| DLMF 30.16.3 | Identifies the same-index finite DLMF eigenvalue limit with the classical eigenvalue; this supplies the name attached to the internal iInf carrier. | `[COFINAL_FAMILY][PAPER]` |
| `mode4RootFunction` | Exact project left/right matching equation at split `K`; coefficients, shift, and recessive right tail are already source-crosswalked. | `[ABSTRACT][LEAN]` |
| `mode4HermitianSchurMatrix.det` | Exact positive-factor/determinant crosswalk to `mode4RootFunction`. | `[FINITE_CELL][LEAN]` |
| Desired literal root crosswalk | Mathematically determined, but not yet a Lean theorem because the exact DLMF 30.3.5 solution-set theorem is absent as a formal source declaration. | `[ABSTRACT][CONDITIONAL]` |

## 1. Mathematical adjudication

`LITERAL_ROOT_CROSSWALK_MISSING` is too broad.

The correct classification is:

```text
mathematical/source mechanism:
  RECOVERED.

Lean materialization:
  MISSING.
```

For DLMF order `m = 0` and any even nonnegative split degree, DLMF 30.3.5 states that its two-sided continued-fraction equation has exactly the solutions

\[
\lambda=\lambda_{2j}^{0}(G),\qquad j=0,1,2,\ldots.
\]

This is an exact root-set theorem, not an asymptotic statement and not a numerical approximation.

The current project already supplies the other side of the dictionary:

1. the literal project coefficients equal the DLMF recurrence coefficients;
2. the project parameter is the DLMF spheroidal eigenvalue
   \[
   \Lambda=\lambda,
   \]
   while the differential energy is
   \[
   \chi=\Lambda+G;
   \]
3. `mode4LeftPair` is the regular left-boundary solution
   \[
   a_{-1}=0,\qquad a_0=1;
   \]
4. `mode4RightTailLimit` is the canonical recessive right continued fraction;
5. `mode4RootFunction = 0` is exactly equality of those two branches at the split;
6. the Schur determinant is a nonzero positive factor times this root function.

For the current index convention, DLMF's even split degree is

\[
p_{\mathrm{DLMF}}=2(K-1).
\]

The `+1` is load-bearing: the project root compares \(a_K/a_{K-1}\).

Therefore DLMF 30.3.5 and the current recurrence/tail crosswalk identify the literal Schur roots with the classical even spectrum without using endpoint counts, a root bracket, or an already supplied indexed coefficient row.

This is noncircular.

## 2. Exact source object

The source object must be independent of `mode4RootFunction`.

It must encode the literal DLMF 30.3.5 equation from the DLMF coefficients:

```lean
noncomputable def mode4DLMF3035EvenCharacteristicEquation
    (G Λ : ℝ) (splitDegree : ℕ) : Prop
```

Required semantic guard:

```text
splitDegree is even;
left fraction terminates at degree zero;
right fraction is the recessive infinite continued fraction;
coefficients are the literal DLMF 30.3.7 coefficients;
the object is not defined by mode4RootFunction = 0.
```

Defining this predicate as `mode4RootFunction ... = 0` would be a C10 tautological surrogate and is forbidden.

## 3. Exact source theorem head

This theorem combines the exact source statements DLMF 30.16.3 and 30.3.5 with the already materialized internal finite-limit carrier:

```lean
namespace Q3.RouteB

theorem mode4DLMF30163_3035_evenCharacteristicSolutions
    (G Λ : ℝ)
    (hG : 0 < G)
    (K : ℕ)
    (hK : 1 ≤ K) :
    mode4DLMF3035EvenCharacteristicEquation
        G Λ (2 * (K - 1))
      ↔
    ∃ p : ℕ,
      mode4ClassicalEvenEigenvalue G p = Λ
```

This is the first missing source theorem.

It must not bind:

```text
the desired equivalence;
an endpoint count;
a supplied Schur root;
a supplied coefficient row;
a supplied classical index;
a determinant-nonzero fact.
```

## 4. Exact local adapter head

After the source theorem above is in the tree, the bounded project adapter is:

```lean
namespace Q3.RouteB

theorem mode4HermitianSchurMatrix_det_eq_zero_iff_exists_classicalEvenEigenvalue
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20) :
    (mode4HermitianSchurMatrix mProject Λ K).det = 0
      ↔
    ∃ p : ℕ,
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) p = Λ
```

A useful intermediate theorem is:

```lean
theorem mode4RootFunction_eq_zero_iff_exists_classicalEvenEigenvalue
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20) :
    mode4RootFunction mProject K Λ = 0
      ↔
    ∃ p : ℕ,
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) p = Λ
```

## 5. Allowed imports for the later local adapter

```lean
import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierHeadUpper
import Q3.Proofs.RouteB.D0Mode4PSWFLegendreCanonicalIdentification
import Q3.Proofs.RouteB.D0Mode4SchurHermitianSymmetrization
import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenCharacteristicSource
```

The last source module does not currently exist. It is the prerequisite.

Forbidden direct imports:

```text
endpoint count 2/3 files;
finite interval certificates;
Goal 026 numerical brackets;
root-existence receivers;
ordered-psi4 constructors;
Route/RH exports.
```

## 6. Required current-tree suppliers

The local adapter may consume only exact existing declarations of these roles:

```text
mode4JacobiCoefficients_eq_pswfLegendre_evenCrosswalk

mode4RootFunction_eq_zero_iff_match

mode4BackwardTail_tendsto_rightTailLimit
and the canonical recessive-tail identification/uniqueness layer

mode4DLMF3084_3085_shiftedBoundaryRatio_eq_canonical
or the weaker exact recurrence/tail crosswalk it packages

det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det

det_mode4SchurMatrix_eq_upperProd_mul_rootFunction
and positivity of mode4JacobiUpperProd

mode4ClassicalEvenEigenvalue
and its finite-limit convergence package
```

No source endpoint count is an input.

## 7. Mandatory falsifiers

### P1 — tautological source predicate

Mutation:

```text
mode4DLMF3035EvenCharacteristicEquation G Λ p :=
  mode4RootFunction mProject K Λ = 0
```

Required stop:

```text
G3_DLMF3035_SOURCE_EQUATION_TAUTOLOGICAL
```

### P2 — unit shift

Mutation:

```text
classical carrier = Λ + G
```

instead of:

```text
project Λ = DLMF λ;
differential energy χ = Λ + G.
```

Required stop:

```text
G3_DLMF3035_PROJECT_SHIFT_MISMATCH
```

### P3 — split index

Mutation:

```text
splitDegree = 2 * K
```

instead of:

```text
splitDegree = 2 * (K - 1).
```

Required stop:

```text
G3_DLMF3035_SPLIT_INDEX_MISMATCH
```

### P4 — wrong parity family

Mutation: use the odd DLMF solution family or map internal index `p` to degree `2*p+1`.

Required stop:

```text
G3_DLMF3035_EVEN_INDEX_MISMATCH
```

### P5 — finite-tail surrogate

Mutation: replace `mode4RightTailLimit` by terminal-zero finite backward tail.

Required stop:

```text
G3_DLMF3035_FINITE_TAIL_SURROGATE
```

### P6 — circular endpoint route

Mutation: prove root equivalence using endpoint counts `2/3`, an existing root bracket, or a supplied root.

Required stop:

```text
G3_DLMF3035_ENDPOINT_COUNT_CIRCULARITY
```

### P7 — one-direction source import

Mutation: prove only that every classical eigenvalue is a Schur root, while using the result to infer that a separator avoids all Schur roots.

Required stop:

```text
G3_DLMF3035_ROOT_CROSSWALK_ONE_DIRECTION_ONLY
```

## 8. Aristotle boundary

```text
ARISTOTLE_NOT_AUTHORIZED
```

Reason:

The remaining missing theorem is the external DLMF solution-set theorem and its identification with the internal finite-limit carrier. That is the source theorem itself.

A task with

```lean
hDLMF :
  mode4DLMF3035EvenCharacteristicEquation ... ↔ ...
```

as a binder would be another receiver. It would not materialize the source supplier.

Aristotle becomes appropriate only after `D0Mode4DLMF3035EvenCharacteristicSource.lean` exists and is independently accepted. At that point the local root/determinant adapter is a bounded algebraic task.

## FINAL PROPOSAL

Run one read-only source-materialization transaction:

```text
GOAL058_G3_DLMF3035_EVEN_CHARACTERISTIC_SOURCE_CONTRACT
```

It must produce the exact definition and source theorem contract above, with official DLMF equation bytes, the project parameter dictionary, and the DLMF 30.16.3 index dictionary.

It must not create production Lean yet.

Registered prediction:

```yaml
P3035_1:
  prediction: the DLMF equation matches the current root function after
    splitDegree = 2*(K-1) and Lambda = DLMF lambda
  confidence: 0.95

P3035_2:
  prediction: the first formal friction is the independent representation
    of the infinite right continued fraction, not the finite left fraction
  confidence: 0.75
```

## STRONGEST ATTACK

DLMF 30.3.5 uses a two-sided continued fraction at an arbitrary parity-compatible split.

The project uses a left recurrence and a separately constructed `limUnder` right tail.

The names and coefficients matching is not enough. The local adapter must prove that the DLMF infinite right fraction is the same recessive branch as `mode4RightTailLimit`.

That proof may use the current contraction and square-summable uniqueness machinery.

It may not use the desired root equivalence itself.

If this branch identity cannot be proved independently, the mathematical mechanism remains known but the project-object crosswalk stays open.

## CODEX DIRECTIVE

```text
TARGET:
  GOAL058_G3_DLMF3035_EVEN_CHARACTERISTIC_SOURCE_CONTRACT

PIN:
  repo = /Users/emalam/GitHub/rh_lean_01_2026
  branch = rh_clean
  HEAD = origin/rh_clean =
    9eaa0f748f5e967fa7f6af71913cce6e66108da6

MODE:
  read-only source acquisition;
  one Markdown source contract;
  no production Lean;
  no Aristotle;
  no commit;
  no push;
  no Route/Bus/runtime edit.

SOURCE INPUTS:
  NIST DLMF:
    30.3.5
    30.3.7
    30.16.3

  Project:
    D0Mode4ClassicalCarrierFromFiniteLimit.lean
    D0Mode4ClassicalCarrierSchurCount.lean
    D0Mode4ClassicalCarrierHeadUpper.lean
    D0Mode4JacobiRootFunction.lean
    D0Mode4PSWFLegendreRecurrenceCrosswalk.lean
    D0Mode4PSWFLegendreCanonicalIdentification.lean
    D0Mode4SchurHermitianSymmetrization.lean

TASK 1 — EXACT SOURCE EQUATION:
  Transcribe DLMF 30.3.5 and 30.3.7 exactly.
  Define the independent project-unit contract for:
    mode4DLMF3035EvenCharacteristicEquation.

  Do not define it through mode4RootFunction.

TASK 2 — INDEX AND UNIT DICTIONARY:
  Prove in the report:
    DLMF order m = 0;
    splitDegree = 2*(K-1);
    project Lambda = DLMF lambda;
    differential energy chi = Lambda + G;
    internal carrier index p = classical degree 2*p.

TASK 3 — SOURCE SOLUTION SET:
  State the exact Lean theorem:
    mode4DLMF30163_3035_evenCharacteristicSolutions.

  Separate:
    DLMF 30.3.5 root-set fact;
    DLMF 30.16.3 finite-limit identity;
    local project adapter.

TASK 4 — RIGHT-BRANCH DISCRIMINATOR:
  Audit whether the existing project theorems prove that the DLMF recessive
  right fraction equals mode4RightTailLimit.

  Return exactly one:
    DLMF3035_RIGHT_BRANCH_CROSSWALK_READY
    DLMF3035_RIGHT_BRANCH_CROSSWALK_MISSING
    DLMF3035_RIGHT_BRANCH_CROSSWALK_CIRCULAR

MANDATORY PLANTS:
  P1 tautological source equation;
  P2 Lambda versus Lambda+G;
  P3 split degree 2*K versus 2*(K-1);
  P4 even versus odd solution family;
  P5 finite terminal-zero right tail;
  P6 endpoint-count circularity;
  P7 one-direction-only crosswalk.

OUTPUT:
  q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/
    GOAL058_G3_DLMF3035_EVEN_CHARACTERISTIC_SOURCE_CONTRACT_2026-08-14.md

SUCCESS:
  G3_DLMF3035_LITERAL_ROOT_CROSSWALK_SOURCE_MATERIALIZED

TYPED_STOPS:
  G3_DLMF3035_EXACT_SOURCE_EQUATION_UNAVAILABLE
  G3_DLMF3035_PROJECT_SHIFT_MISMATCH
  G3_DLMF3035_SPLIT_INDEX_MISMATCH
  G3_DLMF3035_INTERNAL_CARRIER_IDENTITY_MISSING
  G3_DLMF3035_RIGHT_BRANCH_CROSSWALK_MISSING
  G3_DLMF3035_SOURCE_THEOREM_CIRCULAR

STOP:
  after the one source contract.
```

## META CLOSEOUT

### What became smaller?

The old wall:

```text
literal Schur roots versus classical spectrum
```

is reduced to:

```text
formalize one exact DLMF solution-set theorem
+
prove one independent right-continued-fraction branch equality.
```

### What was killed?

- Treating separator inequalities alone as determinant nonsingularity.
- Treating DLMF 30.3.5 as merely suggestive rather than an exact root-set theorem.
- Defining the source equation through the project root function.
- Using endpoint counts to prove the root crosswalk.

### Current smallest named gap

```text
DLMF3035EvenCharacteristicSourceMaterialization
```

### Next cheapest decisive test

Audit the exact right-branch continued fraction against `mode4RightTailLimit`.

### Fate of prior prediction

```text
LITERAL_ROOT_CROSSWALK_MISSING:
  REPAIRED.

Mathematical mechanism:
  RECOVERED.

Lean source theorem:
  STILL OPEN.
```

### Memory entry

```yaml
iteration:
  target: Goal058_G3_literal_root_avoidance
  status: OPEN
  failed_strategy: treat_strict_endpoint_windows_as_self_proving_nonsingularity
  cognitive_operator_used: LITERATURE_BRIDGE
  new_gap_name: DLMF3035EvenCharacteristicSourceMaterialization
  invariant_learned: DLMF split degree, project Lambda, and recessive right branch must all match exactly
  forbidden_future_move: use_endpoint_counts_or_define_source_equation_by_rootFunction
  next_decisive_test: DLMF3035_right_branch_crosswalk_audit
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
