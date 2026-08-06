# STATUS: CONDITIONAL — TWO-PREMISE SELECTED-RESIDUAL DECAY RECEIVER RATIFIED; UNCONDITIONAL DECAY REMAINS OPEN

```yaml
PRIMARY: G6_S2_D0_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_G6_S2_D0_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER
OPERATIVE_CLASS_COUNT: 1
CANDIDATE: A_TWO_PREMISE_CONDITIONAL_REPAIRED

PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: c9447e28beff8dc18d525b8ea991781f67f81733
  ORIGIN_HEAD_EQUALS_PIN: true
  COMMIT: "[MacOS][rh_clean][Docs] Research Goal 056 residual L2 decay"

AUTHORITY:
  MODE: CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM
  OWNER_ACTION_REQUIRED: false
  SAME_PHASE_KEY: true
  REUSE_CONVERSATION_ID: 6a72e750-dc60-83eb-946b-61d2073c232b
  FRESH_CHAT: false

SOURCE_AUDIT:
  PHASE4G_SHA256: 73fabe1675476e47228730c3bb4bce07a11c8d351d679c9937f51ef3e3fc9723
  PHASE4G_SHA_TRACKED_CLOSEOUT_MATCH: true
  OTHER_SUPPLIER_PATHS_CONTENT_CROSSCHECKED: true
  OTHER_SUPPLIER_SHA256_REHASHED_BY_REVIEWER: false
  SOURCE_MISMATCH_OBSERVED: false

UNCONDITIONAL_TARGET:
  TARGET: >-
    Tendsto
      (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖)
      atTop (𝓝 0)
  STATUS: NOT_ESTABLISHED_FROM_CURRENT_REGISTERED_SOURCE_DATA
  ROUTE_IMPOSSIBLE: false
  PRECISE_OPEN_INPUTS:
    - SELECTED_PROJECTION_TAIL_DECAY
    - SUFFICIENT_CONTROL_OF_SELECTED_TRIAL_NORMALIZATION

SELECTED_TRANSACTION:
  NAME: G6_S2_D0_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
  NAMESPACE: Q3.RouteB.D0Pstar

IMPORTS:
  SOLE_PROJECT_IMPORT:
    Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualCrosswalk
  DIRECT_MATHLIB_IMPORT:
    Mathlib.Analysis.Normed.Ring.Lemmas

PUBLIC_SURFACE:
  DEFINITIONS: 3
  THEOREMS: 2
  PRIVATE_PRODUCTION_DECLARATIONS: 0

PUBLIC_DEFINITIONS:
  - selectedUnnormalizedGalerkinResidualNorm
  - SelectedProjectionTailDecay
  - SelectedTrialNormalizerBounded

PUBLIC_THEOREMS:
  - norm_selectedNormalizedGalerkinResidual_eq
  - selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded

LOGICAL_STATUS:
  TWO_PREMISE_ROUTE: SUFFICIENT_NOT_NECESSARY
  FAILURE_OF_ONE_PREMISE_KILLS_TARGET: false
  WEIGHTED_PRODUCT_ALTERNATIVE_REMAINS_LOGICALLY_POSSIBLE: true

STOP: G6_S2_SELECTED_RESIDUAL_L2_DECAY_CONDITIONAL_RECEIVER_MISSING
SUCCESS: G6_S2_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER_PROVED
ANALYTIC_STOP_AFTER_SUCCESS: G6_S2_SELECTED_RESIDUAL_L2_DECAY_SUPPLIERS_OPEN

PHASE4B_CONTRACT_STATUS:
  STATUS: PROVED_UNCONDITIONALLY_BY_PHASE4G
  REOPENED: false
  MODIFIED: false

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  G6_S2_D0_SELECTED_PROJECTION_TAIL_DECAY_SUPPLIER

ARISTOTLE: FORBIDDEN
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 4

NONCLAIMS:
  SELECTED_RESIDUAL_L2_DECAY_PROVED: false
  COMPACT_OPEN_RESIDUAL_DECAY_PROVED: false
  STRICT_SLOT_S2_PROVED: false
  ROUTE_PROMOTION: false
  PX_RH_CLAIM: NOT_MADE
  RH_CLAIM: false

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
```

## SOURCE LOCK

The branch resolves exactly to `c9447e28beff8dc18d525b8ea991781f67f81733`, with the stated Phase-4H research commit.  `[ABSTRACT][PAPER]`

The Phase-4G closeout records production SHA-256 `73fabe…9723`, direct Lean, target build 7780, full build 7817, `q3_check`, all nine plants, standard-triple axioms, 67/67 tests, strict Spine, and all three SQLite integrity checks. It explicitly names normalized residual (L^2) decay as the sole next node and proves no such decay itself.  `[COFINAL_FAMILY][LEAN]`

The production source confirms that Phase 4G proves the literal object-first coordinate identity and discharges the Phase-4B contract only after justified (L^2\to L^1) integrability and almost-everywhere quotient algebra. It contains no residual norm estimate.  `[COFINAL_FAMILY][LEAN]`

The active control confirms that all non-PX/RH theorem-shape decisions are delegated to Codex and Proshka and that an unchanged six-field phase key retains the existing chat.  `[ABSTRACT][PAPER]`

The Arsenal mandate is accepted. The load-bearing cards here are:

* **C04:** a sequence of scalar norms is well-typed across changing carriers, but a fixed-space vector convergence theorem is not;
* **C09:** the existing `parent ∘ extract` schedule cannot be replaced after observing a favorable subsequence;
* **C10:** a scalar Mellin-coordinate defect cannot replace the literal (H_m)-residual;
* **C12:** the inverse projection normalizer is an unbounded multiplier until proved otherwise.   `[ABSTRACT][PAPER]`

## PRIMARY DECISION

[
\boxed{\text{Select Candidate A, with one logical repair.}}
]

The repair is important:

> `SelectedProjectionTailDecay` and `SelectedTrialNormalizerBounded` are **sufficient suppliers**, not logically necessary conditions for normalized residual decay.

An unbounded normalizer could still be overcome by a faster-decaying projection error. Therefore failure to prove one of the two premises does not kill the target. It kills only this clean factorized route.

### Candidate comparison

| Candidate                                       | Verdict                         | Reason                                                                                           |
| ----------------------------------------------- | ------------------------------- | ------------------------------------------------------------------------------------------------ |
| **A — two-premise conditional receiver**        | **Selected**                    | Gives an exact norm identity and separates projection approximation from normalization stability |
| **B — weighted-tail conditional**               | Rejected as current transaction | After the norm identity, its premise is essentially the desired conclusion under a new name      |
| **C — unconditional theorem from current data** | Not executable                  | No uniform selected-family tail theorem or normalizer lower bound is present                     |
| **D — reselect a subsequence**                  | Rejected                        | Changes the fixed family/quantifier and proves a weaker theorem                                  |

Candidate D is not a repair. The production family uses the literal index

```lean
S.canonical.parent (S.canonical.extract k)
```

and `CanonicalData` stores that parent and extraction as fixed data. Its cofinality assumption says only that the two numerical coordinates tend independently to infinity.  `[COFINAL_FAMILY][LEAN]`

Replacing `extract` or selecting a second subsequence would be a C09 post-outcome object change. Moreover, the requested target is a full `Tendsto` statement on the already-selected sequence, not existence of one favorable subsequence.

## WHY THE UNCONDITIONAL TARGET IS NOT CURRENTLY AVAILABLE

The exact residual is

[
s_k\bigl(P_{m_k,N_k}g_k-g_k\bigr),
\qquad
s_k=|P_{m_k,N_k}g_k|^{-1}.
]

The project proves only the pointwise nonzero condition

[
0<|P_{m_k,N_k}g_k|,
]

which permits defining the inverse normalizer. It supplies no eventual positive lower bound and therefore no boundedness of (s_k).  `[COFINAL_FAMILY][LEAN]`

The source package contains:

```text
pair
lambda_eq
eStar_memLp
trialNonzero
canonical
kTrial_eq
```

but no uniform projection-tail estimate, no norm floor, and no coupling theorem between (m_k), (N_k), and the changing source vector.  `[COFINAL_FAMILY][LEAN]`

The carrier itself varies:

[
H_{m_k}
=======

L^2!\left(
[\lambda_{m_k}^{-1},\lambda_{m_k}],du/u
\right).
]

So does the source vector and the projected subspace. A theorem about monotone projections of one fixed vector in one fixed Hilbert space cannot be applied merely because (N_k\to\infty). The current research commit records exactly this quantifier mismatch and reports no source-side uniform theorem repairing it.  `[COFINAL_FAMILY][PAPER]`

The precise stop is therefore:

```text
G6_S2_SELECTED_RESIDUAL_L2_DECAY_ANALYTIC_SUPPLIERS_MISSING
```

This is not a kill of the residual route.

## PRODUCTION FILE AND IMPORTS

```lean
import Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualCrosswalk
import Mathlib.Analysis.Normed.Ring.Lemmas

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar
```

The direct Mathlib import is intentional. The final conditional step uses the pinned theorem:

```lean
Filter.isBoundedUnder_le_mul_tendsto_zero
```

whose hypotheses are exactly a bounded norm multiplier and a factor tending to zero.  `[ABSTRACT][LEAN]`

## PUBLIC SURFACE

### 1. Literal unnormalized projection-error norm

```lean
noncomputable def selectedUnnormalizedGalerkinResidualNorm
    (S : ProlateCanonicalSourceData) (k : ℕ) : ℝ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  ‖(gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp‖
```

`[COFINAL_FAMILY][CONDITIONAL]`

This definition contains the actual projection and full object. It does not contain `rawFplus`, `Gwin`, the scalar coordinate defect, or the Mellin integral.

### 2. First analytic supplier contract

```lean
def SelectedProjectionTailDecay
    (S : ProlateCanonicalSourceData) : Prop :=
  Tendsto
    (selectedUnnormalizedGalerkinResidualNorm S)
    atTop
    (𝓝 0)
```

`[COFINAL_FAMILY][CONDITIONAL]`

This is a proposition, not a structure field, axiom, or theorem claimed to hold.

### 3. Second analytic supplier contract

```lean
def SelectedTrialNormalizerBounded
    (S : ProlateCanonicalSourceData) : Prop :=
  IsBoundedUnder (· ≤ ·) atTop
    (fun k : ℕ => ‖(selectedTrialNormalizer S k : ℂ)‖)
```

`[COFINAL_FAMILY][CONDITIONAL]`

This is also a proposition, not new canonical source data.

Its source-side meaning is:

```text
the inverse norms of the selected finite projections are eventually bounded.
```

Pointwise `TrialNonzero` is not enough.

### 4. Exact pointwise norm factorization

```lean
theorem norm_selectedNormalizedGalerkinResidual_eq
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    ‖selectedNormalizedGalerkinResidual S k‖ =
      ‖(selectedTrialNormalizer S k : ℂ)‖ *
        selectedUnnormalizedGalerkinResidualNorm S k := by
  simp [selectedNormalizedGalerkinResidual,
    selectedUnnormalizedGalerkinResidualNorm, norm_smul]
```

`[COFINAL_FAMILY][CONDITIONAL]`

After compilation: `[COFINAL_FAMILY][LEAN]`.

### 5. Conditional decay receiver

```lean
theorem
    selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded
    (S : ProlateCanonicalSourceData)
    (hTail : SelectedProjectionTailDecay S)
    (hNormalizer : SelectedTrialNormalizerBounded S) :
    Tendsto
      (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖)
      atTop
      (𝓝 0) := by
  ...
```

`[COFINAL_FAMILY][CONDITIONAL]`

After compilation: `[COFINAL_FAMILY][LEAN]`.

## EXACT PROOF SHAPE

The proof is only:

1. Rewrite every residual norm using `norm_selectedNormalizedGalerkinResidual_eq`.
2. Expose the scalar product
   [
   |s_k|,e_k,
   \qquad
   e_k:=|P_{m_k,N_k}g_k-g_k|.
   ]
3. Apply:

   ```lean
   Filter.isBoundedUnder_le_mul_tendsto_zero
   ```

   to `hNormalizer` and `hTail`.

No Fourier theorem, projection-density theorem, source-paper estimate, Mellin theorem, or compact-open argument is permitted in this transaction.

## K6 OBJECT PRECOMMIT

```yaml
K6_OBJECT_PRECOMMIT:
  selected_index:
    selectedPairIndex S k

  selected_index_expansion:
    "(S.canonical.parent (S.canonical.extract k)).1"

  varying_carrier:
    H_m (selectedPairIndex S k)

  projected_object:
    gTrial_m_N i h hLp

  full_object:
    gTrial_m i h hLp

  unnormalized_residual_order:
    projection_minus_full

  normalized_object:
    selectedNormalizedGalerkinResidual S k

  normalizer:
    selectedTrialNormalizer S k

  scalar_error:
    norm_of_literal_projection_minus_full_object

  target:
    norm_tendsto_zero_on_the_existing_full_selected_sequence

  forbidden_surrogates:
    - selectedGalerkinCoordinateDefect
    - selectedGalerkinResidualMellinCoordinate
    - rawFplus_minus_scaledGwin
    - a_new_subsequence
    - a_fixed_H_m_carrier
```

## K6 PLANTS

### `P056Q-1 — fixed-space API misuse`

Mutation:

```text
apply starProjection_tendsto_self directly to the selected family.
```

Required result:

```text
G6_S2_RESIDUAL_DECAY_FIXED_SPACE_API_MISMATCH
```

The carrier, vector, and submodule vary with (k). A fixed-space theorem must not typecheck as a proof of the selected cofinal result.

### `P056Q-2 — cofinality is not uniform approximation`

Control family:

```text
in ℓ², let P_N project onto the first N coordinates
and choose x_N = e_(N+1).
```

Then:

[
N\to\infty,
\qquad
|P_Nx_N-x_N|=1.
]

Required result:

```text
G6_S2_RESIDUAL_DECAY_COFINALITY_NOT_TAIL
```

This plant proves that increasing projection dimension alone does not control a simultaneously moving source vector.

### `P056Q-3 — pointwise nonzero is not bounded normalization`

Scalar control:

[
e_k=\frac1{k+1},
\qquad
a_k=k+1.
]

Then:

[
e_k\to0,
\qquad
a_k>0,
\qquad
a_ke_k=1.
]

Required result:

```text
G6_S2_RESIDUAL_DECAY_POINTWISE_NONZERO_NOT_BOUNDED
```

This prevents `TrialNonzero` from being consumed as a uniform normalizer theorem.

### `P056Q-4 — exact parent/extract path`

Mutation:

```text
parent (extract k)
→ parent k
```

or:

```text
parent (extract (k+1)).
```

Required result:

```text
G6_S2_RESIDUAL_DECAY_PARENT_EXTRACT_MISMATCH
```

The new definitions must unfold through the existing `selectedPairIndex`, never reconstruct the schedule independently.

### `P056Q-5 — scalar-coordinate surrogate`

Mutation:

```text
selectedUnnormalizedGalerkinResidualNorm
→ abs (selectedGalerkinCoordinateDefect S k 0)
```

Required result:

```text
G6_S2_RESIDUAL_DECAY_SCALAR_SURROGATE
```

An abstract two-dimensional control must accompany the scanner:

```text
a nonzero vector may lie in the kernel of one scalar functional.
```

Thus one coordinate can vanish while the Hilbert norm remains positive. **[C10]**

### `P056Q-6 — subtraction-order discriminator**

A norm alone cannot detect reversal because

[
|x-y|=|y-x|.
]

Therefore the plant must use the already-proved **signed** Phase-4G crosswalk:

```text
temporarily reverse projection - full to full - projection
in the underlying object;
the new norm identity may survive,
but D0PstarMuntzGalerkinResidualCrosswalkContract_proved must fail.
```

Required result:

```text
G6_S2_RESIDUAL_DECAY_ORDER_SIGNED_CROSSWALK_MISMATCH
```

A plant that checks only the norm theorem is invalid:

```text
G6_S2_RESIDUAL_DECAY_ORDER_PLANT_NOT_DISCRIMINATING
```

### `P056Q-7 — weighted-tail restatement**

Mutation:

```text
replace the two named Props by
Tendsto (fun k => normalizerNorm k * projectionError k) atTop (𝓝 0)
```

and advertise it as an analytic supplier.

Required result:

```text
G6_S2_RESIDUAL_DECAY_WEIGHTED_TAIL_RESTATEMENT
```

That statement may be logically exact after the factorization, but it does not decompose the missing mathematics.

## SUCCESS AND REMAINING STATUS

If the transaction succeeds, the following is proved:

```text
SelectedProjectionTailDecay S
+ SelectedTrialNormalizerBounded S
→ normalized selected residual norm tends to zero.
```

What remains open:

```text
SelectedProjectionTailDecay S
SelectedTrialNormalizerBounded S
```

Neither premise is inserted into `ProlateCanonicalSourceData`. Neither is declared as an axiom.

The Phase-4B contract stays unconditionally proved through Phase 4G and is not reopened.

## SOLE NEXT NODE

The sole next transaction is:

```text
G6_S2_D0_SELECTED_PROJECTION_TAIL_DECAY_SUPPLIER
```

with exact target:

```lean
theorem selectedProjectionTailDecay
    (S : ProlateCanonicalSourceData) :
    SelectedProjectionTailDecay S
```

It is **not authorized in this batch**.

This node is selected before the normalizer bound because it tests the substantive varying-carrier Fourier approximation mechanism. If it fails, the two-premise route is blocked at its main analytic input. The normalizer bound remains independently open.

Its required mathematics cannot be:

```text
N_k → ∞, therefore the Fourier projection error tends to zero.
```

It must supply a uniform selected-family estimate or transport the varying (H_m) spaces to a common carrier with enough uniform regularity.

## STRONGEST ATTACK

Candidate A is stronger than logically necessary.

It is possible that

[
|s_k|\to\infty
]

while

[
|P_kg_k-g_k|
]

decays fast enough that their product still tends to zero. Therefore:

```text
failure of SelectedTrialNormalizerBounded
does not kill normalized residual decay.
```

This verdict does not claim otherwise.

Candidate A is selected because it is the smallest **non-tautological, source-readable** sufficient decomposition currently supported by a compiled scratch. It separates two mathematically different risks:

```text
projection approximation;
inverse-normalizer blow-up.
```

If that decomposition later fails, two unselected re-representations remain:

1. **Relative projection-tail route**
   [
   \frac{|P_kg_k-g_k|}{|P_kg_k|}\to0.
   ]
   High exactness, low explanatory separation.

2. **Fixed-carrier logarithmic isometry route**
   transport every (H_{m_k}) to one reference (L^2)-space and prove a uniform Fourier/Sobolev tail theorem there.
   Higher cost, greater kill-power against the varying-carrier wall.

Neither is authorized now.

## META CLOSEOUT

**What became smaller?**

The blended target

```text
normalized Galerkin residual tends to zero
```

is reduced to:

```text
unnormalized selected projection tail tends to zero;
selected inverse projection normalizers remain bounded;
one proved product-limit receiver.
```

**What was killed?**

* unconditional decay from bare cofinality;
* direct use of fixed-space projection convergence;
* pointwise nonzero as uniform normalizer control;
* scalar Mellin-coordinate decay as an (H_m)-norm theorem;
* reselection of the canonical extraction;
* a norm-only subtraction-order plant.

**What must not be tried again?**

Do not infer a joint uniform approximation theorem from independent divergence of (m_k) and (N_k). Do not hide the target inside a weighted-tail premise and call the wall closed.

**Current smallest named gap:**

```text
G6_S2_D0_SELECTED_PROJECTION_TAIL_DECAY_SUPPLIER
```

**Next cheapest decisive test:**

Try to place the selected source trials, after exact log-window transport, in one common Sobolev/Fourier regularity class with constants uniform in (m). Failure to obtain a uniform constant is the discriminator between a genuine cofinal theorem and fixed-(m) density only.

**Prediction fate:**

```text
Phase-4G prediction:
  the next wall is residual norm decay, separate from coordinate identity.
  CONFIRMED.

Phase-4H research prediction:
  current source data does not contain a joint selected-family rate.
  CONFIRMED BY SOURCE AUDIT.

Candidate-A prediction:
  exact factorization plus bounded-times-zero closes in Lean.
  REPORTED LEAN-CONFIRMED; production validation pending.

Candidate-C prediction:
  fixed-space Fourier density is insufficient.
  CONFIRMED BY QUANTIFIER/CARRIER AUDIT.
```

```yaml
iteration:
  target: selected_normalized_Galerkin_residual_L2_decay
  status: OPEN
  failed_strategy: infer_selected_joint_decay_from_fixed_space_projection_density
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G6_S2_D0_SELECTED_PROJECTION_TAIL_DECAY_SUPPLIER
  invariant_learned: projection carrier, source vector, parent_extract path, and inverse normalizer must remain explicit
  forbidden_future_move: replace_the_literal_residual_by_a_scalar_coordinate_or_reselect_the_sequence
  next_decisive_test: uniform_log_window_Fourier_tail_on_the_selected_source_family
  progress_class: REPRESENTATION_PROGRESS
  route_score: 4
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_G6_S2_D0_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER

TRANSACTION:
  G6_S2_D0_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

PHASE:
  phase_key_change: false
  reuse_conversation_id: 6a72e750-dc60-83eb-946b-61d2073c232b
  fresh_chat: forbidden

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: c9447e28beff8dc18d525b8ea991781f67f81733

  required_sha256:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualCrosswalk.lean:
      73fabe1675476e47228730c3bb4bce07a11c8d351d679c9937f51ef3e3fc9723
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean:
      1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff
    q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage3.lean:
      924027a3dd9b95e75c776db552ad37779ed8dd75a7924d744a39cb1a613ebdfa
    q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean:
      3004f7551bcf187bb21d0de19a1e6c90f9836c749d00836ed8543389e54423b1
    q3.lean.aristotle/Q3/Proofs/RouteB/D0CanonicalApproximation.lean:
      60409208d26aeae7b4974150bd66ad42da83f09a223f41196dbde7abd3157695

ON_SOURCE_MISMATCH:
  stop: G6_S2_RESIDUAL_DECAY_SOURCE_LOCK_MISMATCH
  edit_files: false

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean

IMPORTS_EXACT:
  project:
    - Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualCrosswalk
  mathlib:
    - Mathlib.Analysis.Normed.Ring.Lemmas

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 3
  theorems: 2
  private_production_declarations: 0

PUBLIC_DEFINITION_1: |
  noncomputable def selectedUnnormalizedGalerkinResidualNorm
      (S : ProlateCanonicalSourceData) (k : ℕ) : ℝ :=
    let i := selectedPairIndex S k
    let h := selectedProlateTrial S k
    let hLp := S.source.eStar_memLp i
    ‖(gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp‖

PUBLIC_DEFINITION_2: |
  def SelectedProjectionTailDecay
      (S : ProlateCanonicalSourceData) : Prop :=
    Tendsto
      (selectedUnnormalizedGalerkinResidualNorm S)
      atTop
      (𝓝 0)

PUBLIC_DEFINITION_3: |
  def SelectedTrialNormalizerBounded
      (S : ProlateCanonicalSourceData) : Prop :=
    IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => ‖(selectedTrialNormalizer S k : ℂ)‖)

PUBLIC_THEOREM_1: |
  theorem norm_selectedNormalizedGalerkinResidual_eq
      (S : ProlateCanonicalSourceData) (k : ℕ) :
      ‖selectedNormalizedGalerkinResidual S k‖ =
        ‖(selectedTrialNormalizer S k : ℂ)‖ *
          selectedUnnormalizedGalerkinResidualNorm S k := by
    ...

PUBLIC_THEOREM_2: |
  theorem
      selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded
      (S : ProlateCanonicalSourceData)
      (hTail : SelectedProjectionTailDecay S)
      (hNormalizer : SelectedTrialNormalizerBounded S) :
      Tendsto
        (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖)
        atTop
        (𝓝 0) := by
    ...

REQUIRED_PROOF_ROUTE:
  - prove theorem_1 only by unfolding the literal object and norm_smul
  - rewrite the target sequence pointwise using theorem_1
  - apply Filter.isBoundedUnder_le_mul_tendsto_zero
  - do not invoke fixed-space projection convergence
  - do not prove either analytic premise
  - do not import or use a scalar Mellin-coordinate estimate

K6_OBJECT_PRECOMMIT:
  index: selectedPairIndex_S_k
  index_expansion: parent_extract_k
  carrier: H_m_of_selectedPairIndex
  projected_object: gTrial_m_N
  full_object: gTrial_m
  residual_order: projection_minus_full
  normalizer: selectedTrialNormalizer
  error: norm_of_literal_projection_minus_full
  conclusion: full_sequence_norm_tendsto_zero

MANDATORY_PLANTS:
  P056Q_1_FIXED_SPACE_API:
    expected: G6_S2_RESIDUAL_DECAY_FIXED_SPACE_API_MISMATCH

  P056Q_2_COFINALITY_NOT_TAIL:
    control: l2_basis_vector_just_beyond_each_projection
    expected: G6_S2_RESIDUAL_DECAY_COFINALITY_NOT_TAIL

  P056Q_3_NORMALIZER:
    control: a_k_eq_k_plus_one_error_eq_inverse_k_plus_one
    expected: G6_S2_RESIDUAL_DECAY_POINTWISE_NONZERO_NOT_BOUNDED

  P056Q_4_PARENT_EXTRACT:
    mutation: parent_k_or_shifted_extract
    expected: G6_S2_RESIDUAL_DECAY_PARENT_EXTRACT_MISMATCH

  P056Q_5_SCALAR_SURROGATE:
    mutation: replace_H_m_norm_by_one_coordinate
    expected: G6_S2_RESIDUAL_DECAY_SCALAR_SURROGATE

  P056Q_6_ORDER:
    mutation: reverse_underlying_residual_order
    discriminator: Phase4G_signed_crosswalk_must_fail
    expected: G6_S2_RESIDUAL_DECAY_ORDER_SIGNED_CROSSWALK_MISMATCH
    invalid_detector: norm_identity_only

  P056Q_7_WEIGHTED_RESTATEMENT:
    mutation: replace_two_props_by_target_product_tendsto
    expected: G6_S2_RESIDUAL_DECAY_WEIGHTED_TAIL_RESTATEMENT

VALIDATION:
  - verify HEAD equals origin before editing
  - verify all required SHA-256 locks
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
  - dedicated target build
  - full build
  - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
  - scan for sorry admit exact? native_decide axiom opaque Float
  - scan for imports from aristotle_output or ACTIVE RequestProject
  - require exactly three public definitions
  - require exactly two public theorems
  - require zero private production declarations
  - fire P056Q_1 through P056Q_7
  - remove every temporary plant file
  - print axioms for both public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database reimport
  - require all five declarations indexed and both theorems marked proven
  - run all 67 orchestration tests
  - python3 orchestrator/spine.py --strict --reason goal-close
  - require strict Spine PASS
  - run SQLite integrity_check on knowledge.db
  - run SQLite integrity_check on aristotle_proofs.db
  - run SQLite integrity_check on observability.db
  - require all three equal ok
  - report observability source count, stale count, and numeric ZERO_COVERAGE separately
  - git diff --check
  - exact git status report

STOP:
  G6_S2_SELECTED_RESIDUAL_L2_DECAY_CONDITIONAL_RECEIVER_MISSING

SUCCESS:
  G6_S2_SELECTED_RESIDUAL_L2_DECAY_TWO_PREMISE_RECEIVER_PROVED

AFTER_SUCCESS:
  unconditional_decay_proved: false
  Phase4B_contract_reopened: false
  analytic_open_inputs:
    - SelectedProjectionTailDecay
    - SelectedTrialNormalizerBounded

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  name: G6_S2_D0_SELECTED_PROJECTION_TAIL_DECAY_SUPPLIER
  target: |
    theorem selectedProjectionTailDecay
        (S : ProlateCanonicalSourceData) :
        SelectedProjectionTailDecay S

ARISTOTLE:
  status: FORBIDDEN

FORBIDDEN:
  - add either Prop as a field of ProlateCanonicalSourceData
  - declare either Prop as an axiom
  - claim unconditional residual decay
  - use fixed-space projection density on the varying selected family
  - infer normalizer boundedness from TrialNonzero
  - replace the literal H_m residual by a scalar coordinate
  - reverse projection_minus_full
  - change parent or extract
  - select a new subsequence
  - prove compact-open residual decay
  - prove strict SlotS2
  - edit Q3.Main
  - edit Goal_055
  - create Bus_010
  - submit Aristotle
  - promote Route_B
  - make PX_or_RH_claim
  - open a fresh Proshka chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  Aristotle_submission: NONE
  route_promotion: false
  PX_RH_CLAIM: NOT_MADE
```
