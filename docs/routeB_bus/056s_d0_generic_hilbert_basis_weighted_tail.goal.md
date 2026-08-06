# GOAL 056 / Phase 4J — generic Hilbert-basis weighted tail

```yaml
GOAL: 056
PHASE: 4J
NODE: D0HilbertBasisWeightedTail
STATUS: OPEN
OPERATIVE_CLASS: TRY_G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL
TRANSACTION: G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL
STOP: G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL_RECEIVER_MISSING
SUCCESS: G6_S2_D0_GENERIC_HILBERT_BASIS_PARSEVAL_AND_WEIGHTED_TAIL_PROVED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 10
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

The tenth batch in the same living Proshka phase chat selected the abstract
generic Hilbert-basis receiver under `CODEX_PLUS_PROSHKA` authority at pin
`0dea3fc20e0b0af45ed8aad50eed578a1a485b54`.

The exact newline-normalized verdict is materialized canonically and in the
bus mirror with SHA-256
`f0609ecd4e804bd09c2aa839fe0096c2dd1ac70d06ade0f6aab18da406dfcbfe`.
`Answer now` appeared and was not clicked.

This transaction closes only the abstract dependency

```text
complete complex Hilbert basis + summable dominating weight
  -> exact complement Parseval identity
  -> weighted finite-tail bound
```

It proves no `V_n_m` completeness, log-window transport, physical-frequency
corollary, source-specific energy control, selected projection-tail decay,
normalizer bound, compact-open convergence, or strict `SlotS2`.

## Source lock

```yaml
HEAD: 0dea3fc20e0b0af45ed8aad50eed578a1a485b54
REQUIRED_SHA256:
  D0PstarGalerkinResidualDecay.lean: 8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
  D0LogWindowMeasureTransport.lean: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
  D0FiniteProjectionReconstruction.lean: 4f19de8c695450691266171ce05b7343c5cbe16213eb71f3b40d2b119bdcaa8d
  D0KTrialStage1.lean: c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48
  INSIGHTS.md: 5a9046fea2c97392df1b02fc1d8c787f699d932e7520a5fe3ad580e411c79d6a
ON_MISMATCH: G6_S2_GENERIC_HILBERT_BASIS_TAIL_SOURCE_LOCK_MISMATCH
```

No production edit is permitted if HEAD differs from origin or any lock fails.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  scope: ABSTRACT
  scalar_field: Complex
  index_type: Integer
  ambient_object: arbitrary_inner_product_space_E
  basis: HilbertBasis_Z_Complex_E
  coefficient: inner_basis_f
  retained_set: exact_Finset_s
  partial_sum: sum_over_s_of_inner_basis_f_smul_basis
  residual: f_minus_exact_partial_sum
  complement: not_mem_s
  residual_measure: norm_squared
  coefficient_measure: norm_squared
  weighted_energy: tsum_w_times_coefficient_norm_squared
  outside_band_guard: one_le_a_times_w
  assumptions:
    - zero_le_a
    - pointwise_zero_le_w
    - outside_band_one_le_a_mul_w
    - weighted_energy_summable
```

Owned production file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0HilbertBasisWeightedTail.lean
```

Exact import:

```lean
import Mathlib.Analysis.InnerProductSpace.l2Space
```

There are zero project imports and no existing production importer is added.

## Exact production surface

Namespace: `Q3.RouteB.D0Pstar`.

Exactly one private theorem:

```lean
private theorem hilbertBasis_repr_sub_basisPartialSum_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : HilbertBasis ℤ ℂ E)
    (s : Finset ℤ)
    (f : E)
    (n : ℤ) :
    b.repr
        (f - ∑ j ∈ s, inner ℂ (b j) f • b j) n =
      if n ∈ s then 0 else inner ℂ (b n) f
```

Exactly two public theorems:

```lean
theorem norm_sub_basisPartialSum_sq_eq_tsum
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : HilbertBasis ℤ ℂ E)
    (s : Finset ℤ)
    (f : E) :
    ‖f - ∑ n ∈ s, inner ℂ (b n) f • b n‖ ^ 2 =
      ∑' n : ℤ,
        if n ∈ s then 0 else ‖inner ℂ (b n) f‖ ^ 2
```

```lean
theorem norm_sub_basisPartialSum_sq_le_weightedEnergy
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : HilbertBasis ℤ ℂ E)
    (s : Finset ℤ)
    (f : E)
    (a : ℝ)
    (w : ℤ → ℝ)
    (ha : 0 ≤ a)
    (hw : ∀ n, 0 ≤ w n)
    (hband : ∀ n, n ∉ s → 1 ≤ a * w n)
    (hsum :
      Summable
        (fun n : ℤ =>
          w n * ‖inner ℂ (b n) f‖ ^ 2)) :
    ‖f - ∑ n ∈ s, inner ℂ (b n) f • b n‖ ^ 2 ≤
      a * ∑' n : ℤ,
        w n * ‖inner ℂ (b n) f‖ ^ 2
```

Public delta: zero definitions, two theorems, one private theorem, zero private
definitions.

## Forbidden surface

The production file must not import any Q3 module or mention/instantiate any of:

```text
V_n_m
H_m
modeSet
gTrial_m
SelectedProjectionTailDecay
selectedPairIndex
```

No `n²` or physical-frequency corollary is permitted. No existing production
file imports this module. The sole authorized future first importer is
`D0LogWindowVNMCompletenessBridge.lean`.

## Load-bearing plants

```yaml
P056S_1_HILBERT_BASIS:
  mutation: replace_complete_HilbertBasis_by_incomplete_Orthonormal_family
  expected: G6_S2_GENERIC_TAIL_ORTHONORMAL_NOT_COMPLETE
P056S_2_INNER_ORIENTATION:
  mutation: inner_basis_f_to_inner_f_basis
  expected: G6_S2_GENERIC_TAIL_INNER_ORIENTATION_MISMATCH
P056S_3_COMPLEMENT_POLARITY:
  mutation: swap_inside_and_outside_terms
  expected: G6_S2_GENERIC_TAIL_COMPLEMENT_POLARITY_MISMATCH
P056S_4_SUMMABILITY:
  mutation: delete_weighted_energy_summability
  expected: G6_S2_GENERIC_TAIL_WEIGHTED_ENERGY_NONSUMMABLE
P056S_5_NONNEGATIVITY:
  mutation: delete_global_weight_nonnegativity
  expected: G6_S2_GENERIC_TAIL_WEIGHT_NEGATIVITY_MISMATCH
P056S_6_OUTSIDE_BAND:
  mutation: require_band_bound_inside_s
  expected: G6_S2_GENERIC_TAIL_OUTSIDE_BAND_MEMBERSHIP_MISMATCH
P056S_7_EXPONENT_TWO:
  mutation: replace_norm_squared_by_norm_or_fourth_power
  expected: G6_S2_GENERIC_TAIL_EXPONENT_TWO_MISMATCH
P056S_8_NO_SOURCE_SMUGGLING:
  mutation: add_V_n_m_or_SelectedProjectionTailDecay_claim
  expected: G6_S2_GENERIC_TAIL_SOURCE_SPECIFIC_CLAIM_SMUGGLED
```

The first seven plants are mathematical controls; the eighth is a strict
production-surface scan.

## Validation and boundary

Required validation: all five locks; direct Lean; dedicated module build; full
build; `scripts/q3_check.sh`; hole/taint/forbidden-import scan; exact public
surface; all eight plants with temporary files removed; exact standard axiom
triple for both public theorems; proof-DB import with all three declarations
indexed and both public theorems proven; all 67 orchestration tests; strict
Spine; observability source/stale counts with numeric `ZERO_COVERAGE`
reported separately; three SQLite integrity checks; `git diff --check`; exact
status.

The sole next node, not authorized in this transaction, is:

```text
G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE
```

Its future target is to construct for every `i : PairIndex` an exact
`b_i : HilbertBasis ℤ ℂ (H_m i)` with
`∀ n : ℤ, b_i n = V_n_m i n`.

Aristotle, project-specific tail claims, a new chat, Goal 055, Bus 010,
route promotion, PX, and RH claims are forbidden.
