# STATUS: OPEN — GENERIC HILBERT-BASIS COMPLEMENT PARSEVAL AND WEIGHTED-TAIL RECEIVER SELECTED

```yaml
PRIMARY: G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL_SELECTED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL
OPERATIVE_CLASS_COUNT: 1
CANDIDATE: A_GENERIC_HILBERT_BASIS_RECEIVER

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: 0dea3fc20e0b0af45ed8aad50eed578a1a485b54
  ORIGIN_HEAD_EQUALS_PIN: true
  COMMIT: "[MacOS][rh_clean][Docs] Research Goal 056 Fourier tail receiver"

HASH_AUDIT:
  D0PstarGalerkinResidualDecay:
    EXPECTED_SHA256: 8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
    TRACKED_CLOSEOUT_MATCH: true
    CONTENT_AT_PIN_MATCH: true
  D0LogWindowMeasureTransport:
    EXPECTED_SHA256: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
    TRACKED_CLOSEOUT_MATCH: true
    CONTENT_AT_PIN_MATCH: true
  D0FiniteProjectionReconstruction:
    EXPECTED_SHA256: 4f19de8c695450691266171ce05b7343c5cbe16213eb71f3b40d2b119bdcaa8d
    TRACKED_CLOSEOUT_MATCH: true
    CONTENT_AT_PIN_MATCH: true
  D0KTrialStage1:
    EXPECTED_SHA256: c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48
    PHASE4I_SOURCE_LOCK_LEDGER_MATCH: true
    CONTENT_AT_PIN_MATCH: true
  INSIGHTS:
    EXPECTED_SHA256: 5a9046fea2c97392df1b02fc1d8c787f699d932e7520a5fe3ad580e411c79d6a
    CURRENT_COMMIT_CONTENT_MATCH: true
    INDEPENDENT_BYTE_REHASH_BY_REVIEWER: false

PHASE4I:
  COMMIT: 492c459c1026baff95d69eb653f1cebd2482b125
  RESULT: G6_S2_D0_PROLATE_SOURCE_SAME_M_TRIAL_COHERENCE_LOCKED
  UNIVERSAL_TAIL_THEOREM_REACTIVATED: false
  PROJECTION_TAIL_DECAY: OPEN
  NORMALIZER_BOUNDEDNESS: OPEN

SCRATCH_PREFLIGHT:
  SHA256: 84202b3acfe401d3f36a4da531cc93c946b2e6ec46a1e789b8f673fd7cb9eb61
  REPORTED_DIRECT_LEAN: PASS
  SORRY_ADMIT_EXACT_QUERY: zero_reported
  JUDGE_RERAN_SCRATCH: false
  STATUS: STRONG_PREFLIGHT_NOT_PRODUCTION_EVIDENCE

TRANSACTION:
  NAME: G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0HilbertBasisWeightedTail.lean
  IMPORTS:
    - Mathlib.Analysis.InnerProductSpace.l2Space
  PROJECT_IMPORTS: 0
  NAMESPACE: Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  DEFINITIONS: 0
  THEOREMS: 2
  PRIVATE_THEOREMS: 1
  PRIVATE_DEFINITIONS: 0

PUBLIC_THEOREMS:
  - norm_sub_basisPartialSum_sq_eq_tsum
  - norm_sub_basisPartialSum_sq_le_weightedEnergy

PRIVATE_HELPER:
  - hilbertBasis_repr_sub_basisPartialSum_apply

STOP: G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL_RECEIVER_MISSING
SUCCESS: G6_S2_D0_GENERIC_HILBERT_BASIS_PARSEVAL_AND_WEIGHTED_TAIL_PROVED

PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: ABSTRACT_ONLY
COFINAL_FAMILY_PROGRESS: false
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 4

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE

MODESET_N2_COROLLARY_IN_THIS_TRANSACTION: forbidden
V_N_M_COMPLETENESS_CLAIMED: false
PHYSICAL_FOURIER_ENERGY_CONTROL_CLAIMED: false
SELECTED_PROJECTION_TAIL_DECAY_CLAIMED: false

PHASE_KEY_CHANGE: false
NEW_CHAT: false
ARISTOTLE_SUBMISSION: NONE

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Source and predecessor audit

The exact branch pin is verified as `0dea3fc20e0b0af45ed8aad50eed578a1a485b54`. The commit is research-only and records this exact fork: orthonormality is insufficient, a `HilbertBasis` or dense-span bridge is still required, and the generic weighted receiver has been separately Lean-preflighted.  `[ABSTRACT][PAPER]`

Phase 4I is closed exactly as reported. It adds same-(m) coherence for the consumed prolate trial and explicitly leaves projection-tail decay, normalizer boundedness, compact-open convergence, and `SlotS2` open. Its closeout records all six plants, the standard axiom triple, 67/67 tests, strict Spine, and the three SQLite checks.  `[COFINAL_FAMILY][LEAN]`

The Phase-4H file remains purely conditional:

```lean
SelectedProjectionTailDecay S
∧ SelectedTrialNormalizerBounded S
→ ‖selectedNormalizedGalerkinResidual S k‖ → 0.
```

It contains no Fourier completeness theorem or source-specific tail estimate.  `[COFINAL_FAMILY][LEAN]`

The exact production objects are also unchanged:

* `H_m i` is the quotient-valued (L^2(du/u)) carrier;
* `V_n_m i n` is the literal normalized logarithmic Fourier mode;
* `E_m_N i` is the span over the exact `modeSet i`;
* `P_m_N i` is the literal orthogonal projection onto that span.  `[ABSTRACT][LEAN]`

Phase 4C proves only:

```lean
V_n_m_orthonormal (i : PairIndex) :
  Orthonormal ℂ (V_n_m i)
```

with coefficient phase `r - n`, fixed by conjugate linearity in the first argument. It does not prove completeness.  `[ABSTRACT][LEAN]`

Phase 4D reconstructs the finite projection as:

```lean
(P_m_N i f : H_m i) =
  ∑ n ∈ modeSet i,
    inner ℂ (V_n_m i n) f • V_n_m i n.
```

That theorem identifies the finite projected vector; it still does not identify the complement with the infinite Fourier tail.  `[ABSTRACT][LEAN]`

The repository is pinned to Mathlib v4.26.0 at revision `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.  `[ABSTRACT][LEAN]`

### Hash qualification

The four production SHA-256 values are corroborated by tracked closeouts/source-lock ledgers and by the file contents fetched at the exact pin. The `INSIGHTS.md` value is a supplied live-disk hash; its current content matches the sole research diff at the pin, but the GitHub connector does not expose an independent SHA-256 byte rehash. No load-bearing mathematical conclusion depends on the `INSIGHTS.md` hash.

## 2. Scratch theorem audit

### 2.1 Exact complement Parseval identity

The proposed statement is mathematically correct:

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
        if n ∈ s then 0
        else ‖inner ℂ (b n) f‖ ^ 2 := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

After production compilation, the theorem becomes `[ABSTRACT][LEAN]`.

The coefficient orientation is exact. Pinned Mathlib states:

```lean
b.repr f n = inner ℂ (b n) f
```

and reconstructs (f) by the infinite sum of those coefficients times `b n`.   `[ABSTRACT][LEAN]`

The theorem does not follow from `Orthonormal` alone. The `HilbertBasis` object carries completeness through an isometric equivalence with (\ell^2); its source file explicitly distinguishes orthonormality from completeness and provides the dense-span and representation theorems.   `[ABSTRACT][LEAN]`

The complement polarity is correct:

```text
n ∈ s     → coordinate is cancelled;
n ∉ s     → original coordinate survives.
```

The exponent `2` is also exact. Both sides are squared Hilbert norms. Pinned Mathlib’s `lp.hasSum_norm` specializes the (\ell^p)-norm identity to (p=2), while `HilbertBasis.repr` is an isometry into (\ell^2).   `[ABSTRACT][LEAN]`

### 2.2 Generic weighted-tail receiver

The second statement is also correct:

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
        w n * ‖inner ℂ (b n) f‖ ^ 2 := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

The assumptions are neither decorative nor target-equivalent:

* `ha` and `hw` ensure nonnegativity, including on modes inside `s`, where the complement term is zero.
* `hband` supplies the pointwise comparison only outside the retained band.
* `hsum` prevents Lean’s nonsummable-`tsum` convention from silently turning the weighted energy into zero.
* The conclusion follows by pointwise comparison of two nonnegative summable series after the exact Parseval identity.

This is a genuine sufficient receiver. It does not assert that any current D0 energy is summable or controlled.

## 3. Candidate comparison

| Candidate                                              | Source truth                                       |                                             Actual wall reduction |                               Public cost | Hidden analytic work                                                            | Verdict                        |
| ------------------------------------------------------ | -------------------------------------------------- | ----------------------------------------------------------------: | ----------------------------------------: | ------------------------------------------------------------------------------- | ------------------------------ |
| **A. Generic Hilbert-basis receiver**                  | Unconditional abstract Hilbert-space theorem       |           Closes component 1 of the precommitted three-part split |                 2 theorems, 0 definitions | None                                                                            | **Selected**                   |
| **B. Add a `V_n_m` Hilbert-basis field**               | No source theorem currently supplies it            |                             Hides the completeness bridge as data | Structure migration plus a new assumption | The main missing source theorem                                                 | **Killed under C10/C09**       |
| **C. Full log-window unitary/completeness bridge now** | Mathematically plausible and source-faithful       |                         Would close the next source-specific edge |                     Larger theorem family | Quotient-valued (L^2) transport, surjectivity, endpoint and representative work | Deferred as the sole next node |
| **D. Honest stop**                                     | Honest only if A were a wrapper or had no consumer | Would leave an already-preflighted exact component unmaterialized |                                      Zero | None                                                                            | Rejected                       |

### Candidate B

Adding:

```lean
V_n_m_hilbertBasis :
  HilbertBasis ℤ ℂ (H_m i)
```

to source data would assume the missing bridge instead of proving it. It would also force every future source constructor to carry an analytic completeness certificate unrelated to the source packet’s current role. That is a C10 surrogate and a C09 post hoc strengthening.

### Candidate C

Candidate C is the real next source-specific mathematics. It must prove that the exact logarithmic transport carries the ordinary Fourier Hilbert basis to the literal quotient-valued `V_n_m` family. It is not selected now because it is broader than one bounded transaction and has not received the same Lean preflight as A.

### Why A is not unused scaffolding

The previous adjudication explicitly split the active wall into:

1. generic weighted Fourier-tail inequality;
2. physical-bandwidth law;
3. source-specific weighted-energy control.

A proves item 1 exactly and without a new premise on `ProlateCanonicalSourceData`. It removes the future need to repeat complement Parseval, series comparison, and weighted-tail algebra inside the source-specific bridge.

The result is **proof progress at `[ABSTRACT]` scope**, not progress toward the cofinal conclusion by itself.

## 4. Selected production transaction

Owned file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0HilbertBasisWeightedTail.lean
```

Exact import:

```lean
import Mathlib.Analysis.InnerProductSpace.l2Space
```

There are no project imports. This prevents the generic theorem from accidentally acquiring assumptions from the D0 chain.

Namespace:

```lean
namespace Q3.RouteB.D0Pstar
```

### Private helper

Exactly one private helper is permitted:

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
      if n ∈ s then 0 else inner ℂ (b n) f := by
  ...
```

This helper must remain private. It is the exact coordinate-cancellation fact and fixes the complex coefficient orientation.

### Proof route for theorem 1

1. Apply the isometry of `b.repr`.
2. Rewrite the coordinate of the residual using the private helper.
3. Use the (\ell^2) norm identity supplied by `lp.hasSum_norm`.
4. Normalize `ENNReal.toReal 2` to the natural exponent `2`.
5. Fold `HilbertBasis.repr_apply_apply`.

No orthogonal-projection theorem, source mode, `modeSet`, or D0 definition appears.

### Proof route for theorem 2

1. Rewrite the left side with `norm_sub_basisPartialSum_sq_eq_tsum`.
2. Prove pointwise:

   ```text
   complementTerm n
   ≤ a * weightedTerm n.
   ```
3. Inside `s`, use `ha`, `hw`, and nonnegativity.
4. Outside `s`, multiply `hband n` by the coefficient norm square.
5. Use `hsum` to establish summability and apply `Summable.tsum_le_tsum`.
6. Pull the constant `a` outside the `tsum`.

No source-specific choice of `a` or `w` is authorized here.

## 5. Generic Finset versus `modeSet`

The production theorems must remain generic over:

```lean
s : Finset ℤ.
```

A `modeSet` specialization does **not** belong in this transaction.

Three facts are still missing:

1. a literal Hilbert basis whose values are `V_n_m i n`;
2. a physical weight such as
   [
   \left|\frac{2\pi n}{L_m}\right|^{2r};
   ]
3. a source-proved summability or bound for the corresponding weighted energy.

Publishing a `modeSet`/`n²` corollary now would create a conditional wrapper with no current source consumer. Worse, the bare algebraic weight (n^2) is not yet identified with the source regularity norm; the physical factor contains (2\pi/L_m).

## 6. Import and consumer policy

This transaction modifies or creates only the owned file.

No existing production file should import it yet.

The only authorized first production importer is the future node:

```text
D0LogWindowVNMCompletenessBridge.lean
```

That importer must construct an exact object:

```lean
b_i : HilbertBasis ℤ ℂ (H_m i)
```

with:

```lean
∀ n : ℤ, b_i n = V_n_m i n.
```

If that completeness bridge is killed, this generic theorem remains valid library mathematics but may not be counted as Route-B cofinal progress.

## 7. K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  scope: ABSTRACT
  scalar_field: Complex
  index_type: Integer
  ambient_object: arbitrary_inner_product_space_E

  basis_object:
    HilbertBasis_Z_Complex_E

  retained_indices:
    exact_Finset_s

  coefficient_orientation:
    inner_basis_vector_then_f

  partial_sum:
    sum_over_exact_s_of_inner_basis_f_smul_basis

  complement:
    n_not_mem_s

  residual_measure:
    norm_squared

  coefficient_measure:
    norm_squared

  weighted_energy:
    tsum_w_n_mul_coefficient_norm_squared

  assumptions:
    - zero_le_a
    - pointwise_zero_le_w
    - outside_band_one_le_a_mul_w
    - weighted_energy_summable

  forbidden_instantiations:
    - V_n_m_is_HilbertBasis_without_bridge
    - modeSet_physical_tail_without_energy_supplier
    - SelectedProjectionTailDecay
    - target_dependent_choice_of_weight
```

## 8. Mandatory K6 plants

### `P056S-1 — Hilbert basis versus mere orthonormality`

Mutation:

```text
HilbertBasis
→ Orthonormal family.
```

Control: an incomplete orthonormal family in a Hilbert space with a nonzero orthogonal-complement vector. Its listed coefficients are all zero, while the residual norm is positive.

Required result:

```text
G6_S2_GENERIC_TAIL_ORTHONORMAL_NOT_COMPLETE
```

The detector must be mathematical, not merely “the `repr` API is absent.”

### `P056S-2 — complex coefficient orientation`

Mutation:

```text
inner ℂ (b n) f
→ inner ℂ f (b n).
```

Control in a one-dimensional temporary generic harness:

```text
f = I • b(*).
```

The correct coefficient is `I`; the reversed coefficient is `-I`. Retaining the sole mode gives zero residual only under the correct orientation.

Required result:

```text
G6_S2_GENERIC_TAIL_INNER_ORIENTATION_MISMATCH
```

### `P056S-3 — complement polarity`

Mutation:

```text
if n ∈ s then 0 else coefficient
→ if n ∈ s then coefficient else 0.
```

Control:

```text
f = b(n₀)
s = {n₀}.
```

The true residual is zero; the mutated right side is one.

Required result:

```text
G6_S2_GENERIC_TAIL_COMPLEMENT_POLARITY_MISMATCH
```

### `P056S-4 — summability is load-bearing`

Mutation:

```text
delete hsum.
```

Control: an (\ell^2) coefficient row whose chosen weighted energy is not summable. Under Lean’s nonsummable-`tsum` convention, the weighted `tsum` becomes zero and cannot bound a positive residual.

Required result:

```text
G6_S2_GENERIC_TAIL_WEIGHTED_ENERGY_NONSUMMABLE
```

### `P056S-5 — weight nonnegativity`

Mutation:

```text
delete hw.
```

Control: put the only nonzero coefficient inside `s`, take `a = 1`, and assign that mode a negative weight. The residual is zero while the proposed right side is negative.

Required result:

```text
G6_S2_GENERIC_TAIL_WEIGHT_NEGATIVITY_MISMATCH
```

### `P056S-6 — outside-band membership`

Mutation:

```text
hband : ∀ n ∈ s, 1 ≤ a * w n
```

instead of:

```text
hband : ∀ n ∉ s, 1 ≤ a * w n.
```

Control: retain mode (0), put all mass in mode (1), and set the outside weight to zero. The mutated band condition is satisfied but the residual is positive and the weighted energy vanishes.

Required result:

```text
G6_S2_GENERIC_TAIL_OUTSIDE_BAND_MEMBERSHIP_MISMATCH
```

### `P056S-7 — exponent two`

Mutation:

```text
coefficient norm squared
→ coefficient norm
```

or to the fourth power.

Scaling control:

```text
f = t • b(n₀), n₀ ∉ s.
```

The residual scales as (t^2); the mutated energy scales as (t) or (t^4).

Required result:

```text
G6_S2_GENERIC_TAIL_EXPONENT_TWO_MISMATCH
```

### `P056S-8 — premature D0 conclusion`

Mutation: add any theorem or field asserting one of:

```text
HilbertBasis ℤ ℂ (H_m i) with values V_n_m i;
SelectedProjectionTailDecay S;
physical N/log(m) tail decay;
uniform weighted source energy.
```

Required result:

```text
G6_S2_GENERIC_TAIL_SOURCE_SPECIFIC_CLAIM_SMUGGLED
```

The production file must contain none of:

```text
V_n_m
H_m
modeSet
gTrial_m
SelectedProjectionTailDecay
selectedPairIndex
```

except in comments explaining the nonclaim.

## 9. Validation gates

Required source and build gates:

```text
1. Verify HEAD = origin/rh_clean =
   0dea3fc20e0b0af45ed8aad50eed578a1a485b54.

2. Verify all five supplied source hashes before editing.

3. Direct Lean:
   lake env lean \
     q3.lean.aristotle/Q3/Proofs/RouteB/D0HilbertBasisWeightedTail.lean

4. Dedicated module build:
   lake build Q3.Proofs.RouteB.D0HilbertBasisWeightedTail

5. Full build:
   lake build

6. q3_check:
   bash scripts/q3_check.sh \
     q3.lean.aristotle/Q3/Proofs/RouteB/D0HilbertBasisWeightedTail.lean
```

Taint and dependency gates:

```text
- zero sorry
- zero admit
- zero exact?
- zero native_decide
- zero declared axiom
- zero opaque proof certificate
- zero Float
- zero import from aristotle_output
- zero import from ACTIVE/RequestProject
- exactly one import:
    Mathlib.Analysis.InnerProductSpace.l2Space
```

Surface gate:

```text
- zero public definitions
- exactly two public theorems
- exactly one private theorem
- no project-specific declaration
```

Axiom gates:

```lean
#print axioms
  Q3.RouteB.D0Pstar.norm_sub_basisPartialSum_sq_eq_tsum

#print axioms
  Q3.RouteB.D0Pstar.norm_sub_basisPartialSum_sq_le_weightedEnergy
```

Both must return exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Plant and infrastructure gates:

```text
- P056S-1 through P056S-8 all fire
- temporary plant files removed
- proof DB reimport
- all three declarations indexed
- both public theorems marked proven
- 67/67 orchestration tests
- python3 orchestrator/spine.py --strict --reason goal-close
- strict Spine PASS
- observability source count reported
- stale count = 0
- numeric ZERO_COVERAGE reported separately, never called PASS
- SQLite integrity_check:
    knowledge.db = ok
    aristotle_proofs.db = ok
    observability.db = ok
- git diff --check
- exact git status report
```

## 10. What succeeds and what remains open

On success, the project will have proved:

```text
For any complete complex Hilbert basis and any finite retained set,
the squared residual is exactly the coefficient mass outside that set.

A nonnegative summable weighted coefficient energy controls that residual
whenever the weight dominates one outside the retained set.
```

`[ABSTRACT][LEAN]`

It will **not** have proved:

```text
V_n_m is complete;
the log-window Fourier family is a Hilbert basis;
a derivative Parseval identity;
physical bandwidth tends to infinity;
uniform source regularity;
SelectedProjectionTailDecay;
normalized residual decay;
compact-open convergence;
SlotS2.
```

`[COFINAL_FAMILY][PAPER]`

The dependency edge removed is:

```text
complete basis + weighted energy
→ finite projection tail estimate.
```

The next source-specific edges remain:

```text
literal V_n_m completeness;
physical/coupled Fourier-energy control.
```

## 11. Strongest attack

> The theorem assumes a `HilbertBasis`, while completeness of `V_n_m` is exactly what is missing. Is this just moving the wall into a parameter?

It is moving the wall to its correct boundary, but not hiding it.

The selected theorem is quantified over an arbitrary already-complete basis and proves the exact functional-analytic consequence once. It does not add a basis field to `ProlateCanonicalSourceData`, does not assert that `V_n_m` is complete, and does not conclude the desired D0 tail.

The remaining source theorem becomes sharply typed:

```text
construct the exact HilbertBasis whose values are V_n_m.
```

That is a smaller and independently falsifiable obligation.

A second attack is:

> Arbitrary weights allow a tautological choice that encodes the desired residual.

Correct. Therefore no D0 weight is chosen in this transaction. A future physical-energy transaction must precommit its weight from the logarithmic derivative frequency (2\pi n/L_m), prove its summability independently, and prove the schedule/rate law without using the target tail.

## 12. Sole next node

Not authorized in this batch:

```text
G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE
```

Its exact mathematical target is:

```text
For every i : PairIndex, construct
  b_i : HilbertBasis ℤ ℂ (H_m i)
such that
  ∀ n : ℤ, b_i n = V_n_m i n.
```

The proof should proceed through the exact logarithmic-window (L^2) isometry and the fixed-interval Fourier Hilbert basis, not through a new source field.

Physical weighted-energy control is a later node, not a co-runner in this verdict.

## META CLOSEOUT

**What became smaller?**

The log-window tail wall is decomposed into:

```text
generic complement Parseval and weighted receiver — selected now;
literal V_n_m completeness — next;
physical/coupled energy control — later.
```

**What was killed?**

* orthonormality as a substitute for completeness;
* adding completeness as an unsupported source field;
* bundling the full log-window unitary and energy estimate into one transaction;
* a premature `modeSet`/`n²` wrapper;
* any claim that the generic receiver proves selected tail decay.

**What must not be tried again?**

Do not invoke Bessel inequality as exact residual Parseval. Do not infer `HilbertBasis` from `V_n_m_orthonormal`. Do not choose a weight after seeing the desired error.

**Current smallest named gap:**

```text
G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL_RECEIVER_MISSING
```

**Next cheapest decisive test:**

Compile the exact complement theorem and fire the incomplete-orthonormal-family plant before any source-specific completeness work.

**Prediction fate:**

```text
Phase4I prediction:
  source coherence alone would not prove projection-tail decay.
  CONFIRMED.

Phase4J preflight prediction:
  the generic Hilbert-basis receiver is locally executable.
  REPORTED LEAN-CONFIRMED; production validation pending.

Candidate-B prediction:
  a source-data Hilbert-basis field would hide the missing bridge.
  CONFIRMED BY TYPE AUDIT.

Candidate-C prediction:
  the next actual source wall is log-window completeness.
  CONFIRMED.
```

```yaml
iteration:
  target: selected_log_window_Fourier_tail_rate
  status: OPEN
  failed_strategy: use_orthonormality_as_if_it_were_complete_Parseval
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL_RECEIVER_MISSING
  invariant_learned: completeness_coefficient_orientation_and_outside_band_summability_are_load_bearing
  forbidden_future_move: add_V_n_m_completeness_as_source_data_or_choose_target_dependent_weights
  next_decisive_test: production_compile_plus_incomplete_orthonormal_family_plant
  progress_class: PROOF_PROGRESS
  route_score: 4
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL

TRANSACTION:
  G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

PHASE:
  phase_key_change: false
  reuse_existing_living_chat: true
  fresh_chat: forbidden

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 0dea3fc20e0b0af45ed8aad50eed578a1a485b54

  required_sha256:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean:
      8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
    q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean:
      59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
    q3.lean.aristotle/Q3/Proofs/RouteB/D0FiniteProjectionReconstruction.lean:
      4f19de8c695450691266171ce05b7343c5cbe16213eb71f3b40d2b119bdcaa8d
    q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean:
      c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48
    q3.lean.aristotle/docs/INSIGHTS.md:
      5a9046fea2c97392df1b02fc1d8c787f699d932e7520a5fe3ad580e411c79d6a

ON_SOURCE_MISMATCH:
  stop: G6_S2_GENERIC_HILBERT_BASIS_TAIL_SOURCE_LOCK_MISMATCH
  edit_files: false

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0HilbertBasisWeightedTail.lean

IMPORTS_EXACT:
  - Mathlib.Analysis.InnerProductSpace.l2Space

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 0
  theorems: 2
  private_theorems: 1
  private_definitions: 0

PRIVATE_HELPER: |
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
        if n ∈ s then 0 else inner ℂ (b n) f := by
    ...

PUBLIC_THEOREM_1: |
  theorem norm_sub_basisPartialSum_sq_eq_tsum
      {E : Type*}
      [NormedAddCommGroup E]
      [InnerProductSpace ℂ E]
      (b : HilbertBasis ℤ ℂ E)
      (s : Finset ℤ)
      (f : E) :
      ‖f - ∑ n ∈ s, inner ℂ (b n) f • b n‖ ^ 2 =
        ∑' n : ℤ,
          if n ∈ s then 0
          else ‖inner ℂ (b n) f‖ ^ 2 := by
    ...

PUBLIC_THEOREM_2: |
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
          w n * ‖inner ℂ (b n) f‖ ^ 2 := by
    ...

REQUIRED_PROOF_ROUTE:
  theorem_1:
    - rewrite the residual through HilbertBasis.repr
    - prove exact coordinate cancellation with the private helper
    - use lp.hasSum_norm at exponent two
    - use HilbertBasis.repr_apply_apply
    - preserve inner_basis_then_f orientation
    - preserve exact Finset complement

  theorem_2:
    - rewrite by theorem_1
    - establish pointwise nonnegative domination
    - use hband only for n outside s
    - use hsum before invoking any tsum comparison
    - apply Summable.tsum_le_tsum
    - factor out a
    - do not choose any project-specific weight

FORBIDDEN_IN_THIS_TRANSACTION:
  - import any Q3 RouteB production module
  - mention or instantiate V_n_m
  - mention or instantiate H_m
  - specialize to modeSet
  - add an n_squared or physical_frequency corollary
  - assert V_n_m completeness
  - assert SelectedProjectionTailDecay
  - assert physical bandwidth cofinality
  - assert source-specific weighted energy control
  - add any field to ProlateCanonicalSourceData
  - use Orthonormal where HilbertBasis is required
  - reverse complex inner-product orientation
  - omit summability or weight nonnegativity
  - choose a or w from the target residual
  - modify Phase4A through Phase4I production files
  - edit Q3.Main
  - edit Goal_055
  - create Bus_010
  - submit Aristotle
  - promote Route_B
  - make PX_or_RH_claim
  - open a fresh Proshka chat

K6_OBJECT_PRECOMMIT:
  scope: ABSTRACT
  index_type: Integer
  basis: HilbertBasis_Z_Complex_E
  coefficient: inner_basis_f
  retained_set: exact_Finset_s
  residual: f_minus_exact_partial_sum
  complement: not_mem_s
  power: two
  weighted_energy: w_times_coefficient_norm_squared
  outside_band_guard: one_le_a_times_w
  summability: explicit

MANDATORY_PLANTS:
  P056S_1_HILBERT_BASIS:
    mutation: replace_HilbertBasis_by_incomplete_Orthonormal_family
    expected: G6_S2_GENERIC_TAIL_ORTHONORMAL_NOT_COMPLETE

  P056S_2_INNER_ORIENTATION:
    mutation: replace_inner_basis_f_by_inner_f_basis
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
    mutation: require_band_bound_inside_s_instead_of_outside
    expected: G6_S2_GENERIC_TAIL_OUTSIDE_BAND_MEMBERSHIP_MISMATCH

  P056S_7_EXPONENT_TWO:
    mutation: replace_norm_squared_by_norm_or_fourth_power
    expected: G6_S2_GENERIC_TAIL_EXPONENT_TWO_MISMATCH

  P056S_8_NO_SOURCE_SMUGGLING:
    mutation: add_V_n_m_or_SelectedProjectionTailDecay_claim
    expected: G6_S2_GENERIC_TAIL_SOURCE_SPECIFIC_CLAIM_SMUGGLED

VALIDATION:
  - verify HEAD equals origin before editing
  - verify every required SHA-256
  - direct Lean on D0HilbertBasisWeightedTail.lean
  - dedicated module build
  - full build
  - q3_check PASS
  - taint and forbidden-import scan
  - exact public surface 0_definitions_2_theorems_1_private
  - fire P056S_1 through P056S_8
  - remove all temporary plant files
  - print axioms for both public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database reimport
  - require all three declarations indexed
  - require both public theorems marked proven
  - run all 67 orchestration tests
  - run python3 orchestrator/spine.py --strict --reason goal-close
  - require strict Spine PASS
  - report observability source count and stale count
  - report numeric ZERO_COVERAGE separately
  - run SQLite integrity_check on knowledge.db
  - run SQLite integrity_check on aristotle_proofs.db
  - run SQLite integrity_check on observability.db
  - require all three results equal ok
  - git diff --check
  - exact git status report

STOP:
  G6_S2_D0_GENERIC_HILBERT_BASIS_WEIGHTED_TAIL_RECEIVER_MISSING

SUCCESS:
  G6_S2_D0_GENERIC_HILBERT_BASIS_PARSEVAL_AND_WEIGHTED_TAIL_PROVED

FIRST_FUTURE_IMPORTER_POLICY:
  only_authorized_importer:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowVNMCompletenessBridge.lean
  current_transaction_adds_importer: false

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  name: G6_S2_D0_LOG_WINDOW_V_N_M_COMPLETENESS_BRIDGE
  target: |
    construct, for every i : PairIndex,
    b_i : HilbertBasis ℤ ℂ (H_m i)
    with ∀ n : ℤ, b_i n = V_n_m i n

AFTER_SUCCESS:
  generic_tail_receiver_proved: true
  V_n_m_completeness_proved: false
  physical_energy_control_proved: false
  selected_projection_tail_decay_proved: false
  normalized_residual_decay_proved: false
  compact_open_convergence_proved: false
  SlotS2_proved: false

ARISTOTLE:
  status: FORBIDDEN

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  Aristotle_submission: NONE
  route_promotion: false
  PX_RH_CLAIM: NOT_MADE
```
