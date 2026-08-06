# STATUS: OPEN — CURRENT UNIVERSAL TAIL THEOREM SHAPE KILLED; SAME-(m) SOURCE REPAIR SELECTED

```yaml
PRIMARY: G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_REPAIR_SELECTED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_REPAIR
OPERATIVE_CLASS_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: e2ef5f0741c15b644514eade8332d35ed5629666
  ORIGIN_HEAD_EQUALS_PIN: true
  COMMIT: "[MacOS][rh_clean][Docs] Research Goal 056 projection tail supplier"

HASH_AUDIT:
  PHASE4H_PRODUCTION_SHA256:
    expected: 8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
    tracked_closeout_match: true
  CORE_056Q_SUPPLIER_HASHES:
    tracked_goal_match: true
  STAGE2_AND_PAPER_HASHES:
    tracked_source_lock_match: true
  ALL_PATH_CONTENTS_AT_PIN_FETCHED: true
  FRESH_LOCAL_BYTE_REHASH_BY_REVIEWER: false
  VERIFICATION_CLASS: PIN_PLUS_TRACKED_SHA_LEDGER_PLUS_CONTENT_CROSSCHECK
  HASH_MISMATCH_OBSERVED: false

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_USED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C12_BOUNDED_POTENTIAL_EXCLUSION

CURRENT_UNIVERSAL_TARGET:
  theorem: selectedProjectionTailDecay
  quantifier: "forall S : ProlateCanonicalSourceData"
  fate: KILLED_AS_CURRENT_SOURCE_UNSUPPORTED_THEOREM_SHAPE
  mathematical_negation_proved: false
  classification: OVERSTRONG_AND_UNDERDETERMINED
  fixed_space_proof_route: invalid
  recoverable_after_repairs: conditional

SOURCE_INTERFACE:
  CURRENT_FIELD: "pair : PairIndex -> ProlatePair"
  SOURCE_FAITHFULNESS_BUG: true
  ABSTRACT_TEST_FAMILY_LEGALITY: true
  CANONICAL_SOURCE_PACKAGE_LEGALITY: false
  MINIMAL_REPAIR:
    exact_same_m_equality_of_consumed_prolateCombination: required
    pair_or_certificates_full_equality: not_required
    source_trial_N_independence: required
    projection_and_nonzero_certificates_may_depend_on_N: true

SELECTED_TRANSACTION:
  NAME: G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_REPAIR
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
  NAMESPACE: Q3.RouteB.D0Pstar
  NEW_FILES: 0
  MODIFIED_FILES: 1
  STRUCTURE_FIELDS_ADDED: 1
  PUBLIC_THEOREMS_ADDED: 1
  PUBLIC_DEFINITIONS_ADDED: 0
  PRIVATE_DECLARATIONS_ADDED: 0

STOP: G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_MISSING
SUCCESS: G6_S2_D0_PROLATE_SOURCE_SAME_M_TRIAL_COHERENCE_LOCKED

ANALYTIC_STATUS_AFTER_SUCCESS:
  SelectedProjectionTailDecay: OPEN
  SelectedTrialNormalizerBounded: OPEN
  unconditional_normalized_residual_decay: OPEN
  Phase4G_crosswalk_contract: PROVED_UNCONDITIONALLY
  Phase4H_two_premise_receiver: PROVED
  compact_open_decay: OPEN
  strict_SlotS2: OPEN

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  G6_S2_D0_SELECTED_LOG_WINDOW_FOURIER_TAIL_RATE

PHASE:
  PHASE_KEY_CHANGE: false
  SAME_LIVING_CHAT: true
  FRESH_CHAT: false

PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 1. Source-lock and Phase-4H audit

The attached ninth-batch request fixes the exact pin, source hashes, Candidate A–D fork, and the prohibition against silently replacing the projection-tail target with another premise. 

The branch resolves exactly to `e2ef5f0741c15b644514eade8332d35ed5629666`. The commit modifies the research ledger only and records the same diagnosis: the current source may vary with (N), independent cofinality does not control (N/\log m), and the paper uses an iterated rather than arbitrary joint limit.  `[ABSTRACT][PAPER]`

Phase 4H is materialized exactly as represented in the request. Its production module defines:

```text
SelectedProjectionTailDecay S
SelectedTrialNormalizerBounded S
```

as separate propositions, proves the exact norm factorization, and proves only bounded-times-zero decay. It does not establish either supplier.  `[COFINAL_FAMILY][LEAN]`

The tracked Phase-4H closeout records production SHA-256 `8fe089…f62f63`, direct Lean, target/full builds, `q3_check`, seven fired plants, the standard axiom triple, proof-DB import, 67/67 tests, strict Spine, and three valid SQLite databases.  `[COFINAL_FAMILY][LEAN]`

The supplied core source SHA locks for `D0ProlateKTrialSource` and `D0CanonicalApproximation` are reproduced in the tracked 056q goal.  The Stage-2 and paper hashes are independently recorded by the earlier concrete-trial source audit.  The connector exposes file contents and Git blob SHAs rather than a local byte-stream SHA-256 command, so this verdict claims ledger-and-content verification, not a fresh independent byte rehash of every listed file.

## 2. The source packet has a real type-level provenance bug

Current production Lean says:

```lean
structure ProlateKTrialSourceData where
  pair : PairIndex → ProlatePair
  lambda_eq : ∀ i, (pair i).pw.lambda = lambda_m i
  ...
```

`PairIndex` contains both `m` and `N`. Consequently, two indices with equal `m` and different `N` may carry different `ProlatePair` values and therefore different `prolateCombination` source functions. The only current lock is equality of their bandwidths.  `[ABSTRACT][LEAN]`

The source object is not (h_{m,N}). It is the fixed function

[
h_m=h_{\lambda_m},
\qquad
\lambda_m=\sqrt m,
]

constructed from the (h_{0,\lambda}) and (h_{4,\lambda}) modes; (N) enters only later through the finite projection (P_{m,N}). The source-lock audit gives the exact formula and explicitly distinguishes this mathematically fixed object from the current free Lean argument.  `[ABSTRACT][PAPER]`

Therefore:

```text
pair : PairIndex → ProlatePair
```

is acceptable as a broad abstract test-family interface, but it is not acceptable as the canonical source-faithful Route-B package without an (N)-coherence invariant.

The filename, module commentary, and downstream role all call this a source-faithful prolate package. In that role, the freedom is a bug, not intentional generality.

## 3. Precise fate of the universal theorem

The theorem

```lean
theorem selectedProjectionTailDecay
    (S : ProlateCanonicalSourceData) :
    SelectedProjectionTailDecay S
```

is **not derivable from the current registered data**.

I am not claiming its logical negation for every inhabitant of the current structure. No complete source-faithful counterexample inhabitant satisfying every `ProlatePair`, `MemLp`, `TrialNonzero`, and central-index field has been constructed. The accurate classification is:

```text
OVERSTRONG_AND_UNDERDETERMINED
```

The theorem shape is killed as the current production target, not refuted as an abstract proposition.

Two independent defects cause this.

### Defect 1 — the vector may vary with (N)

Fixed-vector Fourier completeness cannot apply when changing the cutoff can also change the vector being projected. Equality of `lambda_m` does not identify the source trial. This is a **C04** category error: same carrier scale is not same mathematical object.

### Defect 2 — independent cofinality does not control physical bandwidth

Production defines:

[
L_m=\log m,
\qquad
\operatorname{modeSet}(m,N)={-N,\ldots,N},
]

and `PairCofinal` requires only:

[
m_k\to\infty,
\qquad
N_k\to\infty.
]

`[COFINAL_FAMILY][LEAN]`

Under the exact logarithmic coordinate used by the Fourier modes, retained physical frequency is proportional to

[
\omega_k
========

\frac{2\pi(N_k+1)}{L_{m_k}}.
]

The sequence

[
m_k=2^{(k+1)^2},
\qquad
N_k=k+1
]

has both coordinates tending to infinity, while

[
\frac{N_k}{\log m_k}
====================

\frac{1}{(k+1)\log 2}
\longrightarrow0.
]

Thus `PairCofinal` does not even force the retained physical bandwidth to diverge.

The exact production modes themselves carry the factor (2\pi n/L_m), confirming that (N/L_m), not bare (N), is the relevant scale.  `[ABSTRACT][LEAN]`

## 4. The paper does not supply the missing joint theorem

The primary paper states the proposed limit in two stages:

1. **For fixed (\lambda)**, take (N\to\infty) to obtain the continuum ground-state object.
2. Then take **(\lambda\to\infty)** and seek convergence, after normalization, to (\Xi).

`[COFINAL_FAMILY][PAPER]`

Section 8 then identifies two essential missing steps: simple-evenness of the lowest Weil eigenvector and sufficiently accurate approximation of that eigenvector by the prolate trial.  `[COFINAL_FAMILY][PAPER]`

That source does not prove convergence on every arbitrary independently cofinal path ((m_k,N_k)).

## 5. Current source data has no uniform Fourier-rate supplier

`ProlatePair` stores support, integrability, normalization, parity, two center identities, and the formal bandwidth. It explicitly does **not** assert an operator domain, an eigenfunction theorem, or spectral existence.  `[ABSTRACT][LEAN]`

The only current Lipschitz result is conditional on externally supplied constants `K0` and `K4`. The theorem neither stores these constants in `ProlateKTrialSourceData` nor makes them uniform in (m).  `[ABSTRACT][LEAN]`

No current field or theorem supplies:

```text
a uniform transported Sobolev norm;
a weighted Fourier-energy bound;
an E_star summation regularity estimate uniform in m;
a coupling between N and log m.
```

Candidate C or a real Candidate-B rate theorem is therefore still required after source coherence is repaired.

## 6. Exact selected repair

The smallest source-faithful invariant is equality of the **consumed trial function**, not equality of every proof field in the entire `ProlatePair`.

Modify `ProlateKTrialSourceData` by adding exactly:

```lean
structure ProlateKTrialSourceData where
  pair : PairIndex → ProlatePair

  prolateCombination_eq_of_same_m :
    ∀ i j : PairIndex, i.m = j.m →
      prolateCombination (pair i) =
        prolateCombination (pair j)

  lambda_eq : ∀ i, (pair i).pw.lambda = lambda_m i

  eStar_memLp :
    ∀ i,
      MemLp (E_star (prolateCombination (pair i))) 2
        (dStar.restrict (I_m i))

  trialNonzero :
    ∀ i,
      TrialNonzero i
        (prolateCombination (pair i))
        (eStar_memLp i)
```

`[ABSTRACT][CONDITIONAL]`

This is not a projection-tail assumption. It is the exact source identity already imposed by the paper: fixing (m) fixes (h_m), while the projection certificate and projected nonvanishing may still depend on (N).

Add one public derived theorem:

```lean
@[simp] theorem ProlateKTrialSourceData.E_star_eq_of_same_m
    (S : ProlateKTrialSourceData)
    (i j : PairIndex)
    (hm : i.m = j.m) :
    E_star (prolateCombination (S.pair i)) =
      E_star (prolateCombination (S.pair j)) := by
  rw [S.prolateCombination_eq_of_same_m i j hm]
```

After successful Lean validation, both claims are `[ABSTRACT][LEAN]`.

Do **not** add:

```lean
SelectedProjectionTailDecay S
```

as a structure field. That would restate the desired theorem and violate C10.

### Why this is smaller than an (m)-indexed structure redesign

An (m)-indexed field would also be source-faithful, but it would rename the existing `pair` projection and widen the API migration. The exact same-(m) equality of the consumed function makes the needed illegal states unavailable to the route while preserving every existing downstream term.

This is the `MINIMAL_LEMMA` repair.

## 7. Atomic migration surface

Repository search finds no production constructor of the form:

```lean
ProlateKTrialSourceData where
```

outside the structure declaration itself.  `[ABSTRACT][PAPER]`

The only direct production importer of `D0ProlateKTrialSource` is:

```text
D0PstarMuntzCenteredCoordinateLock.lean
```

`[ABSTRACT][PAPER]`

Its downstream chain includes:

```text
D0PstarMuntzGalerkinResidualContract
D0PstarProjectedMellinCoordinate
D0PstarFullMellinGwinCrosswalk
D0PstarMuntzGalerkinResidualCrosswalk
D0PstarGalerkinResidualDecay
```

No downstream theorem statement needs to change. They must all be recompiled atomically to confirm that the new source field has not created an implicit object switch.

Future constructors must now supply the coherence proof.

## 8. A–D comparison

| Candidate                              | Mathematical truth                                     | Source fidelity | Wall reduction                                                            | Cost   | Main risk                                                                                      | Verdict                                        |
| -------------------------------------- | ------------------------------------------------------ | --------------- | ------------------------------------------------------------------------- | ------ | ---------------------------------------------------------------------------------------------- | ---------------------------------------------- |
| **A — source (N)-coherence first**     | Exact source requirement                               | Highest         | Removes the first invalid quantifier seam                                 | Low    | Mistaking source repair for tail decay                                                         | **SELECTED**                                   |
| **B — coupled uniform Fourier rate**   | Valid if stated through an independent weighted energy | High            | Would genuinely imply projection-tail decay                               | High   | Hiding the target inside the “rate” premise                                                    | Next theorem-shape, not authorized             |
| **C — constructive diagonal schedule** | Mathematically legitimate before family freezing       | Conditional     | Can obtain an existential good schedule without uniform-in-(m) regularity | Medium | Changes `forall S` to existence and must also preserve central nonzero, normalization, and H2b | Legal new constructor route only; not selected |
| **D — source stop only**               | Honest diagnosis                                       | High            | No production edge                                                        | Lowest | Leaves a repairable type bug in place                                                          | Rejected because A is executable               |

### Candidate C ruling

A diagonal constructor is not mathematically forbidden.

For each fixed (m), Fourier completeness could choose an (N(m)) with projection error below a prescribed tolerance, then impose (N(m)\ge m) to obtain cofinality. This would prove existence of a good schedule.

But it would not prove the current theorem for every already-supplied `S`. It is legal only:

```text
before CanonicalData.parent and extract are frozen;
as an explicitly named constructor theorem;
with central-nonzero, TrialNonzero, normalization, H2b, and same-family
obligations retained.
```

Changing the current selected path after seeing the projection errors would violate C09.

## 9. The weakest real coupling law

For any fixed-order Sobolev/Fourier-energy route, independent `PairCofinal` must be strengthened.

Let:

[
i_k=\operatorname{selectedPairIndex}(S,k),
\qquad
L_k=L_m(i_k),
\qquad
N_k=i_k.N,
]

and define physical cutoff:

[
\omega_k
========

\frac{2\pi(N_k+1)}{L_k}.
]

The weakest simple standalone schedule law for a **uniform fixed-order regularity bound** is:

[
\boxed{
\omega_k\longrightarrow\infty.
}
]

Equivalently:

[
\frac{N_k}{\log m_k}\longrightarrow\infty
]

up to fixed constants and the harmless (+1).

The more general and genuinely weakest coupled rate is:

[
\boxed{
\omega_k^{-2r},\mathcal E_r(S,k)
\longrightarrow0,
}
]

where

[
\mathcal E_r(S,k)
=================

\sum_{n\in\mathbb Z}
\left|
\frac{2\pi n}{L_k}
\right|^{2r}
\left|
\left\langle
V_{n,i_k},
g_k
\right\rangle
\right|^2.
]

The intended exact tail inequality is:

[
\boxed{
|P_{m_k,N_k}g_k-g_k|^2
\le
\left(
\frac{L_k}{2\pi(N_k+1)}
\right)^{2r}
\mathcal E_r(S,k).
}
]

This is not a restatement of the projection tail. It is a weighted full-spectrum energy that could, in principle, be bounded from a prolate differential equation and an `E_star` regularity theorem.

Current source data does not supply (\mathcal E_r), its finiteness, or a uniform bound. Candidate B is therefore a real theorem shape but not currently an unconditional source theorem.

## 10. K6 plants

### `P056R-1 — \(N\)-dependent source rejection`

Temporary mutation:

```text
same m, two different N values, two unequal prolateCombination functions.
```

Expected result:

```text
G6_S2_SOURCE_N_DEPENDENT_TRIAL_REJECTED
```

The new coherence field must be impossible to discharge.

### `P056R-2 — certificate dependence remains legal`

Use one common `prolateCombination` at fixed (m), while allowing the supplied `eStar_memLp` and `trialNonzero` proofs to remain indexed by the full `PairIndex`.

Expected result:

```text
SOURCE_TRIAL_COHERENCE_ACCEPTS_N_DEPENDENT_PROJECTION_CERTIFICATES
```

This prevents overstrengthening the source repair into equality of projection data.

### `P056R-3 — fixed-space Fourier API remains insufficient`

Attempt to use a fixed-vector/fixed-carrier projection theorem directly on:

```text
k ↦ H_m (selectedPairIndex S k)
```

Expected result:

```text
G6_S2_PROJECTION_TAIL_VARYING_CARRIER_API_MISMATCH
```

Source coherence does not identify different (H_m) spaces.

### `P056R-4 — independent cofinality does not imply bandwidth cofinality`

Control:

[
m_k=2^{(k+1)^2},
\qquad
N_k=k+1.
]

Required result:

```text
PAIRCOFINAL_TRUE
PHYSICAL_BANDWIDTH_COFINAL_FALSE
```

Failure code:

```text
G6_S2_PAIRCOFINAL_TO_BANDWIDTH_INVALID
```

### `P056R-5 — exact parent/extract lock`

Mutation:

```text
selectedPairIndex S k
→ S.canonical.parent k
```

or:

```text
extract k → extract (k+1).
```

Expected result:

```text
G6_S2_SOURCE_COHERENCE_PARENT_EXTRACT_MISMATCH
```

No repaired theorem may reselect the sequence.

### `P056R-6 — no projection-tail restatement`

Source scan must reject any addition of:

```text
SelectedProjectionTailDecay
Tendsto selectedUnnormalizedGalerkinResidualNorm
projectionErrorTendsToZero
```

as a source field or axiom.

Expected result:

```text
G6_S2_SOURCE_REPAIR_TAIL_RESTATEMENT
```

These plants test six different semantics: source identity, legitimate (N)-dependent certificates, varying carriers, schedule scaling, path identity, and non-tautology.

## 11. Strongest attack

> Adding a coherence field merely assumes the desired source identity. It does not prove projection decay. Why count this as progress?

Correct: it does not prove projection decay.

`ProlateKTrialSourceData` is already a package of source-supplied facts—mode support, integrability certificates, bandwidth equality, and projected nonvanishing. The new field records a fact already fixed by the source definition: (h_m) depends on (m), not on (N).

Its value is fail-closed type correction:

```text
before:
  an N-varying source trial can enter the canonical route;

after:
  every future source constructor must prove that the consumed trial is
  the same whenever m is the same.
```

That is representation progress at the source boundary. It is not analytic progress, and the success code does not claim otherwise.

The stronger attack remains:

> Even after (N)-coherence, where does the uniform Fourier-energy estimate come from?

It does not currently exist. That is the sole next theorem-shape wall.

## 12. Final proposal

Implement only the source-coherence repair.

Do not attempt `selectedProjectionTailDecay` in the same transaction.

After success, the smallest next node is:

```text
G6_S2_D0_SELECTED_LOG_WINDOW_FOURIER_TAIL_RATE
```

with jump target:

[
|P_{m,N}g-g|^2
\le
\left(\frac{L_m}{2\pi(N+1)}\right)^{2r}
\mathcal E_r(g).
]

That next node must separate:

```text
generic Fourier-tail inequality;
physical-bandwidth coupling;
source-specific uniform energy supplier.
```

It remains unauthorized.

## META CLOSEOUT

**What became smaller?**

The opaque target

```text
prove selected projection-tail decay
```

has split into:

```text
same-m source coherence;
physical-bandwidth coupling;
weighted Fourier-energy control;
generic tail inequality.
```

**What was killed?**

* the universal theorem at the current interface;
* `lambda_eq` as a substitute for source identity;
* `PairCofinal → projection tail`;
* direct use of fixed-space Fourier completeness;
* post-hoc extraction reselection.

**What must not be tried again?**

Do not apply fixed-(m) Fourier density to a family whose carrier, vector, and physical cutoff all vary. Do not add the desired tail as a source field.

**Current smallest named gap:**

```text
G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_MISSING
```

**Next cheapest decisive test:**

Add the exact same-(m) coherence field and run the negative (N)-varying-source constructor plant before touching any tail theorem.

**Prediction fate:**

```text
Phase-4H prediction:
  fixed-space density would not directly prove the selected cofinal target.
  CONFIRMED.

Phase-4H prediction:
  the two-premise factorized receiver would compile.
  CONFIRMED.

Phase-4I prediction:
  source provenance contains an earlier N-coherence defect.
  CONFIRMED.

Candidate-B prediction:
  the next real wall is a uniform weighted Fourier-energy supplier.
  REGISTERED; UNTESTED.
```

```yaml
iteration:
  target: selected_projection_tail_decay
  status: OPEN
  failed_strategy: fixed_space_Fourier_density_on_an_N_dependent_varying_carrier_source
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_MISSING
  invariant_learned: the consumed prolate trial is determined by m while projection certificates may depend on N
  forbidden_future_move: restate_projection_tail_as_source_data_or_reselect_parent_extract
  next_decisive_test: same_m_different_N_source_coherence_negative_constructor
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_REPAIR

TRANSACTION:
  G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_REPAIR

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
  expected_head: e2ef5f0741c15b644514eade8332d35ed5629666

  required_sha256:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean:
      8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
    q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean:
      3004f7551bcf187bb21d0de19a1e6c90f9836c749d00836ed8543389e54423b1
    q3.lean.aristotle/Q3/Proofs/RouteB/D0CanonicalApproximation.lean:
      60409208d26aeae7b4974150bd66ad42da83f09a223f41196dbde7abd3157695
    q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean:
      c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48
    q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage2.lean:
      aabaf47cb484f0157fd7b2ac4f30811aec9595116c1193715e41de8b520393cd
    q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean:
      59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
    q3.lean.aristotle/Q3/Proofs/RouteB/ProlateLayer.lean:
      3c2099c97df6cd0fb45f7b367d24898d11c031ed297fe9031b25ee5b9dc0edf4
    q3.lean.aristotle/Q3/Proofs/RouteB/ProlateCombinationMuntzRegularity.lean:
      d3990c1be7288b49f6d63dec42bbfa12e7799a955d80bee24c3ca9dcea9624c0
    q3.lean.aristotle/literature/zotero/H8ULBMAL/fulltext.md:
      7ba4b01845df2989cdd763a19c83904e4114e26fc51d5d7f93d09489d52871d4

ON_SOURCE_MISMATCH:
  stop: G6_S2_SOURCE_N_COHERENCE_SOURCE_LOCK_MISMATCH
  edit_files: false

MODIFY_EXACTLY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean

CREATE_PRODUCTION_FILES: []

STRUCTURE_REPAIR: |
  structure ProlateKTrialSourceData where
    pair : PairIndex → ProlatePair

    prolateCombination_eq_of_same_m :
      ∀ i j : PairIndex, i.m = j.m →
        prolateCombination (pair i) =
          prolateCombination (pair j)

    lambda_eq : ∀ i, (pair i).pw.lambda = lambda_m i

    eStar_memLp :
      ∀ i,
        MemLp (E_star (prolateCombination (pair i))) 2
          (dStar.restrict (I_m i))

    trialNonzero :
      ∀ i,
        TrialNonzero i
          (prolateCombination (pair i))
          (eStar_memLp i)

PUBLIC_THEOREM_ADD: |
  @[simp] theorem ProlateKTrialSourceData.E_star_eq_of_same_m
      (S : ProlateKTrialSourceData)
      (i j : PairIndex)
      (hm : i.m = j.m) :
      E_star (prolateCombination (S.pair i)) =
        E_star (prolateCombination (S.pair j)) := by
    rw [S.prolateCombination_eq_of_same_m i j hm]

COMMENT_REPAIR:
  - state that the consumed source trial is determined by m
  - state that N enters only through projection and its certificates
  - remove wording suggesting independent source packets for every (m,N)
  - state explicitly that no projection-tail or regularity theorem is proved

PUBLIC_SURFACE_DELTA:
  structure_fields_added: 1
  public_theorems_added: 1
  public_definitions_added: 0
  private_declarations_added: 0

MIGRATION_POLICY:
  current_production_constructors_found: 0
  direct_importer_to_recompile:
    - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzCenteredCoordinateLock.lean
  transitive_consumers_to_recompile:
    - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
    - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean
    - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFullMellinGwinCrosswalk.lean
    - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualCrosswalk.lean
    - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
  downstream_statement_changes_allowed: false
  if_any_constructor_is_found:
    stop: G6_S2_SOURCE_N_COHERENCE_CONSTRUCTOR_MIGRATION_GAP
    do_not_invent_coherence_proof: true

K6_OBJECT_PRECOMMIT:
  source_trial: prolateCombination
  source_index: m_only
  projection_index: pair_m_N
  same_m_different_N_source_trial: equal
  eStar_memLp_certificate: may_depend_on_N
  trialNonzero_certificate: may_depend_on_N
  canonical_path: existing_parent_comp_extract
  projection_tail_claimed: false

MANDATORY_PLANTS:
  P056R_1_N_DEPENDENT_SOURCE_REJECTED:
    mutation: same_m_different_N_unequal_prolateCombination
    expected: G6_S2_SOURCE_N_DEPENDENT_TRIAL_REJECTED

  P056R_2_N_DEPENDENT_CERTIFICATES_ALLOWED:
    mutation: same_source_trial_with_pair_indexed_MemLp_and_TrialNonzero_certificates
    expected: SOURCE_TRIAL_COHERENCE_ACCEPTS_N_DEPENDENT_PROJECTION_CERTIFICATES

  P056R_3_FIXED_SPACE_API:
    mutation: apply_fixed_carrier_projection_convergence_to_selected_varying_H_m_family
    expected: G6_S2_PROJECTION_TAIL_VARYING_CARRIER_API_MISMATCH

  P056R_4_PAIRCOFINAL_BANDWIDTH:
    control:
      m_k: "2 ^ ((k + 1) ^ 2)"
      N_k: "k + 1"
    expected:
      - BOTH_COORDINATES_COFINAL
      - N_DIV_LOG_M_TENDS_TO_ZERO
    failure_code: G6_S2_PAIRCOFINAL_TO_BANDWIDTH_INVALID

  P056R_5_PARENT_EXTRACT:
    mutation: replace_parent_extract_k_by_parent_k_or_shifted_extract
    expected: G6_S2_SOURCE_COHERENCE_PARENT_EXTRACT_MISMATCH

  P056R_6_NO_TAIL_RESTATEMENT:
    forbidden_source_fields:
      - SelectedProjectionTailDecay
      - projectionErrorTendsToZero
      - Tendsto_selectedUnnormalizedGalerkinResidualNorm
    expected: G6_S2_SOURCE_REPAIR_TAIL_RESTATEMENT

VALIDATION:
  - verify HEAD equals origin before editing
  - verify every required SHA-256
  - confirm no production ProlateKTrialSourceData constructor exists before edit
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzCenteredCoordinateLock.lean
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
  - dedicated target build
  - full build
  - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
  - scan for sorry admit exact? native_decide axiom opaque Float
  - scan for imports from aristotle_output or ACTIVE RequestProject
  - require public-surface delta exactly one field and one theorem
  - fire P056R_1 through P056R_6
  - remove all temporary plant files
  - print axioms Q3.RouteB.D0Pstar.ProlateKTrialSourceData.E_star_eq_of_same_m
  - require exactly [propext, Classical.choice, Quot.sound]
  - reprint axioms of both Phase4H public theorems
  - require Phase4H theorem statements byte-unchanged
  - proof database reimport
  - require the new theorem indexed and proven
  - run all 67 orchestration tests
  - python3 orchestrator/spine.py --strict --reason goal-close
  - require strict Spine PASS
  - run SQLite integrity_check on knowledge.db
  - run SQLite integrity_check on aristotle_proofs.db
  - run SQLite integrity_check on observability.db
  - require all three equal ok
  - report observability source count stale count and numeric ZERO_COVERAGE separately
  - git diff --check
  - exact git status report

STOP:
  G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_MISSING

SUCCESS:
  G6_S2_D0_PROLATE_SOURCE_SAME_M_TRIAL_COHERENCE_LOCKED

AFTER_SUCCESS:
  selectedProjectionTailDecay_proved: false
  selectedTrialNormalizerBounded_proved: false
  unconditional_normalized_residual_decay_proved: false
  current_universal_target_reactivated: false

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  name: G6_S2_D0_SELECTED_LOG_WINDOW_FOURIER_TAIL_RATE
  jump_target: |
    ‖(gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp‖ ^ 2
      ≤
    (L_m i / (2 * Real.pi * (i.N + 1))) ^ (2 * r) *
      FourierEnergy_r i (gTrial_m i h hLp)
  required_future_inputs:
    - physical_bandwidth_or_combined_rate_law
    - independently_defined_weighted_Fourier_energy
    - source_proved_uniform_or_coupled_energy_control
  projection_tail_as_hypothesis: forbidden

ARISTOTLE:
  status: FORBIDDEN

FORBIDDEN:
  - prove selectedProjectionTailDecay in this transaction
  - add projection tail as a source field
  - infer source equality from lambda_eq only
  - require eStar_memLp or trialNonzero proof equality across N
  - invoke fixed-space Fourier convergence on varying H_m
  - infer N_div_log_m divergence from PairCofinal
  - change parent or extract
  - select a new subsequence
  - modify Phase4A through Phase4H production files
  - prove compact_open_decay
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
