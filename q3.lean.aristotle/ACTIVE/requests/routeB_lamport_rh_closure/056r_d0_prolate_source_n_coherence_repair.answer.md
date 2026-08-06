# GOAL 056 / Phase 4I answer — prolate source N-coherence repair

```yaml
GOAL: 056
PHASE: 4I
NODE: D0ProlateKTrialSource
STATUS: CLOSED
EXACT_RESULT: G6_S2_D0_PROLATE_SOURCE_SAME_M_TRIAL_COHERENCE_LOCKED
OPERATIVE_CLASS: TRY_G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_REPAIR
ARSENAL_USED: [C04, C09, C10, C12]

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 9
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated decision and honest status

The ninth batch in the same living Proshka phase chat selected the minimal
same-`m` source repair at pin
`e2ef5f0741c15b644514eade8332d35ed5629666`. Its exact 30,705-byte verdict
is archived canonically and in the bus mirror with SHA-256
`0e954f41389df08204693a79a49c89a0f3c517d8d7172781b54c7934a1a6c714`.

The previously proposed universal theorem

```lean
theorem selectedProjectionTailDecay
    (S : ProlateCanonicalSourceData) :
    SelectedProjectionTailDecay S
```

is `KILLED_AS_CURRENT_SOURCE_UNSUPPORTED_THEOREM_SHAPE`. Its mathematical
negation was not proved. This transaction corrects the source interface only:
the prolate trial consumed at fixed `m` can no longer change when `N`
changes.

Projection-tail decay, bounded selected normalizers, unconditional normalized
residual decay, compact-open convergence, and strict `SlotS2` all remain
open.

## Materialized production interface

```yaml
PRODUCTION_MODULE: Q3.Proofs.RouteB.D0ProlateKTrialSource
PRODUCTION_SHA256: 7597910a8cf2160c4ab9786144d25595a6c519395f64fc0846d84a249a96c016
PRODUCTION_LINES: 133
PRODUCTION_BYTES: 4894
MODIFIED_PRODUCTION_FILES: 1
NEW_PRODUCTION_FILES: 0
STRUCTURE_FIELDS_ADDED: 1
PUBLIC_THEOREMS_ADDED: 1
PUBLIC_DEFINITIONS_ADDED: 0
PRIVATE_DECLARATIONS_ADDED: 0
```

The new source invariant is:

```lean
prolateCombination_eq_of_same_m :
  ∀ i j : PairIndex, i.m = j.m →
    prolateCombination (pair i) =
      prolateCombination (pair j)
```

The single derived public theorem is:

```lean
@[simp] theorem ProlateKTrialSourceData.E_star_eq_of_same_m
    (S : ProlateKTrialSourceData)
    (i j : PairIndex)
    (hm : i.m = j.m) :
    E_star (prolateCombination (S.pair i)) =
      E_star (prolateCombination (S.pair j))
```

Its proof is exactly one rewrite by the new structure field. No projection
tail, regularity, source constructor, new subsequence, or downstream theorem
statement was added.

The module commentary now states the real ownership split: the consumed source
trial is determined by `m`; `N` enters through projection and the
pair-indexed `MemLp` / `TrialNonzero` certificates.

## Atomic migration result

The pre-edit search found zero production constructors of
`ProlateKTrialSourceData`. Therefore no coherence proof was invented.

The direct importer
`D0PstarMuntzCenteredCoordinateLock.lean` and the downstream Phase-4H module
`D0PstarGalerkinResidualDecay.lean` both compile unchanged. The latter
retains SHA-256
`8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63`,
so both public Phase-4H statements are byte-unchanged.

## Load-bearing plant results

```yaml
P056R_1_N_DEPENDENT_SOURCE_REJECTED:
  result: FIRED
  stop: G6_S2_SOURCE_N_DEPENDENT_TRIAL_REJECTED
  evidence: unequal prolateCombination values at equal m contradict the new field in Lean
P056R_2_N_DEPENDENT_CERTIFICATES_ALLOWED:
  result: FIRED
  success: SOURCE_TRIAL_COHERENCE_ACCEPTS_N_DEPENDENT_PROJECTION_CERTIFICATES
  evidence: Lean accepts eStar_memLp independently at two full PairIndex values with equal m
P056R_3_FIXED_SPACE_API:
  result: FIRED
  stop: G6_S2_PROJECTION_TAIL_VARYING_CARRIER_API_MISMATCH
  evidence: Lean rejects an H_m(selected k) term where H_m(selected (k+1)) is required
P056R_4_PAIRCOFINAL_BANDWIDTH:
  result: FIRED
  stop: G6_S2_PAIRCOFINAL_TO_BANDWIDTH_INVALID
  evidence: m_k=2^((k+1)^2), N_k=k+1, while N_k/log(m_k)=1/((k+1)log 2) tends to zero
P056R_5_PARENT_EXTRACT:
  result: FIRED
  stop: G6_S2_SOURCE_COHERENCE_PARENT_EXTRACT_MISMATCH
  evidence: Lean rejects rfl between selectedPairIndex S k and (S.canonical.parent k).1
P056R_6_NO_TAIL_RESTATEMENT:
  result: FIRED
  stop: G6_S2_SOURCE_REPAIR_TAIL_RESTATEMENT
  evidence: injected forbidden name is detected and production structure scan is clean
TEMPORARY_PLANT_FILES: REMOVED
```

The six controls exercise distinct semantics. In particular, the successful
source repair does not make a fixed-space Fourier theorem applicable to the
varying selected `H_m` family.

## Validation

```yaml
SOURCE_LOCKS: PASS_9_OF_9
HEAD_ORIGIN_BEFORE_EDIT: EQUAL
PRODUCTION_CONSTRUCTORS_BEFORE_EDIT: 0
DIRECT_LEAN_OWNED_FILE: PASS
DIRECT_LEAN_DIRECT_IMPORTER: PASS
DIRECT_LEAN_PHASE4H: PASS
TARGET_BUILD: PASS_7781_JOBS
FULL_BUILD: PASS_7817_JOBS
Q3_CHECK: PASS
HOLE_TAINT_FORBIDDEN_IMPORT_SCAN: ZERO
PUBLIC_DELTA: 1_structure_field_1_theorem_0_definitions_0_private
PLANTS: PASS_6_OF_6
TEMPORARY_PLANT_FILES: REMOVED
NEW_THEOREM_AXIOMS: [propext, Classical.choice, Quot.sound]
PHASE4H_SHA256_UNCHANGED: 8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
PHASE4H_AXIOMS: [propext, Classical.choice, Quot.sound]
PROOF_DB_DOC_STATUS: proven
PROOF_DB_NEW_THEOREM: indexed_and_proven
ORCHESTRATOR_TESTS: PASS_67_OF_67
STRICT_SPINE: P9_STRICT_PASS_goal-close
OBSERVABILITY_SNAPSHOT: OBS_53ecac440b1664686256
OBSERVABILITY: 8_sources_0_stale
OBSERVABILITY_FILES: 3339
OBSERVABILITY_IMPORT_EDGES: 5577
OBSERVABILITY_SORRY_SITES: 0
OBSERVABILITY_PROOF_ROOTS: 2
OBSERVABILITY_TAINT_SOURCES: 1
OBSERVABILITY_DEGRADED: 1_numeric_ZERO_COVERAGE_not_PASS
SQLITE_INTEGRITY:
  knowledge.db: ok
  aristotle_proofs.db: ok
  observability.db: ok
```

The exact external verdict contains one intentional trailing space; it was
preserved to keep the archive SHA byte-faithful and excluded only from the
generic whitespace check. All authored files pass `git diff --check`.

The existing user-owned `qmd embed -f` process remained running and was not
duplicated or interrupted. Sensor refresh and strict Spine passed; semantic
refresh was not started behind that process.

## Honest boundary and next wall

Phase 4I closes exactly this provenance seam:

```text
same m
  => same consumed prolateCombination
  => same E_star source function
```

It does not identify different carriers, prove that physical cutoff diverges,
or bound Fourier energy uniformly.

The sole next node is now named:

```text
G6_S2_D0_SELECTED_LOG_WINDOW_FOURIER_TAIL_RATE
```

Its future theorem package must keep three components separate:

1. a generic weighted Fourier-tail inequality;
2. a physical-bandwidth or combined-rate law involving `N / log m`;
3. a source-proved uniform or coupled weighted-energy estimate.

That node is not authorized by this transaction. Aristotle remains forbidden.
Route B remains `CHALLENGER / NOT_RH`; Bus 010 remains `VOID`; Goal 055
remains `HOLD`; no route promotion, PX claim, or RH claim occurred.
