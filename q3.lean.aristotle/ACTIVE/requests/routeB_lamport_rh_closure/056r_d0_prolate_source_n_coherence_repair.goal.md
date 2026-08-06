# GOAL 056 / Phase 4I — prolate source N-coherence repair

```yaml
GOAL: 056
PHASE: 4I
NODE: D0ProlateKTrialSource
STATUS: OPEN
OPERATIVE_CLASS: TRY_G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_REPAIR
TRANSACTION: G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_REPAIR
STOP: G6_S2_D0_PROLATE_SOURCE_N_COHERENCE_MISSING
SUCCESS: G6_S2_D0_PROLATE_SOURCE_SAME_M_TRIAL_COHERENCE_LOCKED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
PROSHKA_CALLS_THIS_PHASE: 9
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```

## Delegated strategic decision

The ninth batch in the same living Proshka phase chat selected the minimal
same-`m` source repair under `CODEX_PLUS_PROSHKA` authority at pin
`e2ef5f0741c15b644514eade8332d35ed5629666`.

The exact 30,705-byte verdict is materialized canonically and in the bus
mirror with SHA-256
`0e954f41389df08204693a79a49c89a0f3c517d8d7172781b54c7934a1a6c714`.

The current universal target

```lean
theorem selectedProjectionTailDecay
    (S : ProlateCanonicalSourceData) :
    SelectedProjectionTailDecay S
```

is killed **as a theorem shape supported by the current source interface**.
Its mathematical negation is not proved. The precise classification is
`OVERSTRONG_AND_UNDERDETERMINED`: the source trial may currently vary with
`N`, and independent `PairCofinal` does not imply divergence of the
physical cutoff `N / log m`.

This transaction repairs only the earlier type-level source bug. It proves no
projection-tail, regularity, normalizer, compact-open, or SlotS2 theorem.

## Source lock

```yaml
HEAD: e2ef5f0741c15b644514eade8332d35ed5629666
REQUIRED_SHA256:
  D0PstarGalerkinResidualDecay.lean: 8fe089afef9e6a43f7b6c7b7b737bc0709e7e35d41ae73a34ab94c49f1f62f63
  D0ProlateKTrialSource.lean: 3004f7551bcf187bb21d0de19a1e6c90f9836c749d00836ed8543389e54423b1
  D0CanonicalApproximation.lean: 60409208d26aeae7b4974150bd66ad42da83f09a223f41196dbde7abd3157695
  D0KTrialStage1.lean: c7dd206ab7979d3390a50969c71919c04582f0c1514dbb142fe1883148ce5b48
  D0KTrialStage2.lean: aabaf47cb484f0157fd7b2ac4f30811aec9595116c1193715e41de8b520393cd
  D0LogWindowMeasureTransport.lean: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
  ProlateLayer.lean: 3c2099c97df6cd0fb45f7b367d24898d11c031ed297fe9031b25ee5b9dc0edf4
  ProlateCombinationMuntzRegularity.lean: d3990c1be7288b49f6d63dec42bbfa12e7799a955d80bee24c3ca9dcea9624c0
  H8ULBMAL/fulltext.md: 7ba4b01845df2989cdd763a19c83904e4114e26fc51d5d7f93d09489d52871d4
ON_MISMATCH: G6_S2_SOURCE_N_COHERENCE_SOURCE_LOCK_MISMATCH
PRODUCTION_CONSTRUCTORS_FOUND: 0
ON_CONSTRUCTOR: G6_S2_SOURCE_N_COHERENCE_CONSTRUCTOR_MIGRATION_GAP
```

No production edit is permitted if a lock fails or a constructor appears.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  source_trial: prolateCombination
  source_index: m_only
  projection_index: pair_m_N
  same_m_different_N_source_trial: equal
  eStar_memLp_certificate: may_depend_on_N
  trialNonzero_certificate: may_depend_on_N
  canonical_path: existing_parent_comp_extract
  projection_tail_claimed: false

OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
NEW_PRODUCTION_FILES: 0
STRUCTURE_FIELDS_ADDED: 1
PUBLIC_THEOREMS_ADDED: 1
PUBLIC_DEFINITIONS_ADDED: 0
PRIVATE_PRODUCTION_DECLARATIONS_ADDED: 0
```

Fixing `m` fixes the consumed `prolateCombination`. The full `ProlatePair`
and its proof certificates need not be propositionally equal across different
`N` values.

## Exact production surface

Add exactly one structure field after `pair`:

```lean
prolateCombination_eq_of_same_m :
  ∀ i j : PairIndex, i.m = j.m →
    prolateCombination (pair i) =
      prolateCombination (pair j)
```

Add exactly one public derived theorem:

```lean
@[simp] theorem ProlateKTrialSourceData.E_star_eq_of_same_m
    (S : ProlateKTrialSourceData)
    (i j : PairIndex)
    (hm : i.m = j.m) :
    E_star (prolateCombination (S.pair i)) =
      E_star (prolateCombination (S.pair j)) := by
  rw [S.prolateCombination_eq_of_same_m i j hm]
```

Repair the module commentary to state:

- the consumed source trial is determined by `m`;
- `N` enters through finite projection and its certificates;
- no projection-tail or regularity theorem is proved.

No downstream theorem statement may change.

## Atomic migration surface

Direct importer:

```text
D0PstarMuntzCenteredCoordinateLock.lean
```

Transitive consumers to recompile:

```text
D0PstarMuntzGalerkinResidualContract.lean
D0PstarProjectedMellinCoordinate.lean
D0PstarFullMellinGwinCrosswalk.lean
D0PstarMuntzGalerkinResidualCrosswalk.lean
D0PstarGalerkinResidualDecay.lean
```

## Load-bearing plants

```yaml
P056R_1_N_DEPENDENT_SOURCE_REJECTED:
  mutation: same_m_different_N_unequal_prolateCombination
  expected: G6_S2_SOURCE_N_DEPENDENT_TRIAL_REJECTED
P056R_2_N_DEPENDENT_CERTIFICATES_ALLOWED:
  control: same_source_trial_with_pair_indexed_certificates
  expected: SOURCE_TRIAL_COHERENCE_ACCEPTS_N_DEPENDENT_PROJECTION_CERTIFICATES
P056R_3_FIXED_SPACE_API:
  mutation: fixed_carrier_projection_convergence_on_varying_H_m
  expected: G6_S2_PROJECTION_TAIL_VARYING_CARRIER_API_MISMATCH
P056R_4_PAIRCOFINAL_BANDWIDTH:
  control: m_k_eq_2_pow_k_plus_1_sq__N_k_eq_k_plus_1
  expected: G6_S2_PAIRCOFINAL_TO_BANDWIDTH_INVALID
P056R_5_PARENT_EXTRACT:
  mutation: parent_k_or_shifted_extract
  expected: G6_S2_SOURCE_COHERENCE_PARENT_EXTRACT_MISMATCH
P056R_6_NO_TAIL_RESTATEMENT:
  mutation: add_projection_tail_field_or_axiom
  expected: G6_S2_SOURCE_REPAIR_TAIL_RESTATEMENT
```

The plants separately pin source identity, legitimate certificate dependence,
varying carriers, physical bandwidth, the canonical selected path, and
non-tautology.

## Validation and boundary

Required validation: all source locks; direct Lean on the owned module,
direct importer and Phase-4H module; dedicated target and full builds;
`scripts/q3_check.sh`; hole/taint/forbidden-import scans; exact public delta;
all six plants with temporary files removed; standard axiom triple for the new
theorem; Phase-4H statements and axioms unchanged; proof-DB reimport; all 67
orchestration tests; strict Spine; three SQLite integrity checks; observability
source/stale counts and numeric `ZERO_COVERAGE` reported separately;
`git diff --check`; exact status.

After success these remain open:

```text
SelectedProjectionTailDecay
SelectedTrialNormalizerBounded
unconditional normalized residual decay
compact-open decay
strict SlotS2
```

The sole next node, not authorized in this transaction, is
`G6_S2_D0_SELECTED_LOG_WINDOW_FOURIER_TAIL_RATE`. Aristotle, a new
subsequence, changes to `parent` or `extract`, Phase 4A--4H edits,
`Q3.Main`, Goal 055, Bus 010, route promotion, PX, and RH claims are
forbidden.
