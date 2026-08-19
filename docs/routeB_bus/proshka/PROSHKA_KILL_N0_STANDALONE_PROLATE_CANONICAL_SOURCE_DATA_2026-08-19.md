# STATUS: FATAL FOR STANDALONE N0 — `ProlateCanonicalSourceData` ALREADY CONSUMES THE ANALYTIC NONVANISHING THAT N0 WAS SUPPOSED TO PRECEDE

```yaml
PRIMARY: KILL_N0_AS_STANDALONE_OBJECT_LOCK
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  OWNER_INPUT_PIN: 29bb34274c5847a8d7849b515ab652eaf1657402
  AUDITED_HEAD: 4054dedd130a9d533a76a3306a8629c669c09f53
  RELEVANT_LEAN_CHANGED_AFTER_OWNER_PIN: false

TARGET:
  NODE: N0
  NAME: ProlateCanonicalSourceDataSupply
  PROPOSED_ROLE: FIRST_OBJECT_LOCK_BEFORE_N1
  VERDICT: KILLED_AS_STANDALONE_FIRST_NODE

CLOSES:
  - N0_STANDALONE_ORDERING_ADJUDICATION
OPENS: []

REVEALS_PREEXISTING_HIDDEN_INPUTS:
  - PROJECTED_PROLATE_TRIAL_NONZERO_ON_THE_CONSUMED_CARRIER
  - COFINAL_CENTRAL_RAWFPLUS_NONVANISHING_SCHEDULE

SOURCE_WRITE:
  LEAN_SOURCE_WRITTEN: false
  SOURCE_RECORD_WRITTEN: false
  REASON: W9_FORBIDS_A_SOURCE_THAT_ONLY_RESTATES_HIDDEN_OPEN_INPUTS

FATAL_SCOPE:
  PROLATE_CANONICAL_SOURCE_DATA_MATHEMATICALLY_IMPOSSIBLE: false
  CURRENT_ROUTE_FATAL: false
  N0_AS_FIRST_PURE_OBJECT_NODE: true
  ARBITRARY_PROLATEPAIR_INHABITANT_AS_REPAIR: forbidden

CURRENT_SHELF:
  SELECTED_FERRERS_PRODUCTION_PROLATE_PAIR: LEAN_PROVED_EXISTENTIAL
  SAME_M_SOURCE_COHERENCE_INTERFACE: LEAN_PROVED
  EXACT_LAMBDA_LOCK: AVAILABLE
  ESTAR_MEMLP_ROUTE: AVAILABLE_FROM_SOURCE_REGULARITY
  TRIAL_NONZERO_ALL_PAIR_INDICES: NOT_PROVED
  CENTRAL_INDEX_COFINAL_FAMILY: NOT_PROVED
  PROLATE_CANONICAL_SOURCE_DATA_INHABITANT: ABSENT

TYPE_AUDIT:
  ProlateKTrialSourceData_requires:
    - pair_for_every_PairIndex
    - same_m_prolateCombination
    - lambda_eq
    - eStar_memLp_for_every_PairIndex
    - TrialNonzero_for_every_PairIndex
  ProlateCanonicalSourceData_requires:
    - ProlateKTrialSourceData
    - CanonicalData
    - exact_kTrial_equality
  CanonicalData_requires:
    - parent_into_CentralIndex
    - PairCofinal_parent
    - strict_extraction
  CentralIndex_requires:
    - bareTransform_at_zero_nonzero
    - equivalently_rawFplus_at_zero_nonzero

ORDERING_RESULT:
  PROPOSED: N0_then_N1_then_N2_then_N3_then_N4
  REJECTED_REASON: N0 already requires finite projected nonvanishing and a cofinal central-value schedule
  REPAIRED_DEPENDENCY: >-
    source-pair shelf plus trial-limit/finite-defect analysis must first produce
    selected projected nonvanishing and central nonvanishing; only then may the
    final ProlateCanonicalSourceData object be assembled

NEXT_LOAD_BEARING_GAP:
  SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING

MINIMAL_MISSING_IDENTITY: >-
  on one precommitted cofinal sequence i_k=(m_k,N_k), prove both
  TrialNonzero i_k (prolateCombination P_{m_k}) and
  rawFplus (exact source coefficient family) i_k 0 != 0,
  with the exact finite projection and no fitted phase or scalar

CANDIDATE_REPRESENTATIONS:
  - code: SELECTED_CARRIER_SOURCE_DATA
    description: >-
      split the current overstrong all-PairIndex source record into a source
      packet family and a selected cofinal finite-projection record; require
      TrialNonzero and CentralIndex only on the consumed sequence
    kill_power: 9/10
    cost: 5/10
  - code: EVENTUAL_CENTRAL_NONVANISHING_FROM_LIMIT_PLUS_DEFECT
    description: >-
      port the CCM trial-to-Xi limit at z=0 and combine it with an exact finite
      projected-transform defect bound to obtain eventual rawFplus(0) != 0;
      assemble the cofinal source object only afterward
    kill_power: 10/10
    cost: 8/10

REGISTERED_PREDICTIONS:
  N0_SPECIFIC_PRETEST_PREDICTION: NONE
  SCORE: NOT_APPLICABLE
  DISCIPLINE_NOTE: >-
    the source audit began before an N0-specific probability was registered;
    no retrospective prediction or score is invented

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C12_BOUNDED_POTENTIAL_EXCLUSION

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 4
```

## ROUTE MAP

### 1. What the existing contract actually asks for

`D0ProlateKTrialSource.lean` does not merely ask for a source-mode object. Its
`ProlateKTrialSourceData` field

```lean
trialNonzero : forall i,
  TrialNonzero i (prolateCombination (pair i)) (eStar_memLp i)
```

requires the exact finite Galerkin projection to be nonzero for **every**
`PairIndex`. This is already an analytic statement about the projected source,
not record assembly.

The outer structure then stores an existing `CanonicalData`. That record has

```lean
parent : Nat -> CentralIndex kTrial
parentCofinal : PairCofinal parent
```

and `CentralIndex` is the subtype on which the finite transform at the anchor is
nonzero. Thus a `ProlateCanonicalSourceData` inhabitant already contains a
cofinal theorem

```text
rawFplus(source row, i_k, 0) != 0.
```

The proposed N0 therefore packages two load-bearing analytic nonvanishing
results inside what the road map called an object lock.

### 2. What is already on the shelf

The selected Ferrers production layer constructs, for every `mProject >= 2`,
a literal degree-zero/degree-four `ProlatePair`. The canonical tail split
`K = 4*mProject` supplies the separation hypothesis. The resulting pair has the
production bandwidth `sqrt mProject`, positive source integrals, nonzero finite
Fourier scalars, exact finite-Fourier eigenrelations, and source-mode
orthogonality.

The project also has the exact same-`m` coherence interface and the source
regularity machinery needed to prove `E_star` membership on the compact
multiplicative window.

These facts close much of the raw source-packet construction. They do **not**
prove the two nonvanishing clauses above.

### 3. Why the missing clauses do not follow formally

`TrialNonzero` means

```text
0 < norm(P_(m,N) gTrial_m).
```

A nonzero source function does not imply that every finite Fourier projection
is nonzero. Completeness gives an existential statement for some sufficiently
large cutoff, not nonvanishing at every cutoff.

Even `TrialNonzero` does not imply `CentralIndex`. A nonzero finite coefficient
row can have zero central coefficient. The repository deliberately keeps the
`TrialNonzero` locus and the central-nonzero locus separate; the central
calibration audit explicitly records

```text
NO_UNCONDITIONAL_TRIAL_NONZERO
NO_COFINAL_BDET_NONZERO_SET.
```

`D0AnchorFloor.lean` is a receiver, not a supplier: it derives projected and
central nonvanishing only after receiving a positive unprojected central-mass
bound. `D0SelectedCentralFloor.lean` likewise assumes a `SelectedAnchorRatioData`
packet containing the positive mass and ratio estimates.

Therefore no theorem currently turns the selected Ferrers pair into a full
`ProlateCanonicalSourceData` inhabitant.

### 4. Why the easy Lean inhabitant is forbidden

`ProlatePair` is intentionally a weak data record. The project contains a
`looseProlatePairPlant` and proves that it is not an actual source-mode pair.
Using such an arbitrary inhabitant, or manufacturing a coefficient row with a
convenient nonzero constant mode, could satisfy a weakened record but would
change the source function consumed by the CCM/Muntz route.

That is a direct **C10 functional-not-surrogate kill** and a **C04 same-interface,
different-object failure**. A green record constructor for the wrong function
would not close N0.

## FINAL PROPOSAL

Do not write a Lean source for standalone N0. It would have to do one of three
forbidden things:

1. assume `TrialNonzero` and cofinal central nonvanishing as fresh fields;
2. use an arbitrary convenient `ProlatePair` instead of the selected source;
3. hide the same assumptions behind `Classical.choose` without an existence
   theorem.

The honest repair is to make the hidden nonvanishing theorem explicit. The
smallest consumer-ready statement is:

```text
SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING

There exists one precommitted cofinal sequence i_k=(m_k,N_k) such that the
selected Ferrers source packet has:
  - exact E_star MemLp;
  - nonzero finite projection;
  - nonzero rawFplus at z=0;
  - exact same-m source coherence.
```

Only after that theorem may `CanonicalData` and
`ProlateCanonicalSourceData` be assembled without new mathematical inputs.

The likely source of the theorem is not record plumbing. It is the combination
of the CCM Lemma-7.3 central limit with an exact finite-projection/transform
defect estimate. This means the current graph has a dependency inversion: the
final canonical object cannot precede all of N1/N2 in its present type.

## STRONGEST ATTACK

> Perhaps the selected prolate packet has a nonzero zero Fourier coefficient
> for elementary sign reasons, so N0 can still go first.

The current source does not contain that theorem. Positive `I0`, positive `I4`,
nonzero finite-Fourier eigenvalues, and nonzero `prolateCombination` concern the
source modes. The needed quantity is the central logarithmic Fourier
coefficient of the **starred summation map after finite projection**. No exact
identity equating those quantities exists in the current tree.

Numerical observations that the coefficient is negative at sampled cells are
not a cofinal theorem and cannot inhabit `CentralIndex`.

The repaired claim is weaker and exact:

```text
The selected source-pair family exists and is source-locked.
The final ProlateCanonicalSourceData inhabitant remains blocked specifically
by selected finite projected and central nonvanishing.
```

## CODEX DIRECTIVE

```text
NO LEAN EXECUTION FOR STANDALONE N0.

Read-only next task:
  SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING_PREFLIGHT

Required output:
  1. exact theorem signatures relating
       inner(V0, gTrial_m), Gwin(...,0), and rawFplus(...,0);
  2. whether CCM Lemma 7.3 supplies a quantitative nonzero margin at z=0;
  3. the exact finite-projection defect needed to transfer that margin;
  4. one precommitted cofinal schedule;
  5. either a theorem-ready source statement with no new inputs,
     or KILL_CENTRAL_NONVANISHING_FROM_CURRENT_CORPUS.

Forbidden:
  arbitrary ProlatePair;
  assumed TrialNonzero;
  fitted central phase;
  numerical nonzero samples as a universal proof;
  editing ProlateCanonicalSourceData to erase source provenance.
```

## META CLOSEOUT

**What became smaller?**

The vague object wall is now one exact theorem:

```text
SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING.
```

**What was killed?**

The ordering claim that `ProlateCanonicalSourceData` can be constructed as a
pure first object node before the nonvanishing/limit analysis.

**What must not be tried again?**

Do not inhabit the weak `ProlatePair` interface with a convenient surrogate and
do not restate `TrialNonzero` or `CentralIndex` as constructor assumptions.

**Current smallest named gap?**

```text
SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING.
```

**Next cheapest decisive test?**

At `z=0`, derive the exact equality chain

```text
inner(V0, gTrial_m)
<-> full-window Gwin source value
<-> finite rawFplus central coefficient plus projection defect,
```

then test whether the paper Lemma-7.3 estimate yields a strict eventual margin.

**Fate of prior registered predictions?**

No N0-specific prediction was registered before this audit. None is scored or
retroactively repaired.

**Memory entry**

```yaml
iteration:
  target: ProlateCanonicalSourceDataSupply as first N0 node
  status: FATAL_FOR_PROPOSED_ORDERING
  failed_strategy: pure_record_assembly
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING
  invariant_learned: >-
    source identity, finite projected nonvanishing, and central-value
    nonvanishing are distinct obligations
  forbidden_future_move: >-
    do not use an arbitrary ProlatePair or assume TrialNonzero/CentralIndex
  next_decisive_test: >-
    central z=0 equality plus Lemma-7.3 margin and finite-defect transfer
```
