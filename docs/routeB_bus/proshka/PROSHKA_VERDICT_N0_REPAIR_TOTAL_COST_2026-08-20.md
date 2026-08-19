# STATUS: CONDITIONAL — B ДОМИНИРУЕТ ПО СОВОКУПНОЙ ЦЕНЕ, НО ТОЛЬКО КАК PRE-ANCHOR N1 + EXACT ZERO-MODE + ADDITIVE SELECTED SHELL

```yaml
PRIMARY: SELECT_B_PREANCHOR_L73_PLUS_ADDITIVE_SELECTED_SHELL
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: c69ff0f4939978f4d2e1eb57466ccb84113a743d
  PIN_VERIFIED: true
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  REQUEST_DATE: 2026-08-20

INPUT_MEASUREMENT:
  ARBITRARY_PAIRINDEX_USE_POINTS: 54
  ARBITRARY_PAIRINDEX_FILES: 11
  SELECTED_PAIRINDEX_USE_POINTS: 6
  SELECTED_PAIRINDEX_FILES: 1
  MEASUREMENT_ACCEPTED: true

DECISION:
  A_INVASIVE_RECORD_NARROWING:
    verdict: REJECT
    reason: FULLY_GREEN_11_FILE_54_POINT_REFACTOR
    old_cost: 5/10
    revised_cost: 8/10

  A_ADDITIVE_SELECTED_SHELL:
    verdict: KEEP_AS_PACKAGING_AFTER_B
    competing_analytic_route: false
    estimated_cost: 2/10
    existing_green_layer_changed: false

  B_DIRECT_TO_CURRENT_SELECTED_MUNTZ_APPROXIMATION:
    verdict: KILL_CIRCULAR
    reason: CURRENT_SELECTED_OBJECT_ALREADY_REQUIRES_PROLATE_CANONICAL_SOURCE_DATA

  B_PREANCHOR_CCM_LEMMA_7_3:
    verdict: SELECT
    gross_cost: 4/10
    already_scheduled_as_G6_N1: true
    marginal_N0_cost_before_packaging: 1/10

  THIRD_ALL_INDEX_TRIALNONZERO:
    verdict: REJECT_AS_OVERSTRONG
    reason: REQUIRES_EVERY_M_AND_EVERY_N_NOT_EVENTUAL_SELECTED_FAMILY
    estimated_cost: 9/10

  THIRD_SELECTED_TRIALNONZERO:
    verdict: ABSORBED_IN_B_ZERO_MODE_COROLLARY

CLOSES:
  - N0_REPAIR_TOTAL_COST_ADJUDICATION
OPENS: []

TARGET_TRANSACTION:
  NAME: G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL
  CLOSES:
    - CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT
    - SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING
  OPENS: []
  REMAINS_OPEN:
    - SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY

MINIMAL_MISSING_IDENTITY: >-
  For the unnormalized pre-anchor source trial, prove that its Gwin value at
  z=0 equals sqrt(L_m) times the V0 overlap; use exact preservation of the V0
  overlap by Galerkin projection to infer selected TrialNonzero and nonzero
  normalized rawFplus(0) from the pre-anchor CCM Lemma-7.3 limit.

REGISTERED_PREDICTIONS:
  P_N0_B0:
    statement: the z=0 Galerkin Mellin defect is exactly zero because V0 belongs to every finite carrier
    probability: 0.92
    fate: PENDING
  P_N0_B1:
    statement: CCM Lemma 7.3 can be ported before anchor normalization with a source-defined nonzero scalar/gauge
    probability: 0.75
    fate: PENDING
  P_N0_B2:
    statement: a new selected roof view can avoid edits to the 11-file arbitrary-index layer
    probability: 0.80
    fate: PENDING

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
```

## ROUTE MAP

### 1. The tree measurement changes the cost verdict

The measurement is decisive. `ProlateKTrialSourceData` is an all-index record:
it stores `pair`, same-`m` source coherence, `lambda_eq`, `eStar_memLp`, and
`trialNonzero` for every `PairIndex`. The outer
`ProlateCanonicalSourceData` additionally stores a global `CanonicalData` and
a global equality of coefficient families.

Therefore replacing that record by a selected-only record is not a five-point
local change. As an invasive repair it is a migration of a green source layer.
The revised cost is `8/10`, with the main cost coming from regression risk and
semantic review, not from the number of Lean lines.

The old `5/10` estimate is retained only for the different interpretation:
**add a parallel selected view and leave the existing all-index layer frozen**.
That view is useful, but it does not prove nonvanishing. It is packaging after
the analytic result, not a competing repair.

### 2. Direct B is circular in the current API

The current selected objects

```text
selectedPairIndex
selectedGwinTransformCoordinate
selectedTrialNormalizer
selectedMuntzApproximation
```

all take

```lean
S : ProlateCanonicalSourceData
```

as input. That type already contains `trialNonzero` and a `CanonicalData.parent`
landing in `CentralIndex`.

Hence the theorem

```text
CCM Lemma 7.3 for selectedMuntzApproximation S
```

cannot be used to construct `S`: it presupposes the object whose hidden
nonvanishing it is meant to prove. This is a C04/C10 type-and-object kill.

The repair is to port Lemma 7.3 one layer earlier, to the literal unnormalized
full source object

```text
prolateCombination
  -> E_star
  -> gTrial_m
  -> full Mellin / Gwin
```

which needs `eStar_memLp` but neither `TrialNonzero` nor `CentralIndex`.

### 3. At z=0 the finite defect should disappear exactly

The crucial simplification is stronger than the previous
"limit plus small finite defect" plan.

For every finite carrier, the zero logarithmic Fourier mode `V0` belongs to
`E_m_N`. Orthogonal projection therefore preserves its overlap exactly:

\[
\langle V_0,P_{m,N}g_m\rangle
=
\langle V_0,g_m\rangle.
\]

The pre-anchor full Mellin/Gwin value at zero is the window integral, hence the
required exact identity is

\[
Gwin(h_m,\lambda_m,0)
=
\sqrt{L_m}\,\langle V_0,g_m\rangle.
\]

Consequently

\[
Gwin(h_m,\lambda_m,0)\ne0
\Longrightarrow
P_{m,N}g_m\ne0
\quad\text{for every }N,
\]

and, after applying the exact positive trial normalizer,

\[
rawFplus_{m,N}(0)
=
\|P_{m,N}g_m\|^{-1}Gwin(h_m,\lambda_m,0)
e0.
\]

No compact-open Galerkin defect estimate is needed at `z=0`. The genuinely new
compact-decay wall remains necessary for general `z`, but not for constructing
the anchor locus.

### 4. Why Lemma 7.3 supplies eventual central nonvanishing

The paper theorem gives locally uniform convergence of the pre-anchor trial
transform, after its exact source normalization, to `Xi` on closed substrips.
In particular it applies at `z=0`, where the target is nonzero.

The project port must expose the normalization explicitly. It is sufficient to
produce a source-defined factor `a_k` with `a_k != 0` and

\[
a_k\,Gwin_k \longrightarrow \Xi
\]

locally uniformly. Eventual nonvanishing of the product at zero and `a_k != 0`
then imply eventual nonvanishing of `Gwin_k(0)` itself. No lower or upper bound
on `a_k` is needed for this particular conclusion.

After discarding a finite prefix, the same precommitted `(m_k,N_k)` path has:

```text
exact source pair;
exact E_star MemLp;
TrialNonzero;
rawFplus(0) != 0;
cofinality.
```

This is exactly `SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING`.

### 5. How the additive selected shell avoids the 54 points

Do not modify `ProlateKTrialSourceData` or `ProlateCanonicalSourceData`.

Instead define one new selected source object whose carrier is the already
precommitted path:

```lean
structure SelectedProlatePreAnchorData where
  index : ℕ → PairIndex
  mCofinal : Tendsto (fun k => (index k).m) atTop atTop
  nCofinal : Tendsto (fun k => (index k).N) atTop atTop
  pair : ℕ → ProlatePair
  lambda_eq : ∀ k, (pair k).pw.lambda = lambda_m (index k)
  eStar_memLp : ∀ k,
    MemLp
      (E_star (prolateCombination (pair k))) 2
      (dStar.restrict (I_m (index k)))
```

After the pre-anchor limit and zero-mode bridge, enrich the same path with
proved fields:

```lean
structure SelectedProlateCofinalSourceData
    extends SelectedProlatePreAnchorData where
  trialNonzero : ∀ k,
    TrialNonzero (index k)
      (prolateCombination (pair k)) (eStar_memLp k)
  rawZeroNonzero : ∀ k, selectedRawFplusPath ... k 0 ≠ 0
```

Then construct directly

```lean
selectedProlateCanonicalApproximation :
  SelectedProlateCofinalSourceData → CanonicalApproximation ℕ
```

with `parent = id`, the frozen cofinal proposition, and the centered selected
raw transform as `Pstar.family`.

The roof is polymorphic in its index type, so this does not require changing
`CanonicalRHRouteSkeleton`. Existing all-index D0Pstar modules remain frozen.
Only the selected terminal adapters are added. The selected view must carry a
definitional or proved equality to the literal source rows on the path; it may
not introduce a second family or schedule.

This is the non-invasive form of A. It is mandatory packaging after B, not an
alternative to B.

### 6. The third route

The statement

```text
production pair supplies TrialNonzero for every PairIndex
```

is strictly stronger than repaired B.

Lemma 7.3 gives an eventual/cofinal source-transform result. The all-index
record asks for every `m >= 2` and every finite cutoff `N`, including the finite
prefix. Although the zero-mode identity removes dependence on `N`, it still
requires a nonzero full central value for every `m`, not merely eventually.

Therefore the all-index third route is not "the same analysis without the
bonus". It is a stronger quantifier, at least as hard as B, and it receives no
G6-N1 payoff. It is rejected.

If "dostroit do TrialNonzero" means only the selected tail, it is not a third
route at all. It is the exact zero-mode corollary inside repaired B.

## FINAL PROPOSAL

Select the following single transaction:

```text
G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL
```

### Phase B0 — pre-anchor object lock

Use the exact selected Ferrers source pair, `lambda_m`, and `E_star MemLp`, but
do not assume or mention `TrialNonzero`, `CentralIndex`, `selectedTrialNormalizer`,
or `selectedCenteringFactor`.

### Phase B1 — exact zero-mode bridge

Prove source-parametric theorems of the following mathematical types:

```lean
preAnchorGwin_zero_eq_sqrtL_mul_innerV0

trialNonzero_of_preAnchorGwin_zero_ne

selectedRawFplusPath_zero_eq_invNorm_mul_preAnchorGwin_zero
```

The third theorem is stated only after the second has constructed the legal
`TrialNonzero` witness.

### Phase B2 — CCM Lemma 7.3 pre-anchor port

Prove the exact source-line, coordinate and normalization crosswalk and obtain
a locally uniform limit for a nonzero source-normalized pre-anchor Gwin family.
The proof must not divide by `rawFplus(0)` and must not take
`ProlateCanonicalSourceData` as an input.

### Phase B3 — tail extraction and selected shell

Use `Xi(0) != 0` to obtain eventual Gwin nonvanishing, discard one finite prefix,
prove `TrialNonzero` and raw central nonvanishing on the frozen tail, and build
the additive `CanonicalApproximation ℕ` view.

### Success condition

The transaction closes both catalog inputs:

```text
CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT
SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING
```

and exports no new analytic premise. The next wall remains exactly:

```text
SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY
```

## STRONGEST ATTACK

The strongest failure mode is normalization circularity:

> The alleged pre-anchor Lemma-7.3 port may secretly normalize by the same
> `rawFplus(0)` whose nonvanishing it is supposed to prove.

That is fatal. The port must use only the paper/source normalization of the
unprojected trial line and prove its multiplier nonzero independently. A
numerically fitted scalar, the production centering factor, or a theorem whose
input already contains `CentralIndex` is rejected under C04/C10.

A second attack is API duplication: the selected shell may quietly recreate
all 54 arbitrary-index definitions under new names. The transaction passes
only if the old eleven files remain byte-unchanged and the new selected layer
contains terminal adapters rather than a parallel copy of the D0Pstar stack.

## CODEX DIRECTIVE

```text
TASK:
  G6_N1_ZERO_MODE_PREANCHOR_PREFLIGHT

MODE:
  READ_ONLY_FIRST. Do not edit Lean until the exact heads below are extracted.

SOURCE PIN:
  c69ff0f4939978f4d2e1eb57466ccb84113a743d

REQUIRED OUTPUT:
  1. Exact #check-ready head for
       Gwin(h, lambda_m i, 0)
       = sqrt(L_m i) * inner(V_n_m i 0, gTrial_m i h hLp).

  2. Exact #check-ready head deriving
       TrialNonzero i h hLp
     from the nonzero Gwin value, using V0_mem_E_m_N and
     inner_V0_gTrial_m_N_eq.

  3. Exact #check-ready head for the normalized projected raw transform at
     zero as the positive inverse projected norm times the pre-anchor Gwin
     value. Confirm that the z=0 Galerkin Mellin defect is definitionally or
     theorem-level exactly zero.

  4. Extract the exact CCM Lemma-7.3 source normalization, coordinate and
     closed-substrip quantifiers. State the pre-anchor project theorem without
     ProlateCanonicalSourceData, CentralIndex or rawFplus normalization.

  5. Produce one frozen cofinal schedule interface and the finite-prefix tail
     extraction preserving both m- and N-cofinality.

  6. Give an additive selected-carrier API and list every downstream adapter
     required. Confirm by grep that none of the existing 11 arbitrary-index
     files must change.

  7. Return exactly one:
       G6_N1_PREANCHOR_ZERO_MODE_ROUTE_SOURCE_LOCKED
       G6_N1_PREANCHOR_NORMALIZATION_CIRCULAR
       G6_ZERO_MODE_PROJECTION_DEFECT_NOT_EXACT
       G6_SELECTED_SHELL_REQUIRES_GREEN_LAYER_REFACTOR

FORBIDDEN:
  - using selectedMuntzApproximation S before S exists;
  - editing ProlateKTrialSourceData or ProlateCanonicalSourceData;
  - assuming TrialNonzero or CentralIndex;
  - fitted scalar or phase;
  - numerical nonzero samples as proof;
  - using N2 compact-decay as a substitute for the exact z=0 identity;
  - opening a new free compact-rate premise.

IF LEAN SOURCE IS LATER AUTHORIZED:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/<owned-file>.lean
    lake build Q3.Proofs.RouteB.<OwnedModule>
  WORKDIR repo root:
    scripts/q3_check.sh Q3/Proofs/RouteB/<owned-file>.lean
  EXPECTED AXIOMS:
    [propext, Classical.choice, Quot.sound]
```

## META CLOSEOUT

**What became smaller?**

The apparent A/B refactor choice became one exact path:

```text
pre-anchor L7.3
+ exact zero mode
+ additive selected roof view.
```

**What was killed?**

- invasive 54-point narrowing of the green all-index record;
- direct circular port to `selectedMuntzApproximation`;
- all-index `TrialNonzero` as the next target;
- use of general compact-decay machinery at `z=0`.

**What must not be tried again?**

Do not normalize the pre-anchor source by `rawFplus(0)`, and do not alter the
old all-index source layer merely to express a selected theorem.

**Current smallest named gap?**

```text
PREANCHOR_CCM_L73_NORMALIZATION_AND_ZERO_MODE_CROSSWALK
```

**Next cheapest decisive test?**

Prove or refute the exact zero-mode identity and the exact vanishing of the
Galerkin Mellin defect at `z=0` before porting any paper limit.

**Fate of prior registered predictions?**

No prior N0-specific prediction is rescored. The three predictions in this
verdict are new and remain pending.

**Memory entry**

```yaml
iteration:
  target: N0 repair total-cost choice
  status: PROGRESS
  failed_strategy: invasive_selected_record_narrowing
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: PREANCHOR_CCM_L73_NORMALIZATION_AND_ZERO_MODE_CROSSWALK
  invariant_learned: >-
    zero-mode Galerkin projection preserves the anchor exactly; general compact
    decay is unnecessary for central nonvanishing
  forbidden_future_move: >-
    do not port Lemma 7.3 through an object that already contains CentralIndex
  next_decisive_test: >-
    exact pre-anchor Gwin(0)-V0 identity plus z=0 residual cancellation
```
