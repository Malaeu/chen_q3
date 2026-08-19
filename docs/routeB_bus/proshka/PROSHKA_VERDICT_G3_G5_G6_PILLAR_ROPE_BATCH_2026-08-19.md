# STATUS: CONDITIONAL — CVS FITS THE H2B TYPE BUT NOT THE CURRENT TRIAL VALUE; G5 PREDICTS TWO ROPES; G6 NEEDS A PAPER LIMIT PORT AND A NEW COMPACT-DECAY INPUT

```yaml
PRIMARY: ADJUDICATE_G3_G5_G6_PILLAR_ROPE_BATCH
PRIMARY_COUNT: 3

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: c91f3a4aa765b80693456b0f01c86ee1888dde3e
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  BATCH: 2026-08-19_EVENING
  CHAIN_GAP_DESIGN_READ: false
  HEAD_MESSAGE_EXPOSED_PRELIMINARY_G5_COUNT: true

DELIVERY:
  DOC_ONLY: true
  LEAN_WRITTEN: false
  ARISTOTLE_CALLED: false
  CODEX_CALLED: false

CLOSES:
  - G3_CVS_INTERFACE_AND_PORT_MEASUREMENT
  - G5_CENTERED_CRITICAL_MOMENT_ROPE_MEASUREMENT
  - G6_TO_SLOT_S2_EDGE_MEASUREMENT
OPENS: []

V1_G3:
  VERDICT: TYPE_LEVEL_YES_CURRENT_VALUE_LEVEL_NO
  PRODUCTION_TYPE_CHANGE_REQUIRED: false
  CURRENT_CANONICAL_APPROXIMATION_DROP_IN: false
  CVS_PROOF_REFORMALIZATION_REQUIRED: false
  ACTUAL_MISSING_FASTENING: GROUND_CANONICAL_PSTAR_VALUE_CROSSWALK
  REMAINS_OPEN:
    - G3_CONCRETE_THEOREM510_REAL_ZERO_BRIDGE_SUPPLIER

V2_G5:
  PREDICTED_MINIMAL_ROPES: 2
  PREDICTION_PROBABILITY: 0.72
  ALTERNATIVE_THREE_ROPES_PROBABILITY: 0.24
  OTHER_COUNT_PROBABILITY: 0.04
  NUMERICAL_FACTS_REQUIRED: 0
  BLINDNESS_CLASS: THEOREM_SHAPE_INDEPENDENT_COUNT_METADATA_CONTAMINATED
  ROPES:
    - CENTERED_WINDOW_WEIGHTED_MOMENT_BUDGET
    - COFINAL_SOURCE_MASS_TO_CENTER_RATIO

V3_G6:
  VERDICT: EDGE_NOT_BUILDABLE_FROM_CURRENT_REPRESENTATION_LEMMAS_ALONE
  MINIMAL_TOP_LEVEL_NODES: 5
  PAPER_PORT_REQUIRED: CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT
  NEW_ANALYTIC_INPUT_REQUIRED: SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY
  FIRST_DEPENDENCY: PROLATE_CANONICAL_SOURCE_DATA_SUPPLY
  FIRST_BY_PRICE_AFTER_OBJECT_LOCK: CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT
  FIRST_GENUINELY_NEW_ANALYTIC_WALL: SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY
  REMAINS_OPEN:
    - PROLATE_CANONICAL_SOURCE_DATA_EXISTENCE
    - SelectedTrialNormalizerBounded
    - SelectedPhysicalFourierEnergyControl
    - SelectedPhysicalBandwidthCofinal
    - G6_S2_D0_SELECTED_FAMILY_MUNTZ_SAME_FAMILY_CROSSWALK
    - SlotS2

REGISTERED_PREDICTIONS:
  P_BATCH_G3:
    statement: no production type declaration must change, but the current trial-valued C cannot be certified by the CvS ground theorem without a new exact value crosswalk
    probability: 0.93
  P_BATCH_G5:
    statement: the minimal independent decomposition has exactly two ropes and no numerical theorem
    probability: 0.72
  P_BATCH_G6:
    statement: after existing representation crosswalks, the strict edge reduces to one paper trial-limit port, one compact-open finite-error wall, and two cheap assemblies
    probability: 0.68

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C12_BOUNDED_POTENTIAL_EXCLUSION

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5
```

## 1. Source and blindness audit

The pinned branch already states that the roof waits on four pillars `G2`, `G3`, `G5`, and `G6`, and that the two unmeasured locations are the `G5` pillar and the `G6 → SlotS2` fastening. `[COFINAL_FAMILY][PAPER]`

I did not open `docs/cartographer/CHAIN_GAP_DESIGN.md`. However, the pinned commit message itself exposes the preliminary owner estimate “about two ropes” for `G5`. Therefore the decomposition below is independent at the theorem-shape level, but the numerical count is not a genuinely blind prediction. This contamination is recorded rather than hidden. `[ABSTRACT][PAPER]`

The Arsenal mandate is accepted. The decisive object-mismatch kill below instantiates **C04** and **C10**; the schedule guards instantiate **C09**; any bound used to exclude collapse must be independent of the selected cluster, per **C12**. `[ABSTRACT][PAPER]`

---

## 2. V1 — CVS-QFRZ-2025 as the `G3` fastening

### Decision

```text
TYPE LEVEL:
  YES.

CURRENT PRODUCTION VALUE:
  NO.
```

No declaration in `CanonicalRHRouteSkeleton.lean` must change. The existing interface

```lean
Theorem510RealZeroBridge C H2aAt :=
  ∀ i, H2aAt i → Differentiable ℂ (C.Pstar.family i) →
    ZerosRealOn Set.univ (C.Pstar.family i)
```

is already broad enough to host the Connes–van Suijlekom conclusion. `[ABSTRACT][LEAN]`

But the theorem is not a drop-in supplier for the current value

```lean
canonicalApproximation D
```

because that value fixes

```lean
C.Pstar.family i = centeredPstarFamily D.kTrial i
```

and `D.kTrial` is the normalized projected prolate **trial** row. CvS proves real zeros for the Fourier transform of the actual simple, isolated, even **ground eigenfunction**. Existence of a separate ground vector says nothing about the zeros of the preselected trial transform. Applying the paper theorem directly to the current value would be a **C04 same-interface/different-object error** and a **C10 functional-surrogate error**. `[COFINAL_FAMILY][LEAN] [C04] [C10]`

Thus the exact mismatch is not the Lean type. It is the value inhabiting the type.

### Exact interface mismatch

| Layer | CvS input/output | Current Q3 consumer | Mismatch | Tags |
|---|---|---|---|---|
| Spectral object | Lower-bounded essentially selfadjoint form; simple isolated minimum; even ground `xi` | Arbitrary proposition `H2aAt i`; no vector or operator appears in the interface | A local adapter must extract or store the literal CCM ground package | `[ABSTRACT][PAPER]` |
| Function | Ordinary Fourier transform of that same ground eigenfunction | The already-fixed `C.Pstar.family i` | Current production value is trial-derived, not definitionally the ground transform | `[COFINAL_FAMILY][LEAN]` |
| Finite coordinate | CvS §5 uses the ground coefficient row and its Lagrange polynomial | Q3 uses the exact P59 carrier, pole orientation and coordinate `-L*z/(2*pi)` | Exact carrier, sign and P59 factor crosswalk is required | `[FINITE_CELL][LEAN]` |
| Normalization | Ground eigenfunction is normalized in the paper’s form/anchor convention | `centeredPstarFamily` uses `centeredXi 0 / rawFplus 0` | The scalar must be proved nonzero and zero-preserving; “up to scalar” is insufficient | `[COFINAL_FAMILY][CONDITIONAL]` |
| Quantifier | One ground object, then finite/infinite approximation in the paper | Every selected index of one precommitted `CanonicalApproximation` | The same `C`, parent and extraction must be retained | `[COFINAL_FAMILY][LEAN] [C09]` |

### What of the CvS proof is already on the shelf

The shortest applicable route is the finite real-spectral route of CvS §5, not the C*-algebraic Carathéodory–Fejér route. The latter is historically important but unnecessary for this production interface. `[ABSTRACT][PAPER]`

| CvS proof module | Current repository status | Existing machinery | Tags |
|---|---|---|---|
| 1. Parity and source commutator | **HAVE** | `CCMFiniteWeilParity`, `CCMFiniteWeilShiftedRankOne` | `[FINITE_CELL][LEAN]` |
| 2. Rank-one correction kills the calibration vector and is self-adjoint for the form | **HAVE** | `RankOneCorrectionWeightedSymmetry` | `[ABSTRACT][LEAN]` |
| 3. Quotient by the radical, induced PosDef metric, real spectrum | **HAVE** | quotient-by-radical files, `MatrixBilinFormRadical`, `PosDefSelfAdjointRealSpectrum` | `[ABSTRACT][LEAN]` |
| 4. Determinant/charpoly to Lagrange real-root transfer | **HAVE by an equivalent shorter route** | quotient/radical charpoly and `RankOneCorrectionLagrangeRealZeros` | `[FINITE_CELL][LEAN]` |
| 5. Fourier/P59 pole and lattice zero transfer | **HAVE for the finite production transform** | `Proposition59GroundLagrangeZeroSetBridge` | `[FINITE_CELL][LEAN]` |

The paper’s infinite-dimensional Hurwitz passage is not needed to inhabit `Theorem510RealZeroBridge`: the roof asks for real zeros of each finite selected function and performs its own cluster/zero-escape step later. `[ABSTRACT][LEAN]`

### Minimal port list

#### G3-P0 — `H2aAtGroundPackage`

```yaml
CHARACTER: PORT
CLOSES:
  - H2A_TO_LITERAL_CCM_GROUND_DATA
OPENS: []
```

Define `H2aAt` so that it carries the exact `m`, `N`, `epsilon`, ground row `xi`, eigen-equation, bottom Rayleigh inequality, one-dimensional eigenspace and legal normalization consumed by the existing finite bridge. This can be a structure/definition rather than a new theorem. `[FINITE_CELL][LEAN]`

#### G3-P1 — `GroundCanonicalPstarValueCrosswalk`

```yaml
CHARACTER: PORT_AND_OBJECT_LOCK
CLOSES:
  - GROUND_CANONICAL_PSTAR_VALUE_CROSSWALK
OPENS: []
```

Construct a ground-valued `CanonicalApproximation` using the existing production types, or prove an exact equality between the selected production function and a nonzero zero-free factor times the literal `proposition59CCMTransform` of the same ground row. For the current trial-valued `canonicalApproximation D`, this equality is not available and must not be postulated. `[COFINAL_FAMILY][CONDITIONAL] [C04] [C10]`

#### G3-P2 — `Theorem510RealZeroBridge_of_groundP59`

```yaml
CHARACTER: ASSEMBLY
CLOSES:
  - G3_CONCRETE_THEOREM510_REAL_ZERO_BRIDGE_SUPPLIER
OPENS: []
```

Invoke `Proposition59GroundLagrangeZeroSetBridge`, then transport zeros through the proved nonzero normalization factor. No new CvS mathematics is required here. `[COFINAL_FAMILY][CONDITIONAL]`

### V1 closeout

`CVS-QFRZ-2025` is therefore a **ready theorem engine**, not a ready fastening for the current trial-valued `C`. The production type is correct; the ground-family value crosswalk is the only load-bearing fastening still missing. `[COFINAL_FAMILY][CONDITIONAL]`

---

## 3. V2 — independent decomposition of `CenteredTrialCriticalMomentRatio`

### Prediction

\[
\boxed{\text{two independent ropes}}
\]

Prediction distribution, registered before reading `CHAIN_GAP_DESIGN.md`:

```text
2 ropes: 0.72
3 ropes: 0.24
other:   0.04
```

The count is metadata-contaminated by the pinned commit message, but the following decomposition was derived directly from the Lean statement. `[ABSTRACT][PAPER]`

`PairCofinal` is already a field of the contract and of `CanonicalData`; it is not a new analytic rope. The finite initial prefix also does not require a numerical theorem: once an eventual bound exists, finitely many early indices can be absorbed into `C_sigma`. `[COFINAL_FAMILY][LEAN]`

### Rope G5-A — centered-window weighted moment budget

```yaml
CHARACTER: SCALE_LEMMA
CLOSES:
  - CENTERED_WINDOW_WEIGHTED_MOMENT_BUDGET
OPENS: []
NUMERICAL_FACT: false
```

Produce a bound for

\[
\int_{-L_m/2}^{L_m/2}
  |q_{m,N}(t)| e^{\sigma |t|}\,dt
\]

in terms of one source-controlled norm or mass, with the complete dependence on `L_m`, `N` and `sigma` explicit. This is the deterministic window/weight bookkeeping. The existing `rawFplus_norm_le_centeredCriticalMoment` then turns it into the exact strip bound consumed by Montel. `[ABSTRACT][CONDITIONAL]`

### Rope G5-B — cofinal source mass-to-center ratio

```yaml
CHARACTER: COFINAL_SOURCE_ESTIMATE
CLOSES:
  - COFINAL_SOURCE_MASS_TO_CENTER_RATIO
OPENS: []
NUMERICAL_FACT: false
```

Prove that the same source norm or mass is uniformly dominated, along the precommitted parent path, by

\[
|rawFplus(0)| = \sqrt{L_m}\,|c_0|.
\]

This is the substantive source estimate. Unit norm of the projected vector does not lower-bound one Fourier coefficient, so this rope cannot be obtained from normalization alone. `[COFINAL_FAMILY][CONDITIONAL] [C12]`

### Why no numerical rope

A finite computation may falsify a proposed uniform constant or calibrate its scale. It cannot occupy the quantifier

```text
forall k
```

inside `CenteredTrialCriticalMomentRatio`. Therefore the minimal proof ledger contains **zero numerical facts**. `[COFINAL_FAMILY][PAPER]`

### Three-rope contingency and discriminator

A third rope is needed only if the usable source estimate is proved for the unprojected continuum trial while the contract is about the finite projected density. Then one must separately prove:

```text
FINITE_PROJECTION_PRESERVES_MOMENT_AND_CENTRAL_COEFFICIENT_RATIO.
```

The discriminator is exact: derive the proposed source norm and inspect whether both the numerator and `c_0` already refer to `kTrial_(m,N)`. If yes, the count is two. If they refer to the continuum trial and require an independent Galerkin transport, the count is three. `[COFINAL_FAMILY][CONDITIONAL]`

### V2 closeout

The predicted minimal character is:

```text
1 scale lemma
+ 1 cofinal source estimate
+ 0 numerical theorems.
```

The three existing consumers do not create additional ropes; they are downstream assemblies already proved. `[COFINAL_FAMILY][LEAN]`

---

## 4. V3 — minimal edge from `D0Pstar*` to literal `SlotS2`

### Current endpoint

The representation layer is much further advanced than the old Phase-0 map:

- the production source row is tied to the prolate trial by `ProlateCanonicalSourceData`;
- the centered coordinate and sign are locked;
- `selectedFamily` is exactly `selectedMuntzApproximation + finite Galerkin defect`;
- the scalar defect is identified with the Mellin coordinate of the literal normalized object residual;
- the full Mellin coordinate is identified with `Gwin`;
- the zeta-to-Xi gauge and its nonvanishing are proved.

`[ABSTRACT][LEAN]`

But none of these representation theorems proves a compact-open limit. `SelectedProjectionTailDecay` is only an `H_m` norm statement, and even that still depends on explicit suppliers. Analyticity of `Rminus` and `Rplus` is not tail smallness. The literal `SlotS2` quantifies over **every** `ClusterData C`, not one chosen cluster. `[COFINAL_FAMILY][LEAN] [C10]`

Therefore the edge is not buildable from current representation lemmas alone.

### Minimal top-level sequence

#### G6-N0 — `ProlateCanonicalSourceDataSupply`

```yaml
CHARACTER: OBJECT_CONSTRUCTION_WALL
CLOSES:
  - PROLATE_CANONICAL_SOURCE_DATA_EXISTENCE
OPENS: []
DEPENDENCY_ORDER: 1
COST: 6/10
```

Construct an actual term of `ProlateCanonicalSourceData` on the production schedule: source modes/pairs, exact `lambda_m`, `MemLp`, `TrialNonzero`, coefficient-family equality, parent and extraction. The existing structure proves provenance only after such data are supplied. `[COFINAL_FAMILY][CONDITIONAL]`

#### G6-N1 — `CCMLemma73SelectedMuntzLimit`

```yaml
CHARACTER: PAPER_PORT_AND_NORMALIZATION_CROSSWALK
CLOSES:
  - SELECTED_MUNTZ_APPROXIMATION_TO_XI_GAUGE_LOCALLY_UNIFORM
OPENS: []
DEPENDENCY_ORDER: 2
COST: 4/10
```

Port CCM Lemma 7.3 to the exact `selectedMuntzApproximation` object, including the one-dimensional source-line scalar, centered sign, anchor normalization and the same `parent (extract k)` schedule. This is the first node by cost after the object lock because the analytic convergence is already paper-proved. `[COFINAL_FAMILY][PAPER] [C04] [C09]`

#### G6-N2 — `SelectedNormalizedGalerkinMellinCompactDecay`

```yaml
CHARACTER: NEW_ANALYTIC_WALL
CLOSES:
  - SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY
OPENS: []
DEPENDENCY_ORDER: 3
COST: 8/10
```

Prove, for every compact `K` in the centered strip,

\[
\sup_{z\in K}
|selectedGalerkinResidualMellinCoordinate\;S\;k\;z|
\longrightarrow 0.
\]

The theorem must close its own compact-evaluation rate. It may consume the existing exact residual crosswalk and may internally use:

```text
SelectedTrialNormalizerBounded
SelectedPhysicalFourierEnergyControl
SelectedPhysicalBandwidthCofinal
```

but it must not export a new free `COMPACT_MELLIN_EVALUATION_RATE` and call that progress. If the compact rate cannot be proved in the same transaction, W9 rejects the source. `[COFINAL_FAMILY][CONDITIONAL]`

This is the first genuinely new analytic input. The current theorem `selectedProjectionTailDecay_of_physicalFourierEnergyControl` reaches only Hilbert-norm projection decay; it does not by itself control Mellin evaluation uniformly on compacta. `[COFINAL_FAMILY][LEAN]`

#### G6-N3 — `D0PstarToMuntzSameFamilyLocallyUniformCrosswalk`

```yaml
CHARACTER: ASSEMBLY
CLOSES:
  - G6_S2_D0_SELECTED_FAMILY_MUNTZ_SAME_FAMILY_CROSSWALK
OPENS: []
DEPENDENCY_ORDER: 4
COST: 2/10
```

Combine the exact decomposition

```text
selectedFamily
  = selectedMuntzApproximation
  + centeredFactor * literalResidualCoordinate
```

with G6-N1 and G6-N2. The output is one fixed locally uniform limit for the literal selected production family on the same schedule. `[COFINAL_FAMILY][CONDITIONAL]`

#### G6-N4 — `SlotS2_of_fixed_selected_limit`

```yaml
CHARACTER: STRICT_CONSUMER_ASSEMBLY
CLOSES:
  - SlotS2
  - G6
OPENS: []
DEPENDENCY_ORDER: 5
COST: 2/10
```

For an arbitrary `D : ClusterData C`, compare `D.convergence` with the fixed limit from G6-N3. Uniqueness of locally uniform limits gives equality of `D.limit` with the fixed `c * centeredXi * gamma`; `S2GaugeNonvanishing` supplies the zero-free gauge and the anchor supplies `c != 0`. This preserves the every-`ClusterData` quantifier. `[COFINAL_FAMILY][CONDITIONAL]`

### Price order versus dependency order

The cheap generic assemblies G6-N3 and G6-N4 must **not** be written first. They would merely assume the two missing limits and would repeat the bridge-splitting failure prohibited by W9.

```text
First dependency:
  G6-N0 — actual source data.

First by proof cost after object lock:
  G6-N1 — the CCM Lemma 7.3 port.

First genuinely new analytic wall:
  G6-N2 — compact-open decay of the normalized Galerkin residual.
```

`[COFINAL_FAMILY][PAPER]`

### Two admissible representations

#### R1 — fixed-limit route

```yaml
KILL_POWER: 10/10
COST: 6/10
```

Port Lemma 7.3 for the exact main term, prove compact residual decay, then obtain a unique fixed limit for the whole selected family. This is primary. `[COFINAL_FAMILY][CONDITIONAL]`

#### R2 — cluster-wise Müntz identification

```yaml
KILL_POWER: 8/10
COST: 7/10
```

For each supplied `ClusterData`, compare its convergent subsequence directly with the exact Müntz decomposition and identify that cluster. This avoids stating whole-family convergence, but it must repeat the every-cluster and same-subsequence bookkeeping. It is a runner-up, not a license to select one convenient cluster. `[COFINAL_FAMILY][CONDITIONAL] [C09]`

**Discriminator:** whether CCM Lemma 7.3 ports to the complete production sequence with exact normalization. If yes, R1 dominates. If only subsequential convergence is available, R2 becomes necessary. A zero-consistent or merely bounded tail result is inconclusive; the discriminator is strict compact-open convergence to zero. `[COFINAL_FAMILY][PAPER]`

### V3 closeout

The missing edge is not one absent wrapper. It consists of:

```text
one paper-proved main-term limit port
+ one genuinely new compact-open finite-error estimate
+ two cheap assemblies.
```

The object construction is a prior dependency. No further representation bridge should be written until one of the two limit suppliers is actually closed. `[COFINAL_FAMILY][CONDITIONAL]`

---

## 5. Final proposal

### G3

Do not port the CvS C*-algebraic proof. Reuse the existing finite §5 machinery and build the exact ground-valued `Pstar` value crosswalk. No production type declaration changes. `[COFINAL_FAMILY][CONDITIONAL]`

### G5

Plan for two ropes. Attack the source mass-to-center ratio first; it is the substantive rope and can kill the route cheaply if the central coefficient collapses. The scale lemma is downstream bookkeeping once the correct source norm is selected. `[COFINAL_FAMILY][CONDITIONAL]`

### G6

After object lock, port CCM Lemma 7.3 before touching another tail proof. Then attack the normalized Galerkin residual directly in compact-open topology. Do not write the final `SlotS2` assembly until both limits exist. `[COFINAL_FAMILY][CONDITIONAL]`

---

## 6. Strongest attack

### Against V1

A theorem about the ground eigenfunction cannot certify the zeros of a nearby or similarly normalized trial function. The current `canonicalApproximation D` value is the wrong object for a direct CvS application. `[COFINAL_FAMILY][LEAN] [C04] [C10]`

### Against V2

The two-rope split is not logically unique. A direct source theorem may prove the ratio in one shot, while a continuum-to-finite proof may require a third Galerkin transfer. The exact projected-versus-continuum carrier is the discriminator. `[COFINAL_FAMILY][CONDITIONAL]`

### Against V3

Hilbert-norm residual decay need not imply compact-open Mellin decay when the evaluation norm grows with the window. The product “evaluation amplification × residual” must tend to zero. Boundedness alone is not convergence. `[COFINAL_FAMILY][CONDITIONAL] [C12]`

---

## 7. Meta closeout

**What became smaller?**

- `G3` is no longer “formalize CvS”; it is one value-level ground-family crosswalk plus assembly.
- `G5` is measured as two substantive ropes, with a precise three-rope discriminator.
- `G6` is reduced to two actual limit suppliers and two assemblies; representation crosswalks are already present.

**What was killed?**

- Drop-in use of CvS on the current trial-valued `Pstar`.
- Counting finite numerics as a `G5` rope.
- Writing another generic `SlotS2` wrapper before the limits exist.
- Treating tail analyticity or Hilbert-norm decay as compact-open tail smallness.

**What must not be tried again?**

- Do not change production types to fit the paper.
- Do not substitute the trial row for the actual ground row.
- Do not select a post-hoc cluster or subsequence.
- Do not split G6-N2 into new free supplier names unless an existing input is closed in the same transaction.

**Current smallest named gaps:**

```text
G3: GROUND_CANONICAL_PSTAR_VALUE_CROSSWALK
G5: COFINAL_SOURCE_MASS_TO_CENTER_RATIO
G6: SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY
```

**Next cheapest decisive tests:**

```text
G3:
  typecheck one ground-valued CanonicalApproximation value and the exact P59 normalization equality.

G5:
  derive the central coefficient of the selected source trial and test whether a cofinal lower envelope is even structurally possible.

G6:
  source-lock the exact CCM Lemma 7.3 normalization against selectedMuntzApproximation.
```

**Fate of prior predictions:** none were registered for this batch before the present source audit. No retroactive scoring is performed.

```yaml
iteration:
  target: G3_G5_G6_PILLAR_ROPE_MEASUREMENT
  status: PROGRESS
  failed_strategy: bridge_first_without_value_or_limit_suppliers
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: GROUND_PSTAR_CROSSWALK__G5_MASS_TO_CENTER__G6_COMPACT_RESIDUAL_DECAY
  invariant_learned: the exact function value, normalization and cofinal sequence are cargo
  forbidden_future_move: write a wrapper whose only effect is to rename an existing open input
  next_decisive_test: exact_ground_Pstar_value_typecheck_then_CCM_L73_normalization_lock
```

`CHALLENGER / NOT_RH`; Bus 010 `VOID`; Goal 055 `HOLD`; no route promotion and no RH claim.
