# STATUS: CONDITIONAL — H2A.4.1B.1 CONSUMER RECOMPUTATION RATIFIED; SOURCE-RATE CLAIM REPAIRED; H2A.4.1B.2 AUTHORIZED
```yaml
PRIMARY: RATIFY_WEIGHTED_RESIDUAL_CONSUMER_AND_AUTHORIZE_EVENTUAL_COMPLEMENT_FLOOR
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 0507bddaecf14f0e446babeb5180469b79e7ad13
  REPORT_PARENT: a08beed765e448c278dade41d4edcbc0935dced6
  REPORT_PATH: docs/routeB_bus/H2A_4_1B_1_SELECTED_FERRERS_COMBINED_CCM_ACTION_DISCRIMINATOR_2026-08-23.md
  REPORT_GIT_BLOB: 982a7ac3bfbdff83fa5bb0e01774606ca964f6b4
  REPORT_LINES: 241
  LEAN_SOURCE_CHANGED_BY_REPORT: false
  ARISTOTLE_USED: false
  NUMERICS_USED: false

PREFLIGHT_ADMISSION:
  SEPARATE_ACTION_DECAY_NOT_NECESSARY_PLANT: RATIFIED
  GENERIC_ALL_PAIRINDEX_CGRAPH_TIMES_LM: KILLED
  EXACT_COMBINED_COEFFICIENT_LOCK: RATIFIED
  STRUCTURED_CCM_COMMUTATOR_IDENTITY: RATIFIED
  TARGET_ONLY_RATE_IDENTITY: ABSENT_AT_CURRENT_SOURCE_LEVEL
  GENERIC_AMBIENT_PRIME_OPNORM_ROUTE: INSUFFICIENT
  R1_COMBINED_SELECTED_RESIDUAL: RETAIN_AS_PRIMARY_REPRESENTATION

OUTCOME_REPAIR:
  REPORTED_CODE: COMBINED_SOURCE_ACTION_RATE_CONTRACT_FOUND
  REPORTED_CODE_STATUS: REJECTED_AS_OVERCLAIM
  RATIFIED_CODE: WEIGHTED_RESIDUAL_CONSUMER_CONTRACT_FOUND
  REASON: >-
    The report found the exact weaker downstream quantity required by H2A.1,
    but it did not derive that quantity from the structured CCM source action.
    The source-rate theorem remains open.

WEIGHTED_RESIDUAL_CONTRACT:
  ODD_MASS: selectedFerrersFiniteCCMOddMass P k
  RESIDUAL_NORM: sqrt(selectedFerrersFiniteCCMResidualEnergy P k)
  CLEAN_SUFFICIENT_CONDITION: >-
    sqrt(oddMass_k) * sqrt(residualEnergy_k) tends to zero
  ABSOLUTELY_MINIMAL: false
  BETA0_INDEPENDENT_CLEAN_CONTRACT: true
  RESIDUAL_DECAY_REQUIRED: false
  PROOF_ROLE: >-
    With a fixed positive lower floor beta0 on both exact reflection sectors,
    oddMass -> 0 and the weighted residual contract force the H2A.1 effective
    floor to tend to beta0 and hence eventually dominate beta0/2.

CORRECTIONS_TO_REPORT:
  PRIME_LOG_LEDGER:
    DIRECT_RESIDUAL_REQUIREMENT_GAP: log(m)^(3/2)
    CURRENT_H2A_4_1A_ACTION_BUDGET_GAP: log(m)^2
    REASON: >-
      The estimate O(m^(1/4) log m) is for an action term before the additional
      normalizer factor t_k/|s_k| = O(sqrt(log m)).  Under the current split,
      A_k+T_k must be o(m^(1/4)/log m), not merely
      o(m^(1/4)/sqrt(log m)).

  BETA_MOMENT_PROVENANCE:
    REPORT_CLAIM: beta dot q lies inside the already proved L73 central/Mellin radius
    STATUS: REJECTED
    EXACT_OBJECT: >-
      beta dot q is the center coordinate of M(D q), equivalently the Weil
      pairing of the center mode with the mode-weighted row D q.  It is not the
      ordinary center value or the ordinary center-mode pairing of q.
    MISSING_THEOREM: SELECTED_FERRERS_BETA_MOMENT_SOURCE_CROSSWALK_OR_BOUND
    CARDS:
      - C04_SAME_COORDINATES_TWO_LAWS
      - C10_FUNCTIONAL_NOT_SURROGATE

  ETA_NOTATION_FIREWALL:
    ccmEtaFinite: all-ones commutator vector
    oddMass_eta: reflection-odd squared mass
    CONFLATION_FORBIDDEN: true

  SELECTED_GRAPH_ENVELOPE:
    status: PLAUSIBLE_NOT_PROVED
    exact_schedule: N=m=k+2 before the theorem-generated finite-prefix deletion
    generic_all_PairIndex_statement: false
    modewise_dimension_loss: forbidden

H2A_BOUNDARY_AFTER_ADJUDICATION:
  H2A_4_1A_EXACT_SOURCE_ACTION_SPLIT: CLOSED
  H2A_4_1B_0_GRAPH_PREFLIGHT: CLOSED
  H2A_4_1B_1_CONSUMER_RECOMPUTATION: CLOSED
  WEIGHTED_RESIDUAL_TO_FIXED_COMPLEMENT_FLOOR_CONSUMER: NEXT_AUTHORIZED
  WEIGHTED_RESIDUAL_SOURCE_RATE: OPEN
  UNIFORM_EVEN_SECTOR_FLOOR: OPEN
  UNIFORM_ODD_SECTOR_FLOOR: OPEN
  POSITIVE_COFINAL_COMPLEMENT_FLOOR: OPEN_UNTIL_NEXT_THEOREM_AND_SUPPLIERS
  SIMPLE_BOTTOM_GROUND: OPEN
  THEOREM_510_APPLICATION: OPEN
  REAL_ZEROS: OPEN

NEXT_AUTHORIZATION:
  CODE: H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR_LEAN
  STATUS: AUTHORIZED
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersWeightedResidualComplementFloor.lean
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_2_WEIGHTED_RESIDUAL_COMPLEMENT_FLOOR_2026-08-23.md
  DIRECT_IMPORTS_EXACT:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance
  PUBLIC_SURFACE_EXACT:
    - selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
  CLOSES:
    - SELECTED_FERRERS_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR
    - RESIDUAL_DECAY_NOT_REQUIRED_FOR_H2A_EFFECTIVE_FLOOR
  OPENS: []
  LEAN_WRITE_AUTHORIZED: true
  ARISTOTLE_AUTHORIZED: false

SUCCESS: H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR_LEAN
FAILURE: H2A_4_1B_2_FILTER_SQRT_OR_FIXED_FLOOR_DOWNGRADE_GAP

NEXT_LOAD_BEARING_GAP_AFTER_ADMISSION:
  H2A_4_1B_3_SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE

REGISTERED_PREDICTIONS:
  P_H2A41B2_1:
    claim: the_H2A1_effective_floor_tends_to_beta0_under_the_weighted_residual_contract
    probability: 0.97
  P_H2A41B2_2:
    claim: the_selected_receiver_yields_an_eventual_fixed_beta0_over_2_complement_floor
    probability: 0.93
  P_H2A41B2_3:
    claim: the_main_Lean_friction_is_Filter_eventual_sqrt_and_division_normal_form
    probability: 0.86
  LIKELIEST_FAILURE: FILTER_EVENTUAL_SQRT_EFFECTIVE_FLOOR_NORMAL_FORM

PRIOR_PREDICTION_FATES:
  P_H2A41B1_1:
    fate: CONFIRMED
  P_H2A41B1_2:
    fate: CONFIRMED
  P_H2A41B1_3:
    fate: CONFIRMED_AT_CURRENT_SOURCE_LEVEL
  P_H2A41B1_4:
    fate: CONFIRMED_WITH_LOG_EXPONENT_CORRECTION
  RETROACTIVE_REPAIR: false

ARSENAL_MANDATE:
  ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. The consumer recomputation is correct

Write

\[
\eta_k:=\operatorname{selectedFerrersFiniteCCMOddMass}(P,k),
\qquad
\rho_k:=\sqrt{\operatorname{selectedFerrersFiniteCCMResidualEnergy}(P,k)}.
\]

The H2A.1 effective floor with a common sector floor \(\beta_0>0\) is

\[
B_k
=
\beta_0(1-\eta_k)
-
\frac{2\sqrt{\eta_k}+\eta_k}{\sqrt{1-\eta_k}}\rho_k.
\]

Because \(\eta_k\ge0\),

\[
(2\sqrt{\eta_k}+\eta_k)\rho_k
=
(2+\sqrt{\eta_k})(\sqrt{\eta_k}\rho_k).
\]

Hence, if

\[
\eta_k\to0,
\qquad
\sqrt{\eta_k}\rho_k\to0,
\]

then the contamination term tends to zero and

\[
B_k\to\beta_0.
\]

Therefore \(B_k\ge\beta_0/2>0\) eventually.  This proves that plain
\(\rho_k\to0\) is unnecessary.  In particular, the H2A.3 bound

\[
\eta_k=O\!\left(\frac{\log m_k}{\sqrt{m_k}}\right)
\]

allows

\[
\rho_k=o\!\left(\frac{m_k^{1/4}}{\sqrt{\log m_k}}\right).
\]

`[COFINAL_FAMILY][PAPER]`

The condition \(\sqrt{\eta_k}\rho_k\to0\) is not the logically weakest
possible condition once a numerical value of \(\beta_0\) is known.  A small
enough positive limsup can also suffice.  It is, however, the clean
\(\beta_0\)-independent asymptotic contract and is the correct next source
quantity to expose.

### 2. The report did not prove a source-action rate

The exact combined object is indeed the selected residual

\[
(K_k-a_kI)q_k.
\]

The commutator identity preserves cancellation and therefore R1 remains the
primary representation.  But the report only identified the weaker consumer.
It did not prove

\[
\sqrt{\eta_k}\rho_k\to0
\]

from the Loewner structure, the prime sum, the target coefficients, or the L73
error.  The source-rate wall therefore remains open. `[COFINAL_FAMILY][CONDITIONAL]`

### 3. The structured beta moment is not a proved L73 moment

The exact commutator gives

\[
M(Dq)-D(Mq)
=
\mathbf 1\,(\beta\!\cdot q)-\beta\,(\mathbf 1\!\cdot q).
\]

Here \(\mathbf1=\texttt{ccmEtaFinite}\), whereas \(\eta_k\) above is the
reflection-odd mass.  These objects must not share one unqualified symbol.

Moreover,

\[
\beta\!\cdot q
=
\bigl(M(Dq)\bigr)_{\mathrm{center}},
\]

using symmetry of the source matrix.  Thus it is a derivative/mode-weighted
action quantity.  Existing central-anchor and Mellin values control the
unweighted all-ones moment and transforms of the source family; they do not,
without a new theorem, control this weighted finite Weil-action moment.

The matched signature is **C04**: an unweighted central transform value and a
mode-weighted source-action value live on the same coordinates but obey
different laws.  It is also **C10**: the L73 transform functional is not the
finite Riesz-action functional required by the consumer.

### 4. Exact correction to the prime ledger

Under H2A.3,

\[
\sqrt{\eta_k}=O\!\left(\frac{\sqrt{L_k}}{m_k^{1/4}}\right),
\qquad L_k=\log m_k.
\]

A direct bound on \(\rho_k\) would need

\[
\rho_k=o\!\left(\frac{m_k^{1/4}}{\sqrt{L_k}}\right),
\]

so comparison with \(O(m_k^{1/4}L_k)\) has thickness \(L_k^{3/2}\).

But the existing H2A.4.1A split first gives

\[
\rho_k\le O(\sqrt{L_k})(A_k+T_k).
\]

Therefore that route requires

\[
A_k+T_k=o\!left(\frac{m_k^{1/4}}{L_k}\right).
\]

Against \(O(m_k^{1/4}L_k)\), the actual missing cancellation is \(L_k^2\).
The report mixed the direct-residual and pre-normalizer ledgers.  Both remain
logarithmic rather than polynomial, but only the corrected ledger may govern a
future theorem statement.

## FINAL PROPOSAL

Formalize the exact downstream consequence before returning to source-action
analysis.  This permanently prevents future workers from over-solving the
residual problem.

The next theorem must conclude a fixed eventual floor \(\beta_0/2\), not merely
positivity of a varying expression and not merely a `Tendsto` statement.

### Exact public theorem shape

```lean
theorem selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (β0 : ℝ) (hβ0 : 0 < β0)
    (hη : Filter.Tendsto
      (fun k => selectedFerrersFiniteCCMOddMass P k)
      Filter.atTop (nhds 0))
    (hweighted : Filter.Tendsto
      (fun k =>
        Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
          Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k))
      Filter.atTop (nhds 0))
    (heven : ∀ᶠ k in Filter.atTop,
      ∀ x,
        ccmComplexReflectionMatrix
            ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = x →
        star ((2⁻¹ : ℂ) •
          (selectedFerrersFiniteCCMRow P k +
            ccmComplexReflectionMatrix
              ((selectedFerrersCofinalSourceData P).index k).N *ᵥ
                selectedFerrersFiniteCCMRow P k)) ⬝ᵥ x = 0 →
        β0 * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix
                ((selectedFerrersCofinalSourceData P).index k) -
              ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
                (1 : Matrix _ _ ℂ)) *ᵥ x)).re)
    (hodd : ∀ᶠ k in Filter.atTop,
      ∀ x,
        ccmComplexReflectionMatrix
            ((selectedFerrersCofinalSourceData P).index k).N *ᵥ x = -x →
        β0 * (star x ⬝ᵥ x).re ≤
          (star x ⬝ᵥ
            ((sourceCCMFiniteMatrix
                ((selectedFerrersCofinalSourceData P).index k) -
              ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ) •
                (1 : Matrix _ _ ℂ)) *ᵥ x)).re) :
    ∀ᶠ k in Filter.atTop,
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix
          ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        ((selectedFerrersFiniteCCMRayleigh P k : ℝ) : ℂ)
        (β0 / 2)
```

The theorem may use private helper predicates to avoid repeating the two sector
floor statements internally.  The public conclusion and quantitative constant
`β0 / 2` must remain exact.

### Proof route

1. Run `./ask.sh "weighted residual complement floor"` before editing.  Reuse an
   existing supplier if the catalog already contains this theorem under another
   name.
2. Intersect `hη`, `hweighted`, `heven`, and `hodd` eventual sets.
3. From `hη`, obtain eventually `0 ≤ η_k < 1/2`; nonnegativity is already a
   theorem from the odd-mass sum.
4. Put `ρ_k := sqrt(residualEnergy_k)` and use
   `selectedFerrersFiniteCCMResidualEnergy_nonneg` to prove
   `residualEnergy_k = ρ_k^2`.
5. Rewrite the H2A.1 contamination term as
   `((2 + sqrt η_k) / sqrt (1 - η_k)) * (sqrt η_k * ρ_k)`.
6. Prove the coefficient tends to `2`, hence the contamination term tends to
   zero by `hweighted`; prove the full effective floor tends to `β0`.
7. Obtain eventually `β0 / 2 ≤ betaEff_k`.
8. Apply
   `selectedFerrersFiniteCCMComplementFloor_of_sectorFloors_oddMass_residual`
   with `βp = βm = β0`, `ρ = ρ_k`, and the exact H2A.1 effective floor.
9. Downgrade the resulting floor from `betaEff_k` to the fixed `β0 / 2` by
   unfolding `complexTrialComplementFloor`, using nonnegativity of the projected
   norm.  Do not add a new spectral theorem.

### Mandatory plants

```text
weighted_residual_is_load_bearing_plant:
  eta_n -> 0 but sqrt(eta_n)*rho_n does not -> 0,
  and the H2A.1 effective floor fails to stay positive.

residual_decay_is_not_necessary_plant:
  eta_n = 0 and rho_n is arbitrary/unbounded,
  while the effective floor is exactly beta0.
```

The plants may be private, but `#print axioms` must include both.

### FORBIDDEN

```text
Do not assume rho_k -> 0.
Do not replace weighted residual control by odd-mass decay alone.
Do not call ccmEtaFinite the odd mass.
Do not import the source-action split into this consumer theorem.
Do not claim the theorem proves the weighted residual source rate.
Do not change the selected row, schedule, sourceScale or exact Rayleigh shift.
Do not bundle sector-floor suppliers, simple ground, Theorem 5.10 or real zeros.
Do not use sorry, admit, typed holes, a paper axiom or theorem weakening.
```

## STRONGEST ATTACK

The strongest objection is that the new `Tendsto` contract merely renames the
source-action wall.  Correct: it does not prove the weighted residual rate.  Its
value is narrower and exact: it proves that **full residual decay was never the
consumer**, and it turns any future source analysis into one scalar target with
an eventual fixed complement-floor payoff.

A second objection is that the report's commutator expansion already controls
all moments.  It does not.  The mode-weighted beta moment remains a separate
source-action quantity, and treating it as an ordinary L73 anchor value is a
C04/C10 object substitution.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR_LEAN

BASE_HEAD:
  use this Proshka verdict commit;
  run git fetch origin rh_clean and live git rev-parse HEAD before editing.

PREFLIGHT:
  ./ask.sh "weighted residual complement floor"

LEAN FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersWeightedResidualComplementFloor.lean

SOURCE RECORD:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_2_WEIGHTED_RESIDUAL_COMPLEMENT_FLOOR_2026-08-23.md

DIRECT IMPORTS — EXACTLY ONE:
  Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance

PUBLIC SURFACE — EXACTLY ONE THEOREM:
  selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual

CLOSES:
  SELECTED_FERRERS_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR
  RESIDUAL_DECAY_NOT_REQUIRED_FOR_H2A_EFFECTIVE_FLOOR

OPENS:
  []

GATE:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersWeightedResidualComplementFloor.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersWeightedResidualComplementFloor

  WORKDIR repository root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersWeightedResidualComplementFloor.lean

EXPECTED AXIOMS FOR THE PUBLIC THEOREM AND BOTH PLANTS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR_LEAN

FAILURE:
  H2A_4_1B_2_FILTER_SQRT_OR_FIXED_FLOOR_DOWNGRADE_GAP
```

## META CLOSEOUT

**What became smaller?**

The source-action objective changed from residual decay to the strictly weaker
weighted quantity

\[
\sqrt{\eta_k}\,\rho_k\to0.
\]

**What was killed?**

- residual decay as a necessary H2A consumer;
- the report's claim that a source-action rate had already been found;
- the claim that the beta moment is already an L73 central moment;
- the mixed `log^(3/2)` / `log^2` ledger.

**What must not be tried again?**

Do not prove separate error and target decay as a necessary route.  Do not state
a graph envelope uniform in all independent `PairIndex.N`.  Do not conflate the
all-ones commutator vector with reflection odd mass.  Do not count a weighted
finite Weil-action moment as a Mellin anchor without a crosswalk theorem.

**Current smallest named gap:**

```text
H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR_LEAN
```

**Next cheapest decisive test after its separate semantic admission:**

```text
H2A_4_1B_3_SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE
```

Its first discriminator is the exact source identity or bound for the
mode-weighted beta moment; zero-consistent numerics remain inconclusive.

**Memory entry:**

```yaml
iteration:
  target: H2A.4.1B.1 combined CCM action discriminator
  status: PROGRESS
  failed_strategy: full residual decay and pre-normalizer log^(3/2) ledger
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: H2A_4_1B_2_WEIGHTED_RESIDUAL_TO_EVENTUAL_COMPLEMENT_FLOOR_LEAN
  invariant_learned: preserve exact selected residual and distinguish odd mass from ccmEtaFinite
  forbidden_future_move: treat beta-dot-row as an ordinary L73 anchor moment
  next_decisive_test: formalize weighted residual to fixed complement floor
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
