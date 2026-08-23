# STATUS: PROVED

```yaml
PRIMARY: SEMANTICALLY_ADMIT_W1_AND_AUTHORIZE_W2_SELECTED_PACKET_VARIATION
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  TRANSACTION_COMMIT: 4984a1071b6728ab64fee318ebaf0e3ee07bf5fb
  TRANSACTION_PARENT: 545cc3f93a465072ed17896c5fcded12af0da01a
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceLogWindowFourierIntegralCrosswalk.lean
  LEAN_GIT_BLOB: 21692df075aca7467503c5d49671691c1a1a1db7
  LEAN_SHA256: b1ab6e27ae880c99b2617e016c60d08fa43de06e734706cf27665c72f4e46ae8
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_INTEGRAL_CROSSWALK_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 7bfe52bacd864eb9913183fb8ec4ac1a8b16911f
  RECEIPT: PASS

KERNEL_GATE_REPORTED:
  lake_env_lean: EXIT_0
  lake_build: PASS_7769_JOBS
  q3_check: EXIT_0
  AXIOM_PROFILES:
    sourceLogWindowZeroExtension: [propext, Classical.choice, Quot.sound]
    sourceLogWindowZeroExtension_integrable: [propext, Classical.choice, Quot.sound]
    coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension: [propext, Classical.choice, Quot.sound]
    one_mode_agreement_without_complete_basis_does_not_identify_maps_plant: [propext, Classical.choice, Quot.sound]
  sorryAx: ABSENT

SEMANTIC_ADMISSION:
  H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_ACTUAL_INTEGRAL_LEAN: PROVED
  SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK: CLOSED

PUBLIC_SURFACE:
  sourceLogWindowZeroExtension:
    status: ADMITTED
    object: ADDITIVE_LOG_WINDOW_ZERO_EXTENSION
    coordinate: Icc_0_L_m
    multiplicative_I_m_Fourier_claim: false
  sourceLogWindowZeroExtension_integrable:
    status: ADMITTED
    new_public_hypothesis: false
  coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension:
    status: ADMITTED
    equality: ALMOST_EVERYWHERE
    pointwise_equality_claimed: false

STRUCTURE_PRESERVED:
  - exact_H_m_vector
  - exact_logWindowL2Equiv_inverse
  - additive_window_Icc_0_L_m
  - existing_sourceLogWindowFourierL2Isometry
  - full_V_n_m_Hilbert_basis
  - exact_Fourier_sign_and_2pi_convention
  - almost_everywhere_category

DROPPED_OR_NOT_CLAIMED:
  - pointwise_representative_independence
  - Plancherel_theorem
  - shifted_form_domain_membership
  - selected_Ferrers_BV
  - Abel_limit
  - root_energy_rate
  - Gamma_source_rate

CLOSES:
  - SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK
OPENS: []

NEXT:
  TASK: H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE_LEAN
  MODE: LEAN_SOURCE_TRANSACTION
  LEAN_EDIT: true
  NUMERICS: false
  ARISTOTLE_AUTHORIZED: false
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_2026-08-23.md

W2_TARGET:
  PUBLIC_DEF: selectedFerrersLemma73SourcePacket
  PUBLIC_THEOREM: selectedFerrersLemma73SourcePacket_boundedVariationOn
  EXACT_PACKET: selectedFerrersLemma73SourceScale_k_mul_prolateCombination_selectedFerrersPreAnchorPair_k
  VARIATION_DOMAIN: Set.univ
  ENDPOINT_CONVENTION: PRODUCTION_FULL_ENDPOINT
  MIDPOINT_OBJECT_DEFINED_HERE: false
  COFINAL_RATE_CLAIMED: false

CANDIDATE_REPRESENTATIONS:
  R1:
    CODE: CLOSED_LEGENDRE_DERIVATIVE_BOUND_TO_LIPSCHITZ_AND_GLOBAL_BV
    ROLE: PRIMARY
    KILL_POWER: 10
    COST: 6
  R2:
    CODE: DIRECT_EVOLUTION_ON_VARIATION_FROM_TAIL_SPLICE
    ROLE: RUNNER_UP_NOT_AUTHORIZED
    KILL_POWER: 8
    COST: 8

ARSENAL_MANDATE:
  ACCEPTED: true
  HASH_STATUS: OWNER_RATIFIED_C13_DECK_SUPERSEDES_2026_08_04_12_CARD_HASH
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE

PRIOR_PREDICTION_FATES:
  P_W1_1_0_91: CONFIRMED
  P_W1_2_0_76: CONFIRMED
  P_W1_3_0_99: CONFIRMED
  LP_RESTRICTED_REPRESENTATIVE_OR_TENDSTO_IN_MEASURE_NORMAL_FORM: PARTIALLY_OBSERVED
  RETROACTIVE_REPAIR: false

REGISTERED_PREDICTIONS:
  P_W2_1:
    probability: 0.88
    prediction: a closed-window Legendre derivative majorant polynomial in degree plus the existing weighted coefficient summability yields a selected-packet BV certificate
  P_W2_2:
    probability: 0.81
    prediction: the production full-endpoint zero extension has finite global variation after paying exactly two endpoint jumps
  P_W2_3:
    probability: 0.72
    prediction: pinned Mathlib BoundedVariation APIs are sufficient without a custom variation structure
  LIKELIEST_FAILURE: CLOSED_INTERVAL_LEGENDRE_DERIVATIVE_BOUND_OR_GLOBAL_ZERO_EXTENSION_VARIATION_GLUE_API

SCOPE: ABSTRACT
VERIFIER: LEAN
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Node | Verdict | Exact boundary | Tags |
|---|---|---|---|
| **W1 actual-Fourier crosswalk** | **PROVED** | For every literal `x : H_m i`, the synthesized whole-line `L²` image equals almost everywhere the ordinary Fourier integral of the **additive** log-window zero extension of `(logWindowL2Equiv i).symm x`. | `[ABSTRACT][LEAN]` |
| **W2 selected packet variation** | **OPEN / AUTHORIZED** | Prove finite global variation for the exact source-scaled selected Ferrers packet with production full endpoint values. | `[COFINAL_FAMILY][CONDITIONAL]` |
| **W3 Abel `L²` lock** | **OPEN AFTER W2** | Define the midpoint representative, import Dirichlet–Jordan and the sine-harmonic bound, and identify the Abel limit. | `[COFINAL_FAMILY][CONDITIONAL]` |
| **W4 fixed-`k` root energy** | **OPEN AFTER W1–W3** | Use W1 and finite-jump decay to prove shifted-form membership for each fixed `k`. | `[COFINAL_FAMILY][CONDITIONAL]` |
| **W5 cofinal rate** | **OPEN LATER** | No quantitative cofinal root-energy or Gamma-rate conclusion follows from W1. | `[COFINAL_FAMILY][CONDITIONAL]` |

## FINAL PROPOSAL

### W1 is semantically exact

The public definition uses the chosen representative of

```text
(logWindowL2Equiv i).symm x
```

and extends it by zero on the additive interval `[0,L_m]`.  The Fourier integral is never applied to the multiplicative `I_m` representative.  This closes the old C04 object mismatch on the literal production coordinates. `[ABSTRACT][LEAN]`

The proof does not infer a whole-space theorem from one displayed mode.  It approximates `x` by finite sums in the complete `V_n_m_hilbertBasis`, proves the finite-sum crosswalk, and then passes to the limit.  The mandatory Fin-2 plant correctly rejects one-mode identification. `[ABSTRACT][LEAN]`

Two limit categories are kept separate:

1. finite Fourier integrals converge pointwise—indeed with the available uniform norm estimate—through the finite-window `L²→L¹` bound with exact constant `sqrt(L_m)`;
2. synthesized isometry images converge in whole-line `L²`.

The proof extracts an almost-everywhere convergent subsequence from the second convergence and identifies its pointwise limit using the first.  It never uses the false implication “uniform convergence on an infinite-measure space implies `L²` convergence.” `[ABSTRACT][LEAN]`

The exceptional set issue is also closed correctly.  Finite-sum equality is initially almost everywhere for each approximant; `ae_all_iff` produces one common full-measure set for every natural-numbered approximant before the subsequence limit is taken. `[ABSTRACT][LEAN]`

### Exact boundary

W1 proves an **almost-everywhere equality of `L²` objects**.  It does not select a canonical pointwise representative of the synthesized isometry.  Any later pointwise argument must use the continuous ordinary Fourier-integral representative supplied on the right-hand side, not silently evaluate the `Lp` class. `[ABSTRACT][LEAN]`

W1 also proves no bounded variation, Abel convergence, shifted-form membership, global Weil-form crosswalk, or source-action rate.  Those remain separate consumers.

## STRONGEST ATTACK

The strongest reviewer objection is:

> The finite-mode equalities may hold on different full-measure sets.  Passing to a limit without synchronizing those sets would leave a quantifier gap.

The source explicitly synchronizes them with `MeasureTheory.ae_all_iff` before taking the subsequence.  This objection is defeated.

The second objection is:

> The ordinary Fourier integral depends on an arbitrary representative of an `Lp` class.

The public definition fixes the representative chosen by the existing coercion.  More importantly, Fourier integrals of integrable almost-everywhere equal representatives agree, while the theorem claims only almost-everywhere equality on the frequency side.  No pointwise representative-independence theorem is needed for this contract.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE_LEAN

MODE:
  ONE GOAL / ONE COMMIT
  LEAN SOURCE TRANSACTION
  NO NUMERICS
  NO ARISTOTLE

PREFLIGHT:
  Run ./ask.sh for:
    selected Ferrers packet bounded variation
    Legendre derivative closed interval bound
    weighted coefficient derivative summability
    BoundedVariationOn zero extension Icc
  Search pinned Mathlib for exact `BoundedVariationOn`, `eVariationOn`,
  Lipschitz/variation gluing, and interval APIs before naming an external lemma.

LEAN FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersPacketVariation.lean

SOURCE RECORD:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_2026-08-23.md

DIRECT IMPORTS:
  Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate
  Mathlib.Analysis.BoundedVariation

PUBLIC SURFACE:

  noncomputable def selectedFerrersLemma73SourcePacket
      (k : ℕ) : ℝ → ℂ :=
    fun x => selectedFerrersLemma73SourceScale k *
      prolateCombination (selectedFerrersPreAnchorPair k) x

  theorem selectedFerrersLemma73SourcePacket_boundedVariationOn
      (k : ℕ) :
    BoundedVariationOn
      (selectedFerrersLemma73SourcePacket k)
      Set.univ

Equivalent repository syntax is allowed.  The object, scalar, pair, endpoint convention, and domain may not change.

CLOSES:
  W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE

OPENS:
  []

PROOF ROUTE:
  1. Prove privately a closed-unit-interval ordinary-Legendre derivative
     majorant polynomial in degree, for example

       |P_n'(x)| ≤ C * (n+1)^2,
       x ∈ [-1,1],

     with a fixed explicit `C`.  Do not reuse the existing strict-subinterval
     bound containing `(1-r^2)^(-1)` at `r=1`.

  2. Use the already source-locked tail splice theorem to obtain

       Summable (fun q => (q+1)^2 * |a q|)

     for each selected mode.  Apply the closed-interval derivative majorant
     to obtain uniform convergence/boundedness of the derivative series on
     the full closed source interval.

  3. Combine closed-window continuity, interior derivative identity, and the
     uniform derivative bound to prove a Lipschitz or directly bounded-
     variation certificate on the closed dimensionless interval.

  4. Transport through physical scaling, positive `L²` normalization, the
     exact selected mode-zero/mode-four combination, and the exact complex
     `selectedFerrersLemma73SourceScale`.

  5. Prove global bounded variation of the production zero extension.  Pay
     the two endpoint jumps explicitly.  The production function uses full
     endpoint values because its support is an `Icc.indicator`; do not replace
     it by the midpoint representative.

  6. Print axioms for every public declaration and the mandatory plant.

MANDATORY PRIVATE PLANT:
  STRICT_COMPACT_DERIVATIVE_BOUND_DOES_NOT_SUPPLY_CLOSED_ENDPOINT_BOUND

  Instantiate the blow-up of `(1-r^2)^(-1)` as `r → 1-`, or an equivalent
  exact arithmetic family.  The plant must reject plugging `r = 1` into the
  existing interior derivative majorant.

FORBIDDEN:
  - interior analyticity plus endpoint continuity relabeled as BV;
  - use of `coefficients_abs_summable` without the weighted derivative sum;
  - assuming endpoint values vanish;
  - replacing full endpoint values by midpoint values;
  - differentiating the F72.6 `C⁰` rate;
  - importing Dirichlet–Jordan or Abel convergence in this transaction;
  - claiming a cofinal variation/root-energy rate;
  - defining a neighboring packet or changing the source scale;
  - sorry, admit, native_decide, new axiom, theorem weakening.

VALIDATION:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersPacketVariation

  WORKDIR repo root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersPacketVariation.lean

EXPECTED_AXIOM_PROFILES:
  every public theorem and the plant:
    [propext, Classical.choice, Quot.sound]

SUCCESS:
  H2A_4_1B_3C_1_11_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE_LEAN

FAILURE_CODES:
  CLOSED_INTERVAL_LEGENDRE_DERIVATIVE_BOUND_GAP
  SELECTED_PACKET_WEIGHTED_DERIVATIVE_SUM_GAP
  GLOBAL_ZERO_EXTENSION_VARIATION_GLUE_GAP
  PINNED_BOUNDED_VARIATION_API_MISMATCH
```

## META CLOSEOUT

**What became smaller?**

The synthesized-Fourier object mismatch is gone for every `H_m` vector.  The active Abel/root-energy chain now starts at one source-specific regularity question: global variation of the selected packet.

**What was killed?**

- a Plancherel backport as a prerequisite;
- modewise equality without completeness;
- Fourier transformation of the multiplicative representative;
- `uniform ⇒ L²` on the whole line;
- a pointwise claim where only an almost-everywhere statement is proved.

**What must not be tried again?**

Do not reopen W1, redefine the isometry, or import selected Ferrers analysis into the generic crosswalk.  Do not infer W2 from interior analyticity and closed-window continuity.

**Current smallest named gap:**

```text
W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE
```

**Next cheapest decisive test:**

Prove a polynomial closed-interval derivative bound for the literal ordinary Legendre basis and check that the existing weighted coefficient summability closes the derivative series on the endpoints.

**Prior predictions:**

All three W1 predictions are confirmed; the predicted normal-form friction was only partially observed and did not alter the theorem statement.

**Memory entry:**

```yaml
iteration: H2A_4_1B_3C_1_10
target: SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK
status: PROGRESS
failed_strategy: PLANCHEREL_BACKPORT_AND_MODEWISE_ONLY_IDENTIFICATION
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: W2_SELECTED_FERRERS_PACKET_VARIATION_CERTIFICATE
invariant_learned: additive_log_window_coordinate_and_ae_category_must_be_preserved
forbidden_future_move: do_not_treat_interior_analyticity_as_global_BV
next_decisive_test: closed_interval_Legendre_derivative_majorant_plus_weighted_tail_sum
```
