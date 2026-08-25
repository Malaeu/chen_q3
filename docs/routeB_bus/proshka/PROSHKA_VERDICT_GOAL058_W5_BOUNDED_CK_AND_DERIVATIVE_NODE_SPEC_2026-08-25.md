# STATUS: CONDITIONAL — BOUNDED_CK_SUFFICES RATIFIED; DERIVATIVE TARGET IS EVENTUAL BOUNDEDNESS
```yaml
PRIMARY: RUN_W5_LOG_DERIVATIVE_EVENTUAL_BOUND
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  CONSUMER_DISCRIMINATOR_COMMIT: b04ba7bebb883c3e1ca914c59ebb954fb453f138
  CONSUMER_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarPhysicalFourierEnergyControl.lean
  CONSUMER: SelectedPhysicalFourierEnergyControl

CONSUMER_RATE_LOCK:
  code: BOUNDED_CK_SUFFICES
  status: RATIFIED
  reason: >-
    The first committed consumer requires IsBoundedUnder atTop of the selected
    physical Fourier energy family. It asks eventual boundedness, not decay,
    not a rate, and not a global supremum over all k.
  P_W5_CONSUMER_1: CONFIRMED

CURRENT_W5_LEDGER:
  L1: PROVED_EVENTUALLY_BOUNDED_CONDITIONAL_ON_F72_6
  ENDPOINT0: PROVED_TENDS_TO_ZERO_CONDITIONAL_ON_F72_6
  ENDPOINTL: PROVED_TENDS_TO_ZERO_CONDITIONAL_ON_F72_6
  SEAM: PROVED_TENDS_TO_ZERO_CONDITIONAL_ON_F72_6
  JUMP: TENDS_TO_ZERO_CONDITIONALLY
  DERIVATIVE: OPEN

TARGET:
  GAP: W5_LOG_DERIVATIVE_BUDGET_RATE
  PUBLIC_THEOREM: selectedFerrersAbelLogDerivativeBudget_bounded_of_modeAndChiRates
  REQUIRED_CONCLUSION: >-
    exists D >= 0 such that eventually
    selectedFerrersAbelLogDerivativeBudget k <= D.
  REQUIRED_RATE: EVENTUAL_BOUNDEDNESS_ONLY
  DECAY_REQUIRED: false
  NEW_C1_F72_6_PREMISE_ALLOWED: false

CRITICAL_REPAIR:
  code: WEIGHTED_DERIVATIVE_ZERO_MASS_HAS_ENDPOINT_DEFECT
  old_claim: integral(y * pkt'(y)) = - integral(pkt) = 0
  verdict: REJECT_AS_STATED
  exact_issue: >-
    On the production full-endpoint representative, integration by parts has
    the boundary term [y*pkt(y)]_{-lambda}^{lambda}. The endpoint packet value
    is not definitionally zero and is already paid by the W4/W5 seam ledger.
  required_fix: >-
    Keep the endpoint term as an explicit shadow/completion term. Do not erase
    it by declaring Q zero-mass.
  arsenal_card: C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

PRIMARY_REPRESENTATION:
  code: ENDPOINT_COMPLETED_SIGNED_ESTAR_WEIGHTED_DERIVATIVE
  object: Q_k(y) = y * deriv(pkt_k)(y) on the physical-window interior
  proof_policy: >-
    Derive the exact additive derivative decomposition first. Perform endpoint-
    aware integration by parts exactly. Separate the endpoint defect into an
    explicit shadow whose cost is controlled by the already-proved endpoint/
    seam rate. Preserve the signed E_star sum until after cancellation. Do not
    replace E_star(Q_k) by a sum of termwise norms.
  kill_power: 9/10
  proof_cost: 4/10

RUNNER_UP_REPRESENTATION:
  code: MINIMAL_C1_F72_6_ONLY_IF_DIRECT_ROUTE_FAILS
  theorem_strength: >-
    Only the weakest C1/right-half envelope actually required to prove eventual
    boundedness of the derivative budget; do not target O(lambda^-2) C1
    convergence unless the direct route proves it necessary.
  kill_power: 8/10
  proof_cost: 7/10

DISCRETE_CONTINUUM_CAVEAT:
  status: OPEN_SMALL_BRIDGE_POSSIBLE
  statement: >-
    SelectedPhysicalFourierEnergyControl is a discrete weighted coefficient
    contract, while W5 currently majorizes the continuum shifted form. An exact
    discrete-continuum identification may be a separate small node.
  changes_BOUNDED_CK_discriminator: false

PREDICTIONS:
  P_W5_DERIVATIVE_1:
    prediction: >-
      Eventual boundedness of the derivative budget can be proved without a
      full C1 analogue of F72.6, by a signed E_star argument with explicit
      endpoint completion.
    probability: 0.62
    fate: UNTESTED
  P_W5_DERIVATIVE_ENDPOINT_DEFECT:
    prediction: >-
      A naive zero-mass proof for Q_k fails unless it carries the nonzero
      full-endpoint boundary term explicitly.
    probability: 0.93
    fate: SOURCE_AUDIT_CONFIRMED_AS_REQUIRED_GUARD

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```

## ROUTE MAP

The consumer lock is settled. `SelectedPhysicalFourierEnergyControl` literally
requires `IsBoundedUnder (· <= ·) atTop` for the selected physical-energy family.
Therefore W5 does not need `C_k -> 0`; eventual boundedness of `C_k` is the
correct theorem strength.

Three analytic components are already controlled. With

\[
C_k = 2\left(L1_k + \frac{Derivative_k + Jump_k}{2\pi}\right),
\]

`L1_k` is eventually bounded and `Jump_k -> 0`. Hence the remaining W5 analytic
obligation is exactly an eventual bound on `Derivative_k`.

The derivative budget is already the literal production quantity

```lean
selectedFerrersAbelLogDerivativeBudget k =
  integral x in 0..L_k, norm (deriv (selectedFerrersAbelLogRepresentative k) x).
```

The target must therefore be the following theorem shape, with the SAME F72.6
inputs used by the L1 and endpoint nodes and with no new public C1 premise:

```lean
theorem selectedFerrersAbelLogDerivativeBudget_bounded_of_modeAndChiRates
    (C0 C4 Cχ : ℝ)
    (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hmode :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 x -
            ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ k in Filter.atTop,
        selectedFerrersAbelLogDerivativeBudget k ≤ D := by
  ...
```

## FINAL PROPOSAL

Formalize exactly one node:

```text
PATH:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersW5DerivativeBudgetRate.lean

PUBLIC_SURFACE:
  selectedFerrersAbelLogDerivativeBudget_bounded_of_modeAndChiRates

CLOSES:
  W5_LOG_DERIVATIVE_BUDGET_RATE

OPENS:
  []
```

Recommended private proof order:

1. Prove the exact seam-free derivative identity for the production additive
   representative. Keep the existing decomposition into the `E_star(packet)`
   term, the weighted derivative term, and the center shadow.
2. Introduce the weighted derivative object only privately:
   `Q_k(y) = y * deriv(packet_k)(y)` on the physical-window interior.
3. Run integration by parts WITH endpoints. Record the exact boundary defect;
   do not assert zero mass for `Q_k` unless Lean proves the endpoint term zero.
4. Move that defect into an explicit shadow/completion term. Pay it using the
   already-proved edge/seam rate, which is `O(lambda^-2)` before the scalar seam
   multiplier and hence harmless for eventual boundedness.
5. Preserve the signed `E_star` structure for the remaining completed object.
   The next private target is an integrable additive-log envelope with a
   k-independent integral. Only after that envelope is proved may norms be
   taken.
6. Add the already-proved L1-style bound for the `(1/2) E_star(packet)` term and
   the center-shadow bound. Integrate the resulting majorant and return one
   constant `D`.

If step 5 cannot be closed from the exact prolate/Fourier identities and the
existing F72.6 inputs, STOP with:

```text
W5_DIRECT_SIGNED_WEIGHTED_DERIVATIVE_ENVELOPE_GAP
```

and report the smallest missing theorem. Do NOT silently add a C1 hypothesis to
the public theorem.

## STRONGEST ATTACK

The main reviewer objection is the boundary term. The previous derivative
sketch stated that `Q(y)=y*pkt'(y)` has zero mass for free because the packet
has zero mass. That is not source-safe for the production full-endpoint object:

\[
\int_{-\lambda}^{\lambda} y\,pkt'(y)\,dy
=
[y\,pkt(y)]_{-\lambda}^{\lambda}
-
\int_{-\lambda}^{\lambda} pkt(y)\,dy.
\]

The second term vanishes, but the first does not vanish by definition; the
project explicitly carries and estimates `pkt(lambda)` in the seam ledger.
Therefore the derivative proof must use an exact endpoint-completed identity.
This is an instance of Arsenal C13: restore the exact symmetry with an explicit
shadow, then estimate the shadow.

A second attack is logical: even if `C_k` eventually bounds the continuum
shifted form, the downstream contract is phrased as discrete
`physicalFourierEnergy`. Keep that crosswalk separate. It does not strengthen
the derivative target, but it may remain the next small semantic bridge after
W5 closes.

## CODEX DIRECTIVE

```text
TASK_ID: GOAL058_W5_LOG_DERIVATIVE_EVENTUAL_BOUND

TARGET:
  selectedFerrersAbelLogDerivativeBudget_bounded_of_modeAndChiRates

NEW_PUBLIC_PREMISES:
  NONE beyond the exact F72.6 mode/chi rate inputs already used by the L1 node.

FORBIDDEN:
  - full C1-F72.6 premise in the public theorem;
  - termwise absolute-value replacement of signed E_star(Q);
  - assertion integral(y*pkt') = 0 without the endpoint term;
  - Poisson or change-of-variable detour unless the direct completion genuinely
    reaches an exact source identity requiring it;
  - theorem weakening to fixed k.

SUCCESS:
  exists D >= 0, eventually Derivative_k <= D.

FAILURE:
  W5_DIRECT_SIGNED_WEIGHTED_DERIVATIVE_ENVELOPE_GAP
  plus exact smallest missing lemma and location.

VALIDATION:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersW5DerivativeBudgetRate.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersW5DerivativeBudgetRate
  WORKDIR repo root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersW5DerivativeBudgetRate.lean

EXPECTED_AXIOMS:
  [propext, Classical.choice, Quot.sound]
```

## META CLOSEOUT

- Became smaller: the consumer no longer asks for a derivative decay rate; only
  eventual boundedness remains.
- Killed: proving full `C1 = O(lambda^-2)` before it is shown necessary.
- Must not be tried again: dropping the production endpoint in the weighted
  derivative zero-mass argument.
- Current smallest gap: `W5_DIRECT_SIGNED_WEIGHTED_DERIVATIVE_ENVELOPE_GAP`.
- Next cheapest decisive test: derive the endpoint-completed weighted-derivative
  identity symbolically before any new C1 estimate.
- Prediction fate: `P_W5_CONSUMER_1` CONFIRMED; `P_W5_DERIVATIVE_1` remains
  registered and untested.
