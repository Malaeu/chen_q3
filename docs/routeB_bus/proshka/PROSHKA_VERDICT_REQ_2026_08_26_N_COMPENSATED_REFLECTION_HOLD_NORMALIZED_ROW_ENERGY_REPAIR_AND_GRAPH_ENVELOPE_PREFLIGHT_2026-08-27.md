# STATUS: CONDITIONAL — COMPENSATED REFLECTION ACCEPTED; NORMALIZED-ROW ENERGY CROSSWALK REPAIRED; GRAPH ENVELOPE REMAINS OPEN

```yaml
PRIMARY: RATIFY_COMPENSATED_REFLECTION_WITH_NORMALIZED_ROW_ENERGY_REPAIR
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: ad621220393ab5646c8d0502dfe8553b9317c24e
  REPORT_PATH: docs/routeB_bus/LINUX_COMPENSATED_REFLECTION_DUHAMEL_RATE_PREFLIGHT_GOAL058_2026-08-27.md
  REPORT_RESULT: COMPENSATED_FUNCTIONAL_AND_ENERGY_CROSSWALK_CLOSED_WITHOUT_X_ENVELOPE
  PARENT_VERDICT: 979feca5a9a6aabbde0817e4eeeaf4a71a4e30e3

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false
  NUMERICS_OCCUPY_QUANTIFIER: false

ADJUDICATION:
  REPORTED_DISCRIMINATOR: HOLD
  DECISION: HOLD_RATIFIED_WITH_C04_ENERGY_OBJECT_REPAIR

  PERIODIC_W02_FOLD: PAPER_PROVED
  REFLECTED_CONTINUOUS_PRIME_MAIN_MATCH: PAPER_PROVED
  EXACT_FOLDED_REMAINDER: "-[L/(2*pi^2)]*exp(-L*t/(4*pi)) dt"

  ARCH_ENDPOINT_RESIDUE:
    status: PAPER_PROVED
    value: "1/(2*pi)"
    independent_of_m: true
    independent_of_schedule: true

  COMPLETED_SOURCE_IS_FINITE_MEASURE: false
  LEGAL_OBJECT: ENDPOINT_COMPENSATED_FUNCTIONAL_ON_LIPSCHITZ_ZERO_BOUNDARY_TESTS
  NAIVE_CUMULATIVE_NU: forbidden
  NAIVE_TOTAL_MASS: forbidden
  COMPENSATED_PRIMITIVE:
    status: CONDITIONAL_ON_INTEGRABLE_REMAINDER
    reason: residue cancellation alone does not replace the remainder-integrability statement

  DUHAMEL_VOLTERRA_IDENTITY: PRESERVED
  POINTWISE_MODE_LOCALIZATION_OF_X_REQUIRED: false

ENERGY_CROSSWALK:
  DUPLICATE_SUPPLIER_MINT: REJECTED
  EXISTING_CONTRACT: SelectedPhysicalFourierEnergyControl
  EXISTING_CONTRACT_STATUS: OPEN_PROP_NOT_DISCHARGED

  REPORT_EXACT_EQUALITY:
    status: REJECTED_C04_OBJECT_MISMATCH
    rejected_formula: >-
      selectedPhysicalFourierEnergy = (4*pi^2/L^2)*||N*q||_2^2
    reason: >-
      selectedPhysicalFourierEnergy is defined on the full unprojected gTrial_m,
      whereas q is the coefficient row of the normalized finite projection
      kTrial_m_N = sTrial_m_N * P_m_N(gTrial_m).

  CORRECT_EXACT_FINITE_IDENTITY: >-
    physicalFourierEnergy(i, coe(kTrial_m_N))
    = (4*pi^2/L^2)*||N*q||_2^2.
  CORRECT_FULL_OBJECT_INEQUALITY: >-
    ||N*q||_2 <= |sTrial_m_N|*(L/(2*pi))*sqrt(physicalFourierEnergy(i,gTrial_m)).

  NORMALIZER_CONTRACT: SelectedTrialNormalizerBounded
  NORMALIZER_SELECTED_FERRERS_SUPPLIER:
    theorem: selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
    status: LEAN_PROVED_UNDER_FROZEN_W5_INPUTS

  REPAIRED_SUFFICIENT_PACKAGE: >-
    SelectedPhysicalFourierEnergyControl
    + SelectedTrialNormalizerBounded
    implies ||N*q||_2 = O(L) along the same selected family.
  REPAIRED_PACKAGE_DISCHARGED: false
  reason: SelectedPhysicalFourierEnergyControl remains an undischarged hypothesis.

GRAPH_TEST_VECTOR:
  object: "x_k(z) = C_k^(-1)*kappa_k(z)"
  current_status: OPEN
  generic_coercive_route: >-
    If C=Q(K-eps I)Q+P and the q-perpendicular floor is beta>0,
    then Re<y,Cy> >= min(beta,1)*||y||^2 and
    ||C^(-1)kappa|| <= ||kappa||/min(beta,1).
  generic_theorem_exported_now: false
  cofinal_instantiation_requires:
    - literal eventual complement-floor rate
    - literal compact P59 kernel-row norm envelope
    - one same-family rate ledger

CLOSES:
  - TRIAL_MODE_ENERGY_AS_A_NEW_SUPPLIER
  - UNCOMPENSATED_REFLECTION_MEASURE_OBJECT
  - POINTWISE_MODE_LOCALIZATION_OF_GRAPH_VECTOR_AS_NECESSARY_INPUT

OPENS: []

CARRIES_OPEN:
  - GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE
  - SELECTED_PHYSICAL_FOURIER_ENERGY_CONTROL
  - COMPENSATED_REFLECTION_DISCREPANCY_SOURCE_BOUND

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_DISCRIMINATOR:
  PASS: GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE_SOURCE_READY
  HOLD: GRAPH_INVERSE_BOUND_REDUCED_TO_P59_KERNEL_NORM_OR_FLOOR_SOURCE
  FAIL: GRAPH_ENVELOPE_REIMPORTS_UNCONTROLLED_FLOOR_OR_CARRIER_GROWTH

CANDIDATE_REPRESENTATIONS:
  R1_DIRECT_GRAPH_COERCIVITY:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 2/10
    object: >-
      Strengthen the banked PosDef proof to the exact lower envelope
      min(beta,1)*I, then divide the literal P59 row norm by that floor.
  R2_GRAPH_ENERGY_DUAL_NORM:
    rank: RUNNER_UP
    kill_power: 8/10
    proof_cost: 5/10
    object: >-
      Bound only the Duhamel pairings through C^(-1/2)-weighted dual norms,
      avoiding a standalone Euclidean ||x|| envelope if the latter grows.

REGISTERED_PREDICTIONS:
  P_GRAPH_ENVELOPE_1:
    probability: 0.65
    prediction: >-
      The generic min(beta,1) inverse bound closes exactly, but the literal
      P59 compact row norm or fixed complement-floor source remains open; HOLD.
  P_GRAPH_ENVELOPE_2:
    probability: 0.25
    prediction: >-
      Existing P59 and eventual-floor suppliers combine to give a usable
      compact envelope; PASS.
  P_GRAPH_ENVELOPE_3:
    probability: 0.10
    prediction: >-
      The literal P59 row has carrier growth that the available floor cannot
      absorb, so the Euclidean-envelope representation fails; FAIL and use R2.

PRIOR_PREDICTION_FATE:
  P_REFLECTION_DUHAMEL_1_0_55: CONFIRMED_WITH_C04_ENERGY_REPAIR
  P_REFLECTION_DUHAMEL_2_0_30: NOT_REALIZED
  P_REFLECTION_DUHAMEL_3_0_15: PARTIALLY_TRIGGERED_ENDPOINT_CATEGORY_REPAIRED_ROUTE_SURVIVES

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - REPRESENTATION_PROGRESS
  - FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| Periodically folded `W02` density is `[L/(2π²)](√m−1)e^{-Lt/(4π)}` | Accepted. | `[COFINAL_FAMILY][PAPER]` |
| Its difference from the reflected continuous prime main is exactly `−[L/(2π²)]e^{-Lt/(4π)}` | Accepted for the continuous main model only. | `[COFINAL_FAMILY][PAPER]` |
| The full arithmetic reflection discrepancy is therefore `O(L)` | Not proved; `dψ−dx`, the lower-end correction and the Arch endpoint functional remain. | `[COFINAL_FAMILY][CONDITIONAL]` |
| The completed source is a finite signed measure | Refuted.  The Arch density has endpoint residues `±1/(2π)`. | `[COFINAL_FAMILY][PAPER]` |
| The endpoint-vanishing Lipschitz pairing is legal | Accepted. | `[COFINAL_FAMILY][PAPER]` |
| The compensated primitive exists solely because the residue is known | Too strong.  The explicit remainder must also be locally integrable after subtraction. | `[COFINAL_FAMILY][CONDITIONAL]` |
| A new trial-mode-energy supplier is required | Refuted.  The catalogue already contains `SelectedPhysicalFourierEnergyControl`. | `[ABSTRACT][LEAN]` |
| Existing selected physical energy equals `(4π²/L²)||Nq||²` | Refuted for the literal objects used in the report. | `[FINITE_CELL][PAPER]` |
| Existing physical energy plus bounded trial normalizer controls `||Nq||` | Accepted through the repaired inequality. | `[COFINAL_FAMILY][PAPER]` |
| The existing physical-energy contract is already proved on the selected Ferrers family | Refuted.  It remains an explicit `Prop` hypothesis. | `[COFINAL_FAMILY][LEAN]` |
| The graph-vector compact envelope follows formally from PosDef alone | Not yet.  PosDef gives invertibility, but the quantitative floor and literal P59 row norm must be retained. | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. The report closes two representation errors

The report correctly accepts the periodic fold and the endpoint-category repair.
The fold is exact:

\[
\left(\sqrt m-2+\frac1{\sqrt m}\right)
\frac{\sqrt m}{\sqrt m-1}=\sqrt m-1.
\]

Thus the folded `W02` continuous density on one angle period is

\[
\frac{L}{2\pi^2}(\sqrt m-1)e^{-Lt/(4\pi)}\,dt,
\]

and subtracting the reflected continuous prime main leaves exactly

\[
-\frac{L}{2\pi^2}e^{-Lt/(4\pi)}\,dt.
\]

This is a real cancellation mechanism.  It is not yet a bound on the full
von-Mangoldt Stieltjes discrepancy.

The Arch density has the exact small-angle behaviour

\[
\frac{L}{4\pi^2}
\frac{e^{Lt/(4\pi)}}{\sinh(Lt/(2\pi))}\,dt
\sim \frac{dt}{2\pi t}.
\]

After reflection the two endpoint residues are equal and opposite.  The test
vanishes to first order at both endpoints, so the literal pairing converges.
This is an instance of **C13**: restore the broken reflection symmetry by
carrying the explicit endpoint shadows, rather than pretending that the source
is a finite measure.

## 2. The catalogue crosswalk is real, but the report used the wrong source object

The report is right about the process conclusion:

```text
Do not mint TRIAL_MODE_ENERGY_BOUND_ALONG_THE_SCHEDULE.
```

The catalogue already contains:

```lean
SelectedPhysicalFourierEnergyControl
```

However, the claimed exact equality crosses three different objects.

Let

\[
g_k:=gTrial_m,
\qquad
P_Ng_k:=gTrial_{m,N},
\qquad
s_k:=\|P_Ng_k\|^{-1},
\]

and let the literal finite CCM row be

\[
q_{k,n}=\langle V_n,s_kP_Ng_k\rangle.
\]

The existing `selectedPhysicalFourierEnergy` is defined on the **full** object
`gTrial_m`.  The literal row `q` is defined from the **normalized finite
projection** `kTrial_m_N = s_k P_Ng_k`.

Therefore the exact finite identity is

\[
\operatorname{Energy}_{\rm phys}(kTrial_{m,N})
=
\frac{4\pi^2}{L^2}\sum_{|n|\le N}n^2|q_{k,n}|^2.
\]

For the existing full-object energy one only gets

\[
\sum_{|n|\le N}n^2|q_{k,n}|^2
\le
|s_k|^2\frac{L^2}{4\pi^2}
\operatorname{Energy}_{\rm phys}(g_k).
\]

Equivalently,

\[
\boxed{
\|Nq_k\|_2
\le
|s_k|\frac{L}{2\pi}
\sqrt{\operatorname{Energy}_{\rm phys}(g_k)}.
}
\]

The omitted `s_k` is load-bearing.  This is exactly the **C04** question:
these objects use the same Fourier coordinates, but they obey different
normalizations and live before versus after finite projection.

The repair is available.  The repository already proves, under the frozen W5
family/rate inputs,

```lean
selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
```

so the correct package is

```text
SelectedPhysicalFourierEnergyControl
+ SelectedTrialNormalizerBounded
→ ||Nq_k|| = O(L_k).
```

The package remains conditional because `SelectedPhysicalFourierEnergyControl`
is still an undischarged source contract.  The first-order projection-tail
route does not silently prove it.

## 3. The graph-test-vector envelope has a cheap exact algebraic core

Let

\[
C=Q(K-\varepsilon I)Q+P,
\qquad
P=qq^*,
\qquad
Q=I-P,
\qquad
q^*q=1.
\]

Assume the literal complement floor at the Rayleigh shift:

\[
\beta\|w\|^2
\le
\operatorname{Re}\langle w,(K-aI)w\rangle,
\qquad q^*w=0,
\]

with `β>0` and `ε≤a`.  Write `y=w+dq`.  The banked PosDef proof already
contains the exact orthogonal decomposition.  Keeping the constants gives

\[
\operatorname{Re}\langle y,Cy\rangle
\ge
\beta\|w\|^2+|d|^2
\ge
\min(\beta,1)\|y\|^2.
\]

Therefore, for `Cx=κ`,

\[
\boxed{
\|x\|_2
\le
\frac{\|\kappa\|_2}{\min(\beta,1)}.
}
\]

This is the cheapest decisive route.  It does not require modewise control of
`x`, dIIKS dressing, or a new operator norm over all source actions.

But it is not yet a cofinal compact envelope.  The selected-family
instantiation must retain two rates:

1. a fixed or controlled reciprocal complement floor;
2. the compact norm of the literal Proposition-59 kernel row on the moving
   finite carrier.

A fixed eventual floor is available only after the existing sector-floor and
weighted-residual suppliers are instantiated.  The P59 kernel norm rate has not
been audited in this representation.

## 4. Strongest attack

The strongest objection is:

> The proposed inverse estimate may be exact but useless, because
> `||κ_k(z)||` can grow with the carrier and the available complement floor may
> shrink.  Then `||C_k^{-1}κ_k(z)||` is not uniformly bounded on compacts.

This objection is decisive and cheap to test.  The next preflight must compute
the exact source-level rate ledger

\[
\frac{\sup_{z\in K}\|\kappa_k(z)\|_2}
     {\min(\beta_k,1)}
\]

without numerics, without replacing the literal row by a pointwise surrogate,
and without assuming a fixed floor that has not been supplied.

Failure of this sufficient Euclidean envelope does not prove the Duhamel route
false.  It selects the runner-up weighted-dual representation.

## 5. Final proposal

Run exactly one paper/source audit:

```text
GOAL058_SELECTED_FERRERS_GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE_PREFLIGHT
```

Required output:

1. Export on paper the exact `min(β,1)` coercive lower envelope for
   `trialGraphOperator`.
2. Derive the exact inverse-solve norm inequality.
3. Identify the literal finite P59 vector `κ_k(z)` including removable lattice
   points and all normalization factors.
4. Derive its norm on an arbitrary fixed compact, with the moving carrier and
   the selected schedule explicit.
5. Bind the exact eventual complement-floor supplier; do not replace it with a
   finite-cell or conditional placeholder.
6. Multiply the rates and compare with the compensated-reflection consumer
   budget.
7. If the Euclidean envelope fails, state whether the `C^{-1/2}` dual-energy
   formulation removes the growth.

No Lean, numerical probe, Aristotle or Codex execution is authorized before
this discriminator.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.

TASK_ID:
  GOAL058_SELECTED_FERRERS_GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

PASS:
  GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE_SOURCE_READY

HOLD:
  GRAPH_INVERSE_BOUND_REDUCED_TO_P59_KERNEL_NORM_OR_FLOOR_SOURCE

FAIL:
  GRAPH_ENVELOPE_REIMPORTS_UNCONTROLLED_FLOOR_OR_CARRIER_GROWTH
```

## META CLOSEOUT

**What became smaller?**

The regularity side no longer asks for pointwise mode control of the graph
solution.  Its graph-dependent part is reduced to one explicit quotient:

\[
\sup_{z\in K}\|\kappa_k(z)\|_2/\min(\beta_k,1).
\]

**What was killed?**

- a duplicate trial-mode-energy supplier;
- the finite-measure reflection object;
- the exact equality between full-object physical energy and normalized finite
  row mode energy;
- the omission of the selected trial normalizer.

**What must not be tried again?**

- identifying `gTrial_m`, `P_m_N gTrial_m`, and `kTrial_m_N` because they share
  Fourier coordinates;
- declaring `SelectedPhysicalFourierEnergyControl` discharged because a
  different first-order tail route exists;
- using `PosDef` as a quantitative inverse bound without exporting its lower
  envelope;
- separating `W02`, Arch and Prime into absolute component budgets.

**Current smallest named gap**

```text
GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE
```

with the subsidiary open input

```text
SELECTED_PHYSICAL_FOURIER_ENERGY_CONTROL.
```

**Next cheapest decisive test**

The exact source-rate audit of

\[
\sup_{z\in K}\|\kappa_k(z)\|_2/\min(\beta_k,1).
\]

**Memory entry**

```yaml
iteration:
  target: compensated reflection Duhamel rate
  status: PROGRESS
  failed_strategy: exact full-energy equals normalized finite-row mode moment
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE
  invariant_learned: full trial, finite projection and normalized finite row are distinct source objects
  forbidden_future_move: omit finite-projection normalizer in a Fourier-energy crosswalk
  next_decisive_test: literal P59 row norm divided by exact complement floor
```
