# STATUS: PROVED — FIXED-MODE C1 SOURCE ACQUISITION RATIFIED; ONLY C0 IS PRESENT; FULL E-STAR DERIVATIVE/JUMP RATE PREFLIGHT AUTHORIZED

```yaml
PRIMARY: ADMIT_FIXED_MODE_C1_SOURCE_ACQUISITION_AND_AUTHORIZE_FULL_DERIVATIVE_BUDGET_PREFLIGHT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 64c3962c0ed86a0c1edffadc04cbf6f654d6208f
  REPORT_PARENT: 8e0f2693d3aa9945940b33d263402065517ee26d
  REPORT_PATH: docs/routeB_bus/H2A_4_1B_3C_1_1_FIXED_MODE_C1_SOURCE_ACQUISITION_2026-08-23.md
  REPORT_GIT_BLOB: 80e3e32572aa5356f93d5a050a27b735beca777a
  MODE: READ_ONLY
  LEAN_EDIT: false
  ARISTOTLE_USED: false
  NUMERICS_USED: false

ACQUISITION:
  REPORTED_OUTCOME: ONLY_C0_RATE_SOURCE_NEW_ANALYSIS_REQUIRED
  SEMANTIC_ADMISSION: PROVED_FOR_THE_INSPECTED_SOURCE_CHAIN
  INSPECTED_SOURCE_SCOPE:
    - MEIXNER_SCHAEFKE_SECTION_2_333_COMPLETE
    - MEIXNER_SCHAEFKE_SECTION_3_251_COMPLETE
    - MEIXNER_SCHAEFKE_SECTION_3_252_COMPLETE
  FIXED_MODE_C0_RATE: PAPER_PROVED
  FIXED_MODE_C1_OR_WEIGHTED_H1_RATE: ABSENT_IN_INSPECTED_CHAIN
  GLOBAL_ABSENCE_FROM_ALL_LITERATURE: NOT_CLAIMED
  FORMAL_DIFFERENTIATION_OF_C0_BIG_O: KILLED
  NEW_ANALYSIS_REQUIRED: true

SOURCE_INTERFACE_AUDIT:
  SATZ9_SOURCE_DATA:
    exact_derivative_and_flux_fields: true
    quantitative_derivative_remainder_field: false
  SELECTED_DIRECT_CYLINDER_RATE:
    consumes_value_rate_only: true
    consumes_derivative_rate: false
  CENTER_ANCHOR:
    exact_value_match_at_zero: true
    fitted_scalar: false

H2A_4_1B_3C_1_2:
  CODE: H2A_4_1B_3C_1_2_SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_JUMP_RATE_PREFLIGHT
  MODE: READ_ONLY_MATH
  LEAN_EDIT: false
  ARISTOTLE_AUTHORIZED: false
  NUMERICS: false
  OUTPUT: docs/routeB_bus/H2A_4_1B_3C_1_2_SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_JUMP_RATE_PREFLIGHT_2026-08-23.md
  RETURN_EXACTLY_ONE:
    - ODE_FLUX_ROUTE_GIVES_SUBCRITICAL_ESTAR_BUDGET
    - DIFFERENTIATED_KERNEL_ROUTE_GIVES_SUBCRITICAL_ESTAR_BUDGET
    - SEAM_BUDGET_SUBCRITICAL_INTERIOR_MULTIPLICATIVE_BOUND_OPEN
    - FIXED_MODE_C1_TOO_WEAK_AFTER_ESTAR
    - DERIVATIVE_ROUTE_RATE_FATAL_FOR_SELECTED_SCHEDULE

DIRECT_FIXED_MODE_C1_LEAN:
  AUTHORIZED: false
  REASON: >-
    A fixed-mode interior derivative theorem is not the consumer.  The consumer
    is the finite mode-weighted energy of the zero-extended, dilated E-star
    packet after center normalization and the precommitted selected schedule.

ARSENAL_MANDATE:
  ACCEPTED: true
  CARDS_USED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

SUCCESS: H2A_4_1B_3C_1_1_FIXED_MODE_C1_SOURCE_ACQUISITION_SEMANTICALLY_ADMITTED
FAILURE: H2A_4_1B_3C_1_2_ESTAR_DERIVATIVE_OR_JUMP_RATE_GAP

PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. What the acquisition closed

The bounded source question is now answered.

Meixner–Schäfke §2.333, §3.251 and §3.252 contain value-level or mean-square
asymptotics, but no quantitative estimate for the derivative of the remainder
and no weighted-H1 estimate.  The exact derivatives occurring on those pages
belong to residual identities or sign normalizations; they are not derivative
remainder estimates.

The strongest theorem available from the inspected chain therefore remains:

```text
fixed source mode, after its own normalization
  -> C0 error O(gamma^(-1))
  -> physical C0 error O(lambda^(-2)).
```

This conclusion is restricted to the named inspected source chain.  It is not a
claim that no derivative estimate exists anywhere in the literature.

`[ABSTRACT][PAPER]`

### 2. The project interface confirms the source boundary

`Satz9SourceData` and `ProjectModeData` carry exact `HasDerivAt` and exact
prolate flux identities on the open physical window.  They carry no numerical
rate for the derivative error.

`selectedFerrers_directCylinderRate_of_explicitSatz9RawRates` consumes only the
pointwise value contracts

```text
norm(scale * p(x) - cylinderTarget(x)) <= rawC / gamma.
```

No derivative contract is hidden in that theorem.

The center scalars are source-derived and precommitted.  They imply exact value
matching at the center.  Parity supplies the corresponding zero derivative at
the center once differentiability is used.  These are useful initial conditions
for a new ODE/flux analysis, but they are not themselves a derivative rate.

`[ABSTRACT][LEAN]`

### 3. Strongest attack on the positive finding

The report correctly notices that the exact integral identity used in §2.333
can be differentiated.  This is a legitimate candidate because the identity,
not the C0 big-O term, is differentiated.

It is not yet a theorem and it is not yet a useful rate.

A successful proof still has to establish all of the following:

1. a derivative-independent integrable majorant for the differentiated kernel;
2. the exact power of the large parameter lost by the differentiated kernel;
3. transport from the Mathieu prototype to the literal spheroidal source mode;
4. center normalization and physical-coordinate scaling;
5. endpoint jumps of the zero extension;
6. all dilation seams of the E-star sum;
7. conversion to the literal finite `CCMModeFinite` mode-weighted energy.

Calling the first four items a `C1 rate` and omitting the last three would prove
a surrogate.  This is a **C10 FUNCTIONAL-NOT-SURROGATE** kill.

Interior C1 regularity and the distributional log derivative of the zero-extended
E-star packet are different objects.  They have the same physical coordinates
but different derivative laws because the latter contains endpoint and dilation
Dirac masses.  This is a **C04 SAME-COORDINATES-TWO-LAWS** boundary.

The selected schedule remains the precommitted one.  It may not be changed after
the exponent ledger is inspected.  This is the **C09 PRECOMMIT** firewall.

### 4. Why the next task is an exponent discriminator, not Lean

The already proved consumer is

```text
L_k * oddMass_k * GammaEnergy_k -> 0.
```

The proved odd-mass rate reduces this to the sufficient threshold

```text
GammaEnergy_k = o(sqrt(m_k) / L_k^2),
L_k = log(m_k),
m_k = N_k = k + 2.
```

A fixed-mode derivative estimate does not show that threshold.  The E-star sum
creates a moving finite dilation count and seams at

```text
t_(k,r) = log(lambda_k / r).
```

Before proving any new source theorem, one must determine whether the best
plausible derivative exponent survives:

```text
physical rescaling
+ E-star dilation
+ seam jumps
+ finite Fourier cutoff N_k = m_k
+ the exact log-window normalization.
```

This is the cheapest decisive test.  A subcritical exponent ledger authorizes
new analysis.  A supercritical ledger kills that representation before a large
proof is attempted.

## FINAL PROPOSAL

Run one read-only mathematical transaction:

```text
H2A_4_1B_3C_1_2_SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_JUMP_RATE_PREFLIGHT
```

### Exact objects

For physical degrees `j = 0, 4`, define the center-anchored physical error on the
literal selected window:

```text
e_(j,k)(x)
  = centerAnchorScalar_j(k) * selectedMode_(j,k)(x)
    - parabolicCylinderTarget_j(x).
```

Use the exact selected `lambda_k`, `gamma_k`, separation value and project ODE.
Do not introduce a new source family or a fitted scalar.

For the factor-four combined packet, derive the distributional log derivative
of the literal E-star error on the log window.  It must have the form

```text
D_t EStarError_k
  = interiorDensity_k(t) dt
    + sum_r jump_(k,r) delta_(t_(k,r)),
```

with all endpoints and every seam enumerated.

### Mandatory tests

#### Test A — exact center-normalized ODE defect

Derive, without asymptotic notation, the inhomogeneous equation satisfied by
`e_(j,k)` from:

```text
project prolate flux equation;
explicit parabolic-cylinder differential equation;
exact selected parameter crosswalk.
```

Record the exact forcing term and exact initial data at the center.  Decide
whether a Volterra, weighted-energy or flux estimate gives a useful derivative
rate without assuming a new spectral gap.

#### Test B — differentiated-kernel route

Differentiate the exact source integral representation, not its big-O result.
Compute the actual parameter loss of the differentiated kernel.  The spheroidal
integral relation must be source-verified; an analogy with the Mathieu formula
is not an import.

#### Test C — seam ledger

Derive the exact jump at each `u = lambda_k / r`, including the square-root
E-star prefactor and the center-anchored endpoint value.  From the existing C0
rate, compute the strongest source-derived bound on

```text
sum_r normSq(jump_(k,r)).
```

Do not replace this by the number of seams times the largest jump unless that
loss is explicitly compared with the critical rate.

#### Test D — finite Fourier conversion

Convert the interior density and jump measure to the literal finite
mode-weighted energy on `CCMModeFinite N_k`.  Use the exact interval length
`L_k` and the exact mode labels.  For the jump part, test a nonharmonic
large-sieve/Bessel bound at the actual seam locations.  A triangle inequality
that introduces a factor equal to the number of seams is only a kill bound.

#### Test E — critical-rate comparison

Return the final bound in the unit

```text
GammaEnergy_k / (sqrt(m_k) / L_k^2).
```

A claim of `small`, `polynomial` or `C1` without this comparison is incomplete.

### Candidate representations

```yaml
R1_PROJECT_ODE_FLUX_PLUS_MULTIPLICATIVE_ENERGY:
  role: PRIMARY
  reason: >-
    The exact selected ODE, flux, parity and center lock are already formalized
    on the correct project object.  This route avoids a new provenance bridge.
  kill_power: 10/10
  estimated_cost: 5/10

R2_DIFFERENTIATED_SOURCE_KERNEL_PLUS_SEAM_LARGE_SIEVE:
  role: RUNNER_UP
  reason: >-
    The source integral identity may provide a sharper fixed-mode derivative
    rate, but the spheroidal identity and the E-star seam transport are new.
  kill_power: 9/10
  estimated_cost: 7/10
```

### Required outcomes

Return exactly one:

```text
ODE_FLUX_ROUTE_GIVES_SUBCRITICAL_ESTAR_BUDGET

DIFFERENTIATED_KERNEL_ROUTE_GIVES_SUBCRITICAL_ESTAR_BUDGET

SEAM_BUDGET_SUBCRITICAL_INTERIOR_MULTIPLICATIVE_BOUND_OPEN

FIXED_MODE_C1_TOO_WEAK_AFTER_ESTAR

DERIVATIVE_ROUTE_RATE_FATAL_FOR_SELECTED_SCHEDULE
```

## STRONGEST ATTACK

A C1 estimate may be true and still be useless.

The E-star derivative contains a sum over dilations.  Bounding those terms by
absolute values can introduce a power of the dilation count and destroy the
required `o(sqrt(m)/log(m)^2)` scale.  Likewise, a small endpoint value per seam
is not enough if the Fourier conversion pays the square of the number of seams.

Therefore the next transaction must preserve either multiplicative
orthogonality, a Hardy/Mellin operator bound, or a sharp nonharmonic Fourier
inequality.  Otherwise it has not reached the consumer.

This does not prove that the derivative route is impossible.  It kills only the
shortcut

```text
fixed-mode C1 error -> Gamma source rate.
```

## CODEX DIRECTIVE

```text
NO LEAN SOURCE IS AUTHORIZED.
NO ARISTOTLE SUBMISSION IS AUTHORIZED.

Produce only:

docs/routeB_bus/
H2A_4_1B_3C_1_2_SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_JUMP_RATE_PREFLIGHT_2026-08-23.md

Use the five mandatory tests and return exactly one registered outcome code.
Do not change the selected schedule, source row, center anchors, factor four,
Rayleigh shift, or any admitted Lean file.
```

## META CLOSEOUT

**What became smaller?**

The literature question is closed.  The unknown is no longer “does Satz 9 hide
a derivative theorem?”  It is one explicit rate question for the distributional
log derivative of the selected E-star packet.

**What was killed?**

- formal differentiation of a C0 big-O;
- treating exact derivative data as a derivative remainder rate;
- treating interior C1 as zero-extension H1;
- treating fixed-mode C1 as the finite Gamma-energy consumer.

**What must not be tried again?**

Do not add a derivative-rate hypothesis to a thin receiver.  Do not formalize a
fixed-mode C1 theorem before its E-star exponent budget is known.

**Current smallest named gap:**

```text
SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_AND_JUMP_BUDGET
```

**Next cheapest decisive test:**

```text
ODE/flux versus differentiated-kernel exponent ledger on the exact selected
schedule, including every E-star seam.
```

**Fate of registered predictions:**

```text
P_C1_SOURCE_FOUND = 0.30:
  REFUTED.

P_NEW_DERIVATIVE_ANALYSIS_REQUIRED = 0.70:
  CONFIRMED.

P_ENDPOINT_JUMPS_LOAD_BEARING = 0.90:
  CONFIRMED.

RETROACTIVE_REPAIR:
  false.
```

**New registered predictions:**

```text
P_DERIVATIVE_BUDGET_1 = 0.82:
  the seam contribution is subcritical once a sharp Fourier/large-sieve bound
  is used; a seam-count triangle bound is supercritical.

P_DERIVATIVE_BUDGET_2 = 0.93:
  a fixed-mode C1 theorem alone does not close the E-star mode-weighted budget.

P_DERIVATIVE_BUDGET_3 = 0.68:
  the project ODE/flux route yields a useful weighted derivative estimate but
  still needs a multiplicative E-star operator inequality.

LIKELIEST_FAILURE:
  MULTIPLICATIVE_DILATION_OPERATOR_OR_SEAM_LARGE_SIEVE_GAP.
```

**Memory entry:**

```yaml
iteration:
  target: fixed-mode derivative source provenance
  status: PROGRESS
  failed_strategy: cite a derivative remainder from Satz 9
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SELECTED_FERRERS_ESTAR_LOG_DERIVATIVE_AND_JUMP_BUDGET
  invariant_learned: interior source derivatives and distributional E-star derivatives are different objects
  forbidden_future_move: formalize fixed-mode C1 before the full exponent ledger
  next_decisive_test: exact ODE/flux and seam-rate preflight
```
