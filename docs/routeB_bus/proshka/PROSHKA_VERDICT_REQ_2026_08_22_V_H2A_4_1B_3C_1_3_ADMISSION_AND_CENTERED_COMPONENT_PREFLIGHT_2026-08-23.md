# STATUS: CONDITIONAL — E★→Γ CROSSWALK PREFLIGHT ADMITTED WITH SCALE/CENTERING REPAIRS; RAYLEIGH-CENTERED COMPONENT DISCRIMINATOR AUTHORIZED

```yaml
PRIMARY: ADMIT_ESTAR_TO_GAMMA_CROSSWALK_WITH_SCALE_AND_CENTERING_REPAIRS
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 2ad49d5eaf0ebda039a50279b331b4211a058458
  REPORT_PARENT: 1386ded14bfc732c64708cc523d5dd8b559316ab
  REPORT_PATH: docs/routeB_bus/H2A_4_1B_3C_1_3_SELECTED_FERRERS_ESTAR_TO_GAMMA_SOURCE_ACTION_CROSSWALK_PREFLIGHT_2026-08-23.md
  REPORT_GIT_BLOB: e82f3f30087ac2bb15d41b201c5d39f669608d85
  MODE: READ_ONLY
  LEAN_EDIT: false
  ARISTOTLE_USED: false
  NUMERICS_USED: false

PREFLIGHT:
  REPORTED_OUTCOME: DERIVATIVE_PROXIMITY_CONTROLS_ROW_NOT_RIESZ_RESIDUAL
  SEMANTIC_ADMISSION: CONDITIONAL_WITH_REPAIRS
  EXACT_TYPE_CHAIN: ADMITTED
  HDC_CONTROLS_PROJECTED_ERROR_DERIVATIVE: true
  HDC_DIRECTLY_CONTROLS_GAMMA: false
  PERIODIC_ENDPOINT_QUOTIENT: ADMITTED
  LARGE_SIEVE_THEOREM_IMPORTED: false

MANDATORY_REPAIRS:
  SCALE_LAW:
    reported_q_eq_t_error_plus_target: REJECTED
    exact_identity: s_k_smul_q_k_eq_t_k_smul_error_plus_target
    required_weight: t_k_squared_div_normSq_s_k
    anchor_ratio_bound_already_kernel_proved_private: true
    selectedTrialNormalizerBounded_as_new_owner_data: RETIRED_FOR_THIS_ROUTE
  W02:
    raw_W02_on_Dq_trace_as_load_bearing: REJECTED_PENDING_CORRECTED_COMPONENT_TEST
    reason: exact_consumer_includes_rank_two_commutator_correction
    card: C10_FUNCTIONAL_NOT_SURROGATE
  PRIME:
    no_representation_avoids_prime: NOT_ESTABLISHED
    raw_absolute_prime_bound: KILL_BOUND_ONLY
    rayleigh_centered_prime_commutator: OPEN_DISCRIMINATOR
  SCALARS:
    trial_normalizer_ratio: INTERNALLY_LEAN_PROVED
    selected_rayleigh_growth: OPEN

CLOSED_BY_THIS_ADJUDICATION:
  - ESTAR_DERIVATIVE_IS_NOT_GAMMA_SOURCE_ACTION
  - SOURCE_SCALE_OMISSION_IN_ROW_DERIVATIVE_LEDGER
  - PERIODIC_ENDPOINT_COLLISION_CLASSIFICATION

STILL_OPEN:
  - FACTOR_FOUR_TARGET_MODE_WEIGHTED_ENERGY
  - SELECTED_RAYLEIGH_GROWTH
  - RAYLEIGH_CENTERED_W02_COMPONENT_RATE
  - RAYLEIGH_CENTERED_PRIME_COMPONENT_RATE
  - FULL_COMBINED_GAMMA_SOURCE_RATE

NEXT:
  CODE: H2A_4_1B_3C_1_4_SELECTED_FERRERS_RAYLEIGH_CENTERED_COMPONENT_DISCRIMINATOR
  MODE: READ_ONLY
  LEAN_EDIT: false
  ARISTOTLE_AUTHORIZED: false
  NUMERICS: false
  OUTPUT: docs/routeB_bus/H2A_4_1B_3C_1_4_SELECTED_FERRERS_RAYLEIGH_CENTERED_COMPONENT_DISCRIMINATOR_2026-08-23.md

DIRECT_H2A_4_1B_3C_1_LEAN:
  AUTHORIZED: false

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

SUCCESS: H2A_4_1B_3C_1_3_ESTAR_TO_GAMMA_PREFLIGHT_SEMANTICALLY_ADMITTED_WITH_REPAIRS
FAILURE: H2A_4_1B_3C_1_4_CENTERED_COMPONENT_OR_PRIME_COMMUTATOR_GAP

PROGRESS_CLASS: FALSIFICATION_AND_REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| Exact physical-error / projection / finite-Riesz object chain | **ADMITTED** | `[COFINAL_FAMILY][LEAN]` |
| A derivative contract for the physical E★ error controls the projected error row | **ADMITTED CONDITIONALLY** | `[COFINAL_FAMILY][CONDITIONAL]` |
| The same derivative contract directly controls the finite Riesz residual or `Gamma` | **REJECTED** | `[COFINAL_FAMILY][PAPER]` |
| The endpoint collision `r=1` / `r=m` is repaired by one periodic quotient | **ADMITTED** | `[COFINAL_FAMILY][PAPER]` |
| A fresh upper bound on the bare trial normalizer is required | **REJECTED** | `[COFINAL_FAMILY][LEAN]` |
| A W02 derivative trace is already proved load-bearing | **REJECTED PENDING CORRECTED-COMPONENT TEST** | `[COFINAL_FAMILY][CONDITIONAL]` |
| The prime channel is unavoidable in every representation | **NOT ESTABLISHED** | `[COFINAL_FAMILY][CONDITIONAL]` |

The main report outcome survives:

```text
physical E★ derivative proximity
  -> projected coefficient derivative control;

physical E★ derivative proximity
  -/-> finite Riesz source-action control.
```

The report therefore made real progress.  Two of its secondary ledgers,
however, used the wrong scaling and the wrong W02 functional.

## 1. Exact type chain: admitted

The disk objects are correctly separated:

```text
physical full E★ error          : H_m after MemLp realization;
projected physical error eE_k   : E_m_N;
projected target gE_k           : E_m_N;
selected row q_k                : exact finite coefficient row of kTrial;
finite Riesz residual r_k       : (M_k - a_k I) q_k;
combined commutator defect      : Gamma_k = D_k r_k.
```

The physical error and `Gamma_k` use the same finite Fourier carrier only
after projection, but they obey different laws.  No ambient compression or
proximity-to-action inference exists on disk.  This is the correct **C04
SAME-COORDINATES-TWO-LAWS** boundary.

`[COFINAL_FAMILY][LEAN]`

## 2. Mandatory scale repair

The report states in Test 2:

```text
q_k = t_k * (eE_k + gE_k).
```

That is not the source theorem.  The exact kernel-checked identity is

\[
\boxed{
 s_k q_k = t_k(eE_k+gE_k),
}
\]

where `s_k` is the exact nonzero source scale and `t_k` is the trial
normalizer.  Consequently,

\[
D_kq_k=\frac{t_k}{s_k}\bigl(D_keE_k+D_kgE_k\bigr).
\]

The relevant scalar is therefore

\[
\frac{t_k^2}{|s_k|^2},
\]

not the bare `t_k`.

H2A.3 already proves internally, from the same center anchor used in the
odd-mass theorem,

\[
\boxed{
 \frac{t_k^2}{|s_k|^2}\le \frac{L_k}{b^2}
}
\]

eventually for a fixed positive anchor floor `b`.  The helper is private,
but it is kernel-checked and consumed by the public odd-mass rate.  Thus
`SelectedTrialNormalizerBounded` is not a new mathematical input for this
route.  A later substantive source theorem may re-export or locally reprove
the ratio; a separate thin wrapper is not authorized.

Under the hypothetical derivative contract

\[
\|D_keE_k\|^2=o\!\left(\frac{\sqrt{m_k}}{L_k^4}\right)
\]

and a target bound `||D_k gE_k||^2 = O(1)`, the correct source ledger gives

\[
\|D_kq_k\|^2
\le
2\frac{t_k^2}{|s_k|^2}
 \left(\|D_keE_k\|^2+\|D_kgE_k\|^2\right)
=
O(L_k)+o\!\left(\frac{\sqrt{m_k}}{L_k^3}\right).
\]

This remains subcritical against the current
`√m_k / L_k^2` `GammaEnergy` threshold.  The report's qualitative conclusion
about the row survives; its normalizer ledger does not.

`[COFINAL_FAMILY][LEAN]`

## 3. Mandatory W02 functional repair

The exact consumer is not the raw term

\[
(W02_k-a_kI)D_kq_k.
\]

It is the combined commutator-corrected defect.  For a literal structured
component `X_k`, define

\[
\begin{aligned}
a_{X,k}&=\operatorname{Re}\langle q_k,X_kq_k\rangle,\\
\beta_{X,k}(j)&=n_j(X_k)_{j,0},\\
A_k&=\mathbf1\cdot q_k,\\
B_{X,k}&=\beta_{X,k}\cdot q_k,
\end{aligned}
\]

and

\[
\boxed{
\Gamma_{X,k}
=(X_k-a_{X,k}I)D_kq_k+A_k\beta_{X,k}-B_{X,k}\mathbf1.
}
\]

The exact structured commutator law gives

\[
\boxed{
\Gamma_{X,k}=D_k(X_k-a_{X,k}I)q_k.
}
\]

For the W02 component this matters decisively.  `W02_k q_k` is rank two and
is determined by the two endpoint functionals of `q_k` itself.  Expanding
`D_k(W02_kq_k-a_{W02,k}q_k)` therefore uses value-level endpoint moments,
fixed mode-weighted endpoint vectors, and `D_kq_k`.  It need not pass through
endpoint functionals of `D_kq_k`.

The report's claimed W02 trace wall arose from estimating the raw first term
and dropping the rank-two commutator correction.  Until the corrected W02
component is expanded exactly, the boundary-trace input `N2` is not a
load-bearing supplier.  This is a direct **C10 FUNCTIONAL-NOT-SURROGATE**
repair: the consumer needs `Gamma_W02`, not raw `W02(Dq)`.

This does not prove the W02 rate.  It kills only the asserted necessity of a
new derivative-trace theorem.

`[COFINAL_FAMILY][CONDITIONAL]`

## 4. Prime status: open, but not globally unavoidable

The literal prime component still has no source-derived subcritical rate.
The ambient opNorm/Chebyshev estimate remains a valid kill bound and remains
supercritical.

But the object to test is the **Rayleigh-centered prime commutator defect**

\[
\boxed{
\Gamma_{P,k}
=D_k(P_k-a_{P,k}I)q_k,
}

or its equivalent commutator-corrected form, not raw `P_k(D_kq_k)`.
Rayleigh centering and the rank-two correction can remove a leading
nonoscillatory contribution.  The current report does not calculate this
centered finite von-Mangoldt sum.

Therefore the statement

```text
no representation avoids the prime wall
```

is too strong.  What is proved is only:

```text
raw separated prime action has no useful disk bound.
```

The full combined `Gamma_k` remains primary, because cancellation between
W02, WR and Prime is still legal.  Component estimates are diagnostics or
sufficient bounds, never the definition of the consumer.

`[COFINAL_FAMILY][CONDITIONAL]`

## 5. Periodic endpoint quotient: admitted

The endpoint phases `+1/2` and `-1/2` are one Fourier class.  Merging them
before applying any nonharmonic sieve is mandatory.  The elementary quotient
keeps the combined atom in the `O(m^{-3/2})` squared-amplitude class and leaves
all remaining classes separated by `c/(mL)`.  Hence the previously computed
seam exponent remains subcritical at constant cost.

The large-sieve inequality itself is still an external, unimported theorem.
The exponent ledger is admitted conditionally; no Lean or paper import is
claimed.

`[COFINAL_FAMILY][PAPER]`

## FINAL PROPOSAL

Run one read-only discriminator before any new Lean source:

```text
H2A_4_1B_3C_1_4_SELECTED_FERRERS_RAYLEIGH_CENTERED_COMPONENT_DISCRIMINATOR
```

Output:

```text
docs/routeB_bus/
H2A_4_1B_3C_1_4_SELECTED_FERRERS_RAYLEIGH_CENTERED_COMPONENT_DISCRIMINATOR_2026-08-23.md
```

### Exact source objects

Use the literal decomposition from `ccmWeilTauN1`:

\[
M_k=W02_k-WR_k-Prime_k.
\]

Do not rename signs.  For each component `X in {W02, WR, Prime}` construct
only in the report:

```text
component matrix X_k;
component beta vector beta_X,k;
component Rayleigh scalar a_X,k;
component beta moment B_X,k;
component corrected defect Gamma_X,k.
```

First verify exactly:

\[
a_k=a_{W02,k}-a_{WR,k}-a_{Prime,k},
\]

\[
\beta_k=\beta_{W02,k}-\beta_{WR,k}-\beta_{Prime,k},
\]

and

\[
\boxed{
\Gamma_k
=
\Gamma_{W02,k}-\Gamma_{WR,k}-\Gamma_{Prime,k}.
}
\]

Every scalar uses the same complex selected row, carrier, Rayleigh convention,
and precommitted schedule.

### Mandatory preflight searches

Run `ask.sh` before naming any new supplier:

```text
selected Ferrers Rayleigh centered component commutator
W02 corrected commutator endpoint rank two
prime Rayleigh centered von Mangoldt pairing
selected sourceScale trial normalizer anchor ratio
```

### Mandatory tests

#### Test 1 — scale omission plant

Use a one-dimensional scalar example with `s != 1` satisfying

```text
s*x = t*(e+g)
```

but not

```text
x = t*(e+g).
```

Record the exact `t/|s|` consumer and the existing anchor ratio theorem.

#### Test 2 — exact component decomposition

Check all signs against the literal `W02 - WR - Prime` source definition.
Check complex conjugation and real-part conventions in every component
Rayleigh scalar.  A component whose matrix or beta vector is not already
source-locked returns object-mismatch, not a guessed definition.

#### Test 3 — corrected W02 expansion

Expand

\[
\Gamma_{W02,k}=D_k(W02_k-a_{W02,k}I)q_k
\]

using the two exact W02 endpoint functionals and their fixed coefficient
vectors.  Decide whether any endpoint functional of `D_kq_k` remains after
the correction is retained.

Required falsifier: exhibit an exact small structured matrix/eigenvector for
which raw `(X-aI)Dq` is nonzero while the corrected commutator defect is zero.
This prevents raw action from being relabeled as `Gamma_X`.

#### Test 4 — centered prime pairing

Derive the exact finite von-Mangoldt expression for

\[
\Gamma_{Prime,k}=D_k(Prime_k-a_{Prime,k}I)q_k.
\]

Keep the full signed/oscillatory sum.  Determine whether Rayleigh centering
removes the leading Chebyshev-scale term or leaves the same
`m^{1/4} log m`-class kill bound after the known physical error rate.

No absolute-value sum may be used as a positive route.

#### Test 5 — target and scalar ledger

Recompute the row derivative with the correct `t_k/|s_k|` factor.  Separate:

```text
factor-four target mode-weighted energy;
selected Rayleigh growth;
component Rayleigh growth;
source-scale/normalizer ratio.
```

Do not reopen the bare trial-normalizer supplier.

#### Test 6 — cancellation firewall

The exact consumer remains the full `Gamma_k`.  The report must repeat the
existing plant where a combined residual vanishes although separated terms
are nonzero.  No componentwise norm sum may be promoted from sufficient bound
to necessary representation.

### Required outcome

Return exactly one:

```text
CENTERED_COMPONENTS_GIVE_SUBCRITICAL_CONTRACT

W02_CENTERED_DEFECT_CLOSED_PRIME_CENTERED_OSCILLATION_OPEN

W02_TRACE_REMAINS_LOAD_BEARING

COMPONENT_SPLIT_DESTROYS_NECESSARY_CANCELLATION

SOURCE_COMPONENT_DECOMPOSITION_OBJECT_MISMATCH
```

### Candidate representations

```yaml
R1_RAYLEIGH_CENTERED_COMPONENT_COMMUTATOR:
  role: PRIMARY_DIAGNOSTIC
  kill_power: 9/10
  estimated_cost: 4/10
  preservation:
    - exact selected row
    - exact carrier and schedule
    - exact full Gamma reconstruction
    - component Rayleigh centering

R2_FULL_SOURCE_WEIL_MELLIN_RADICAL_IDENTITY:
  role: RUNNER_UP
  kill_power: 10/10
  estimated_cost: 8/10
  reason: >-
    A full source-form or radical identity could preserve W02/WR/Prime
    cancellation and bypass every separated component estimate.  It is more
    powerful but substantially more expensive and has no disk theorem yet.
```

### FORBIDDEN

```text
q_k = t_k*(eE_k+gE_k) without division by sourceScale;
reopening SelectedTrialNormalizerBounded as a source input;
calling raw W02(Dq) the corrected W02 defect;
calling raw Prime(Dq) the centered prime defect;
declaring prime unavoidable before the centered calculation;
replacing full Gamma by a sum of component norms;
using absolute von-Mangoldt sums as a positive rate;
using inversion-evenness as a target action theorem;
using the large sieve before the periodic endpoint quotient;
writing Lean, running numerics, or submitting Aristotle.
```

## STRONGEST ATTACK

The centered component decomposition may still be the wrong positive route.
Even if each component is source-locked, the only useful cancellation may occur
between W02, WR and Prime.  A componentwise upper bound can therefore remain
supercritical while the full `Gamma_k` is small.

The next transaction is only a discriminator.  It is authorized because it can
kill the W02 trace wall and measure the centered prime term cheaply.  It is not
a license to replace the full consumer by three independent estimates.

This is the same **C10 FUNCTIONAL-NOT-SURROGATE** firewall applied one level
deeper.

## CODEX DIRECTIVE

```text
NO LEAN SOURCE IS AUTHORIZED.
NO ARISTOTLE SUBMISSION IS AUTHORIZED.
NO NUMERICAL RUN IS AUTHORIZED.

Produce only:

docs/routeB_bus/
H2A_4_1B_3C_1_4_SELECTED_FERRERS_RAYLEIGH_CENTERED_COMPONENT_DISCRIMINATOR_2026-08-23.md

Use the six mandatory tests and return exactly one registered outcome code.
Do not modify the selected row, source matrix, source scale, Rayleigh shift,
precommitted schedule, or any admitted Lean file.
```

## META CLOSEOUT

**What became smaller?**

The physical derivative route is now typed correctly.  The bare normalizer is
removed from the open ledger, and the alleged W02 derivative-trace wall is
reduced to one exact corrected-component calculation.

**What was killed?**

- `q_k = t_k(eE_k+gE_k)` without the source scale;
- the claim that a fresh bare-normalizer bound is required;
- raw W02-on-`Dq` as the exact consumer;
- the global claim that no representation can avoid the prime wall.

**What must not be tried again?**

Do not infer source action from physical proximity.  Do not drop the
commutator correction.  Do not turn a sufficient component triangle bound into
the definition of `Gamma`.

**Current smallest named gap:**

```text
RAYLEIGH_CENTERED_PRIME_COMMUTATOR_SOURCE_RATE
```

This name is provisional until Test 4 confirms that W02 closes and the centered
prime term remains open.

**Next cheapest decisive test:**

```text
exact W02/WR/Prime centered component expansion on the selected row.
```

**Fate of prior registered predictions:**

```text
P_GAMMA_CROSSWALK_1:
  CONFIRMED.

P_GAMMA_CROSSWALK_2:
  CONFIRMED AT THE MAIN TYPE BOUNDARY,
  REPAIRED ON NORMALIZER AND W02 SECONDARY LEDGERS.

P_GAMMA_CROSSWALK_3:
  CONFIRMED.

RETROACTIVE_REPAIR:
  false.
```

**New registered predictions:**

```text
P_CENTERED_COMPONENT_1 = 0.99:
  the existing anchor theorem removes the bare-normalizer input.

P_CENTERED_COMPONENT_2 = 0.90:
  the corrected W02 expansion removes endpoint traces of Dq and uses only
  value-level endpoint moments plus Dq.

P_CENTERED_COMPONENT_3 = 0.72:
  after W02 correction, the centered prime term remains the only substantive
  component source-rate wall.

P_CENTERED_COMPONENT_4 = 0.82:
  the explicit factor-four target admits a polynomial-log mode-weighted/action
  bound without new paper input.

LIKELIEST_FAILURE:
  PRIME_RAYLEIGH_CENTERING_GIVES_NO_ASYMPTOTIC_GAIN_OR_COMPONENT_SIGN_MISMATCH.
```

```yaml
iteration:
  target: EStar derivative to finite Riesz Gamma crosswalk
  status: PROGRESS
  failed_strategy: raw component action ledger
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: RAYLEIGH_CENTERED_PRIME_COMMUTATOR_SOURCE_RATE
  invariant_learned: source scale and commutator correction are part of the consumer
  forbidden_future_move: estimate raw W02 or Prime action as if it were Gamma
  next_decisive_test: exact centered component decomposition and prime rate ledger
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
```
