# STATUS: OPEN — ABSOLUTE STIELTJES MAJORANT KILLED; SIGNED ROUTE HELD BEHIND ONE ZERO-TRANSFER CIRCULARITY GATE

```yaml
PRIMARY: RATIFY_ABSOLUTE_STIELTJES_FAIL_AND_RUN_ZERO_TRANSFER_CIRCULARITY_PREFLIGHT
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: b11a33e0777b14451600658a509a746994b26a60
  REPORT_PATH: docs/routeB_bus/LINUX_ORIENTED_STIELTJES_DISCRIMINATOR_GOAL058_2026-08-28.md
  REPORT_BLOB: 3651ebaeb7056e00bd0382429284819a50bac456
  REPORT_LINES: 127
  PARENT_VERDICT_COMMIT: 5ec3b20c32346c1d3e710270451ab8fb73330fe6
  REPORT_WAS_BRANCH_HEAD_AT_ADJUDICATION: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY_PLUS_DECLARED_NUMERIC_EVALUATION
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false
  NUMERICS_OCCUPY_QUANTIFIER: false

ADJUDICATION:
  REPORTED_DISCRIMINATOR: FAIL
  REPORTED_CODE: ABSOLUTE_MAJORANT_OF_THE_STIELTJES_TERM_REIMPORTS_THE_SUBPOWER_WALL
  DECISION: FAIL_RATIFIED_FOR_ABSOLUTE_MAJORANT_ONLY

  ENDPOINT_FREE_PARTIAL_SUMMATION_IDENTITY: PAPER_PASS
  UPPER_ENDPOINT_TERM: EXACTLY_ZERO
  LOWER_ENDPOINT_TERM: EXACTLY_ZERO
  ENDPOINT_VANISHING_IS_LOAD_BEARING: true

  ABSOLUTE_E_MAJORANT_ROUTE: FATAL
  KOROBOV_VINOGRADOV_CLASS_PAYS_CONSUMER: false
  J_TERM_EXPONENT_CLASS: "exp(L/2-c*L^(3/5)+o(L^(3/5)))/L"
  JPRIME_TERM_EXPONENT_CLASS: "same class after its explicit 1/L factor"
  POLYNOMIAL_REGULARITY_IMPROVEMENT_CAN_REPAIR_EXPONENT_GAP: false

  SIGNED_ORIENTED_STIELTJES_ROUTE: NOT_ADJUDICATED
  SIGNED_RATE_MATHEMATICALLY_REFUTED: false
  ZERO_FREE_REGION_CONVERSE_FOR_LITERAL_SELECTED_J: NOT_YET_PROVED
  TRACKING_CORRIDOR_THAWED: false

REPORT_REPAIRS:
  phrase_majorant_diverges_at_every_size:
    verdict: REPAIRED
    replacement: >-
      The unconditional absolute upper bound grows without bound asymptotically;
      no claim about monotonicity or literal divergence at each finite m is needed.
  derivative_term:
    verdict: CARRIED_EXPLICITLY
    note: >-
      The report displays the J contribution.  The (2*pi/L)J' contribution has
      the same fatal exponential class under any polynomial Duhamel regularity
      budget and must remain in every ledger.
  C_arch_decimal:
    verdict: DIAGNOSTIC_ONLY
    theorem_strength: >-
      The load-bearing statement is finiteness of
      integral_0^infinity u*exp(u/2)/sinh(u) du and the resulting C_arch/L bound;
      the decimal 8.5986645773 is not a proof object.

SMOOTH_SOURCE_ASSET:
  exact_total_variation: "(2/pi)*(1-m^(-1/2))*(3-2*m^(-1/2))"
  uniform_ceiling: "6/pi"
  status: PRESERVED
  limitation: >-
    This is the W02-minus-continuous-prime-main smooth signed measure only.  The
    full oriented source is an endpoint-compensated functional, not a finite
    measure.

EXACT_REMAINING_ARITHMETIC_OBJECT:
  psi: "psi(x)=sum_{n<=x} vonMangoldt(n)"
  E: "E(x)=psi(x)-x"
  t_m: "t_m(x)=2*pi*log(m/x)/log(m)"
  R_m: >-
    R_m(J)=-(1/pi)*integral_1^m E(x)*x^(-3/2)*
      ((1/2)*J(t_m(x))+(2*pi/log(m))*J'(t_m(x))) dx.
  endpoint_values:
    - "J(0)=0"
    - "J(2*pi)=0"

ZERO_TRANSFER_COMPUTING_OBJECT:
  status: PRECOMMITTED_TARGET
  a_rho: "(rho-1/2)*log(m)/(2*pi)"
  r_rho: "exp(-2*pi*a_rho)=m^(-(rho-1/2))"
  transfer: >-
    T_{m,z}(rho)=integral_0^(2*pi) J_{m,z}(t)*exp(-a_rho*t) dt.
  expected_single_zero_shape: >-
    After source-locking the explicit-formula sign and endpoint convention, one
    zero term has magnitude proportional to
    (log(m)/(2*pi^2))*m^(rho-1/2)*T_{m,z}(rho).
  coefficient_form: >-
    If J(t)=sum_n omega_n*sin(n*t)+t*sum_n b_n*cos(n*t), then for Re(a)>0,
    T(a)=sum_n omega_n*n*(1-r)/(a^2+n^2)
      +sum_n b_n*((a^2-n^2)*(1-r)/(a^2+n^2)^2
                  -(2*pi*a*r)/(a^2+n^2)),
    with r=exp(-2*pi*a).  The removable exceptional denominators are handled by
    analytic continuation of the original finite integral.

ENDPOINT_ONLY_FALSIFIER:
  carrier_modes: [0, 1]
  Hilbert_kernel: "H_ij=1/(n_i-n_j), i!=j; H_ii=0"
  q: "e_0"
  y: "e_1"
  orthogonality: "<y,q>=0"
  resulting_test: "J(t)=sin(t)"
  endpoint_values: ["J(0)=0", "J(2*pi)=0"]
  transfer: "T(a)=(1-exp(-2*pi*a))/(a^2+1)"
  conclusion: >-
    Endpoint vanishing and Q-orthogonality alone do not annihilate a dangerous
    zero mode.  Any surviving cancellation must use the literal selected q,
    graph solution y=C^(-1)Q*kappa(z), and source coefficients.

CLOSES:
  - ABSOLUTE_MAJORANT_ROUTE_FOR_ORIENTED_STIELTJES_TERM
  - STIELTJES_BOUNDARY_TERM_UNCERTAINTY
  - ENDPOINT_VANISHING_AS_DECORATIVE_ONLY

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - QPROJECTED_P59_KERNEL_COMPACT_RATE
  - SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER
  - SelectedPhysicalFourierEnergyControl
  - SIGNED_ORIENTED_STIELTJES_EVALUATION_OR_ITS_CIRCULARITY_VERDICT
  - COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE

EXECUTION_PRIORITY:
  freeze_other_five_inputs_until_arithmetic_gate: true
  reason: >-
    Closing graph-floor or regularity suppliers is wasted work if the sole
    arithmetic functional is already zero-free-region strength.  Run the cheap
    exact circularity discriminator first.

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_ORIENTED_STIELTJES_ZERO_TRANSFER_CIRCULARITY_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_TRANSACTION_REQUIRED_OUTPUTS:
  - exact source-locked explicit formula for E=psi-x with signs and endpoint terms
  - exact derivation of the single-zero transfer coefficient T_{m,z}(rho)
  - exact finite alpha/beta coefficient form for the literal J=G+tB
  - specialization to q=selected Ferrers row and y=C^(-1)Q*kappa(z)
  - proof or refutation that z -> T_{m,z}(rho) is identically zero
  - P59 span gate: determine whether the Q-projected kernel rows span q-perp
  - exact condition under which a nonreal zero forces an Omega lower bound
  - classification of cancellation among a conjugate/functional-equation quartet
  - explicit statement whether the required compact rate implies a new zero-free region

NEXT_DISCRIMINATOR:
  PASS: SOURCE_FORCED_ZERO_TRANSFER_ANNIHILATION_READY
  HOLD: ZERO_TRANSFER_EXPLICIT_BUT_SELECTED_NONVANISHING_OR_CONVERSE_UNRESOLVED
  FAIL: SIGNED_ORIENTED_STIELTJES_RATE_IS_ZERO_FREE_REGION_STRENGTH

CANDIDATE_REPRESENTATIONS:
  R1_EXPLICIT_FORMULA_ZERO_TRANSFER_VECTOR:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 2/10
    object: >-
      Write the signed discrepancy as a sum of zero-transfer coefficients.  Use
      the finite Volterra coefficient formula and the P59 span property to decide
      whether a dangerous off-line zero is structurally annihilated or detected.
  R2_DISCRETE_PRIME_JUMP_VOLterra_ABEL:
    rank: RUNNER_UP
    kill_power: 8/10
    proof_cost: 5/10
    object: >-
      Keep individual von-Mangoldt jumps and the literal selected test without
      replacing E by an absolute envelope.  This route is admissible only if R1
      does not already classify the required estimate as zero-free-region
      strength.

REGISTERED_PREDICTIONS:
  P_ZERO_TRANSFER_1:
    probability: 0.74
    prediction: >-
      The selected transfer coefficient is not source-forced to vanish at an
      arbitrary off-line zero; the required signed rate is zero-free-region
      strength, and the oriented tracking corridor closes FATAL.
  P_ZERO_TRANSFER_2:
    probability: 0.18
    prediction: >-
      Q-projection plus the exact Volterra/graph structure creates an additional
      source factor that annihilates every dangerous zero contribution without
      assuming a zero-free region.
  P_ZERO_TRANSFER_3:
    probability: 0.08
    prediction: >-
      The explicit-formula sign, lower endpoint, or source category requires a
      repair before the transfer can be classified.

PRIOR_PREDICTION_FATE:
  P_STIELTJES_ENDPOINT_1_0_68: CONFIRMED_AND_STRENGTHENED
  P_STIELTJES_ENDPOINT_2_0_24: NOT_REALIZED_BY_ABSOLUTE_MAJORANT
  P_STIELTJES_ENDPOINT_3_0_08: NOT_REALIZED

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: DUALIZE
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| The endpoint-free Stieltjes identity is exact | Accepted with the report's source convention. Both boundary terms vanish because the test vanishes, including the lower endpoint where `E(1)=-1`. | `[COFINAL_FAMILY][PAPER]` |
| Endpoint vanishing supplies the missing power saving | Refuted. It buys powers of `log m`, while the majorant still contains the power-scale factor `m^(1/2)`. | `[COFINAL_FAMILY][PAPER]` |
| A Korobov--Vinogradov absolute envelope closes the consumer | Killed. Its saving is sub-power in `m`; the consumer needs a fixed-power-class improvement after all exact multipliers. | `[COFINAL_FAMILY][PAPER]` |
| The report has killed the exact signed Stieltjes functional | No. The report never uses its sign. | `[COFINAL_FAMILY][PAPER]` |
| Endpoint zeros alone annihilate off-critical zero contributions | Refuted by the two-mode plant `J(t)=sin t`. | `[ABSTRACT][PAPER]` |
| The selected source-specific signed rate is noncircular | Not established. | `[COFINAL_FAMILY][CONDITIONAL]` |
| The bounded smooth oriented source remains a real asset | Yes. Its exact finite-`m` total variation is below `6/pi`, with universal ceiling `6/pi`. | `[COFINAL_FAMILY][PAPER]` |

## 1. What the report closes

The partial-summation identity is a real theorem-shaped gain.  Let

\[
t_m(x)=\frac{2\pi\log(m/x)}{L},\qquad L=\log m.
\]

For

\[
f(x)=x^{-1/2}J(t_m(x)),
\]

we have

\[
f'(x)=-x^{-3/2}\left[
\frac12J(t_m(x))+\frac{2\pi}{L}J'(t_m(x))
\right].
\]

Both boundary terms in Stieltjes integration by parts vanish exactly:

\[
J(t_m(m))=J(0)=0,
\qquad
J(t_m(1))=J(2\pi)=0.
\]

Thus the arithmetic remainder is precisely

\[
R_m(J)=-\frac1\pi\int_1^m E(x)x^{-3/2}
\left[
\frac12J(t_m(x))+\frac{2\pi}{L}J'(t_m(x))
\right]dx.
\]

This removes a genuine boundary obstruction.  It does not remove the interior
arithmetic discrepancy.

## 2. Why the absolute route is dead

The strongest generic unconditional envelope has the form

\[
|E(x)|\le Cx\exp\{-c(\log x)^{3/5}(\log\log x)^{-1/5}\}.
\]

After `x=e^u`, the measure factor is of class

\[
e^{u/2-c u^{3/5+o(1)}}du.
\]

Near `u=L`, the first-order endpoint zero of `J` gives one factor `(L-u)/L`.
The derivative channel already carries an explicit `1/L`.  Both contributions
therefore remain of asymptotic class

\[
\frac1L\exp\{L/2-cL^{3/5+o(1)}\}.
\]

No polynomial bound on `J` or `J'` can reverse this exponent comparison.  An
exponentially decaying `J`-budget would itself be the missing tracking theorem;
it cannot be manufactured by the source majorant.

This ratifies the failure code

```text
ABSOLUTE_MAJORANT_OF_THE_STIELTJES_TERM_REIMPORTS_THE_SUBPOWER_WALL
```

for every argument that first discards the sign of `E`.

## 3. Strongest attack on the signed route

The phrase "the test vanishes at both endpoints" is not a signed-cancellation
theorem.

On two modes `n=0,1`, choose `q=e_0` and `y=e_1`.  They are orthogonal.  For the
discrete Hilbert matrix, the polarized current gives

\[
J(t)=\sin t.
\]

It satisfies

\[
J(0)=J(2\pi)=0,
\]

but for every `Re(a)>0`,

\[
\int_0^{2\pi}e^{-at}\sin t\,dt
=
\frac{1-e^{-2\pi a}}{a^2+1}\ne0.
\]

Therefore endpoint vanishing and Q-projection alone do not kill the Laplace mode
associated with an off-critical zero.  Any surviving theorem must use the exact
selected row, exact graph inverse and exact source orientation.

Conditionally on the standard zero term `-x^rho/rho` in the source-locked
explicit formula, its contribution after the angle change has the shape

\[
\frac{L}{2\pi^2}m^{\rho-1/2}
\mathcal T_{m,z}(\rho),
\qquad
\mathcal T_{m,z}(\rho)=
\int_0^{2\pi}J_{m,z}(t)
 e^{-(\rho-1/2)Lt/(2\pi)}dt.
\]

A finite-order endpoint zero supplies only inverse powers of `L`; it cannot by
itself suppress `m^{Re(rho)-1/2}`.  The exact source sign and all remaining
explicit-formula terms are obligations of the next preflight, not assumptions of
this verdict.

## 4. Why one more preflight is legal

The old selected-Ferrers corridor was frozen after the combined-Gamma source
program failed.  The owner-authorized reentry subsequently changed the
representation genuinely:

```text
full source matrix action
→ Hilbert/Volterra current
→ Q-projected oriented one-functional source
→ bounded smooth W02-minus-prime-main part
→ one signed Stieltjes discrepancy.
```

That change closed the former `sqrt(m)` smooth-mass obstruction and therefore was
not another wrapper on the dead object.

Now the representation has reached its final cheap arithmetic gate.  One exact
zero-transfer audit is justified.  Continuing to graph-floor, energy or Lean work
before this gate would violate kill-power-per-cost discipline.

## FINAL PROPOSAL

Run exactly one paper/source-only discriminator on the literal selected test.
Do not attempt a signed estimate yet.

The discriminator must first convert a hypothetical zero contribution into the
finite transfer coefficient `T_{m,z}(rho)`.  It must then decide whether the
selected Q-projected P59 family forces that coefficient to vanish or whether the
family detects the zero.

If it detects the zero and a Turan/Ingham-type lower bound applies on the required
cofinal schedule, the signed rate is RH/zero-free-region strength and this
oriented tracking representation closes `FATAL`.

If an exact source factor annihilates the dangerous contribution, the route gains
a genuinely new arithmetic theorem and may proceed to the five constructed
suppliers.

## STRONGEST ATTACK

A signed sum can be smaller than its absolute majorant.  Therefore the failed
majorant does not kill the exact functional.

The counter-attack is equally strict: calling the remaining cancellation
"oscillation" proves nothing.  The selected kernel must exhibit an exact
annihilator or a source-independent small transfer coefficient.  Otherwise the
asserted cancellation is merely the desired zero-free conclusion written in
prime coordinates.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.

PAPER/SOURCE TASK ONLY:
  GOAL058_SELECTED_FERRERS_ORIENTED_STIELTJES_ZERO_TRANSFER_CIRCULARITY_PREFLIGHT

Read:
  docs/routeB_bus/LINUX_ORIENTED_STIELTJES_DISCRIMINATOR_GOAL058_2026-08-28.md
  docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_26_N_ORIENTED_FULL_VOLTERRA_UNIFORM_SMOOTH_VARIATION_AND_STIELTJES_DISCRIMINATOR_2026-08-28.md
  docs/routeB_bus/LINUX_REENTRY_TRACK1_PRIME_KERNEL_POWER_SAVING_DIRECT_GOAL058_2026-08-27.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteAssetBank.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersHilbertPairing.lean

Return one report with the exact required outputs from NEXT_TRANSACTION.
Do not edit Lean. Do not run numerics. Do not use RH, global Weil positivity,
the desired convergence, or a zero-free region as an input.
```

## META CLOSEOUT

**What became smaller?**

The arithmetic front is no longer "control the prime source." It is one finite
Laplace-transfer coefficient of the literal Volterra test against a hypothetical
zero mode.

**What was killed?**

Every absolute-value estimate of the Stieltjes discrepancy, including the full
Korobov--Vinogradov class.

**What must not be tried again?**

```text
|E|-majorants;
stronger PNT envelopes of the same sub-power class;
claiming endpoint vanishing supplies a power saving;
closing graph/energy suppliers before the arithmetic gate;
calling unspecified sign cancellation a theorem.
```

**Current smallest named gap?**

```text
SELECTED_ORIENTED_STIELTJES_ZERO_TRANSFER_NONVANISHING_OR_ANNIHILATION
```

**Next cheapest decisive test?**

Derive `T_{m,z}(rho)` exactly and decide whether it vanishes identically for the
selected Q-projected P59 family.

**Fate of prior predictions?**

```text
P_STIELTJES_ENDPOINT_1 (0.68): confirmed and strengthened.
P_STIELTJES_ENDPOINT_2 (0.24): not realized by the absolute route.
P_STIELTJES_ENDPOINT_3 (0.08): not realized.
```

**Memory entry**

```yaml
iteration:
  target: ORIENTED_STIELTJES_DISCREPANCY_AGAINST_ENDPOINT_VANISHING_TEST
  status: PROGRESS
  failed_strategy: ABSOLUTE_MAJORANT_OF_E
  cognitive_operator_used: DUALIZE
  new_gap_name: SELECTED_ORIENTED_STIELTJES_ZERO_TRANSFER_NONVANISHING_OR_ANNIHILATION
  invariant_learned: endpoint zeros remove boundary terms but only source-specific transfer can remove off-line zero modes
  forbidden_future_move: discard the sign of E or spend constructed-supplier work before the arithmetic gate
  next_decisive_test: exact zero-transfer coefficient and P59 span/circularity audit
```
