# STATUS: OPEN — ORIENTED FULL-VOLTERRA IDENTITY RATIFIED; THE SMOOTH W02–PRIME-MAIN SOURCE HAS A UNIVERSAL `6/π` TOTAL-VARIATION CEILING

```yaml
PRIMARY: RATIFY_ORIENTED_FULL_VOLTERRA_AND_RUN_ENDPOINT_STIELTJES_DISCRIMINATOR
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: a31f2ef60c918460300dd035ef8703194c6ca86f
  REPORT_PATH: docs/routeB_bus/LINUX_ORIENTED_FULL_VOLTERRA_SOURCE_RATE_PREFLIGHT_GOAL058_2026-08-28.md
  REPORT_BLOB: 722d2252bd2bf90f5bbb5f7792fee19c86aa7044
  REPORT_LINES: 157
  PARENT_VERDICT_COMMIT: 53a99a3910262eafa8ef57a8def8d855aea27a9d
  REPORT_WAS_BRANCH_HEAD_AT_ADJUDICATION: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY_PLUS_DECLARED_NUMERIC_VERIFICATION
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false
  NUMERICS_OCCUPY_QUANTIFIER: false

ADJUDICATION:
  REPORTED_DISCRIMINATOR: HOLD
  REPORTED_CODE: ORIENTED_FULL_VOLTERRA_IDENTITY_WITHOUT_SOURCE_RATE
  DECISION: HOLD_RATIFIED_WITH_MASS_TERMINOLOGY_AND_SOURCE_CATEGORY_REPAIRS

  ORIENTED_ONE_FUNCTIONAL_IDENTITY: PAPER_PASS
  ENDPOINT_LAWS_J_ZERO_AT_0_AND_2PI: PAPER_PASS
  UNFOLDED_W02_ORIENTATION: PAPER_PASS
  FOLDING_WITHOUT_WINDING_SHADOW: KILLED_EXACTLY

  SMOOTH_W02_MINUS_CONTINUOUS_PRIME_MAIN:
    status: PAPER_PROVED
    object_class: FINITE_SIGNED_MEASURE
    exact_total_variation: "(2/pi)*(1-m^(-1/2))*(3-2*m^(-1/2))"
    uniform_upper_bound: "<= 6/pi"
    limit_as_m_to_infinity: "6/pi"
    exact_signed_total_mass: "-(2/pi)*(1-m^(-1/2))"

  REPORT_HEADLINE_EXACTLY_6_OVER_PI_FOR_EACH_M:
    status: REPAIRED
    reason: >-
      For finite m the exact total variation depends on m and is strictly below
      6/pi.  The m-independent statement is the universal upper bound; 6/pi is
      the limiting value and supremum over the cofinal family.

  FULL_ORIENTED_SOURCE_IS_A_FINITE_MEASURE: false
  FULL_ORIENTED_SOURCE_TOTAL_MASS: FORBIDDEN_OBJECT
  reason: >-
    The reflected archimedean density has a simple endpoint singularity with
    residue 1/(2*pi).  It acts continuously on endpoint-vanishing Lipschitz tests,
    but it has no finite total variation.

  SQRT_M_SMOOTH_MASS_OBSTRUCTION: CLOSED
  ARITHMETIC_CONTENT_AFTER_ORIENTATION:
    status: ONE_EXPLICIT_STIELTJES_FUNCTIONAL
    object: "d(psi(x)-x)/sqrt(x) paired with J(2*pi*log(m/x)/log(m))"
    consumer_rate: OPEN

LOCAL_PAPER_CONSEQUENCE:
  L: "log(m)"
  a: "L/(4*pi)"
  r: "m^(-1/2)"
  w02_continuous_density: >-
    [L/(2*pi^2)]*(sqrt(m)-2+1/sqrt(m))*exp(-a*t) dt on t>0.
  reflected_prime_main_density: >-
    [L*sqrt(m)/(2*pi^2)]*exp(-a*t) dt on 0<t<=2*pi.
  signed_smooth_density:
    on_0_2pi: "-[L/(2*pi^2)]*(2-r)*exp(-a*t) dt"
    on_2pi_infinity: >-
      [L/(2*pi^2)]*(sqrt(m)-2+r)*exp(-a*t) dt.
  exact_TV_derivation:
    first_piece: "(2/pi)*(2-r)*(1-r)"
    tail_piece: "(2/pi)*(1-r)^2"
    sum: "(2/pi)*(1-r)*(3-2*r) <= 6/pi"

ARCH_ENDPOINT_FUNCTIONAL_REPAIR:
  density_before_reflection: >-
    [L/(4*pi^2)]*exp(L*t/(4*pi))/sinh(L*t/(2*pi)) dt on 0<t<=2*pi.
  legal_test_class: "Lipschitz J with J(2*pi)=0"
  exact_moment_bound: >-
    |<R_*mu_arch,J>| <= (C_arch/L)*Lip(J), where
    C_arch = integral_0^infinity u*exp(u/2)/sinh(u) du < infinity.
  consequence: >-
    The complete nonarithmetic smooth functional is uniformly controlled in the
    mixed norm ||J||_infinity + Lip(J)/L, even though it is not a finite measure.

EXACT_REMAINING_ARITHMETIC_TARGET:
  psi: "psi(x)=sum_{n<=x} vonMangoldt(n)"
  E: "E(x)=psi(x)-x"
  t_m: "t_m(x)=2*pi*log(m/x)/log(m)"
  stieltjes_form: >-
    R_m(J)=-(1/pi)*integral_[1,m] J(t_m(x))/sqrt(x) dE(x),
    with the exact endpoint convention fixed from the source prime sum.
  endpoint_values:
    - "J(t_m(m))=J(0)=0"
    - "J(t_m(1))=J(2*pi)=0"
  expected_partial_summation_identity: >-
    R_m(J)=-(1/pi)*integral_1^m E(x)*x^(-3/2)*
      ((1/2)*J(t_m(x))+(2*pi/L)*J'(t_m(x))) dx.
  guard: >-
    The sign and endpoint convention must be re-derived from the literal source;
    the displayed identity is the precommitted target, not permission to repair
    signs after seeing a rate.

CLOSES:
  - ORIENTED_FULL_VOLTERRA_ONE_FUNCTIONAL_IDENTITY
  - SQRT_M_MASS_AS_AN_OBSTRUCTION_TO_THE_SMOOTH_W02_PRIME_MAIN_SOURCE
  - FOLDED_FIRST_MOMENT_WITHOUT_WINDING_SHADOW
  - DIAGONAL_AND_OFFDIAGONAL_AS_SEPARATE_PRIMARY_REPRESENTATIONS

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - QPROJECTED_P59_KERNEL_COMPACT_RATE
  - SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER
  - SelectedPhysicalFourierEnergyControl
  - ORIENTED_STIELTJES_DISCREPANCY_AGAINST_AN_ENDPOINT_VANISHING_TEST
  - COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_ORIENTED_STIELTJES_ENDPOINT_PARTIAL_SUMMATION_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_TRANSACTION_REQUIRED_OUTPUTS:
  - exact source sign, 1/pi factor, Stieltjes interval and endpoint convention
  - exact endpoint-free partial-summation identity
  - exact Duhamel bounds for J and J' on the literal pair y=Q*C^(-1)*kappa, q
  - comparison with the prior retained-prime wall after deleting the old endpoint term
  - coupled compact-rate ledger; no isolated prime norm and no component split
  - explicit statement whether the endpoint zero changes the exponent class or only removes a boundary term

NEXT_DISCRIMINATOR:
  PASS: ORIENTED_STIELTJES_ENDPOINT_CONSUMER_RATE_READY
  HOLD: ENDPOINT_PARTIAL_SUMMATION_IDENTITY_WITHOUT_COUPLED_RATE
  FAIL: ORIENTED_STIELTJES_REPRESENTATION_RETURNS_THE_OLD_PRIME_ACTION_WALL

CANDIDATE_REPRESENTATIONS:
  R1_ENDPOINT_STIELTJES_PARTIAL_SUMMATION:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 2/10
    object: >-
      Use J(0)=J(2*pi)=0 to remove both Stieltjes boundary terms exactly, then
      price the remaining E(x) integral against the literal Duhamel J/J' ledger.
  R2_REFLECTED_PRIME_JUMP_ABEL_WITHOUT_ABSOLUTE_E:
    rank: RUNNER_UP
    kill_power: 8/10
    proof_cost: 5/10
    object: >-
      Keep the discrete prime jumps and perform Abel summation directly in the
      reflected angle variable, preserving signs and the selected test instead of
      replacing E(x) by an absolute pointwise envelope.

REGISTERED_PREDICTIONS:
  P_STIELTJES_ENDPOINT_1:
    probability: 0.68
    prediction: >-
      Both boundary terms vanish exactly, but the strongest unconditional
      absolute envelope for E(x) still misses the required coupled compact rate;
      result HOLD, while the exact signed functional remains alive.
  P_STIELTJES_ENDPOINT_2:
    probability: 0.24
    prediction: >-
      The Q-projected Duhamel bounds and the endpoint weights jointly provide a
      consumer-strength rate not visible in the previous retained-prime pairing.
  P_STIELTJES_ENDPOINT_3:
    probability: 0.08
    prediction: >-
      A source sign, lower-endpoint or Stieltjes-convention correction is needed
      before the endpoint-free identity is exact.

PRIOR_PREDICTION_FATE:
  P_ORIENTED_VOLTERRA_1_0_72: CONFIRMED_AND_STRENGTHENED
  P_ORIENTED_VOLTERRA_2_0_20: PARTIAL_SMOOTH_SOURCE_GAIN_WITHOUT_FULL_RATE
  P_ORIENTED_VOLTERRA_3_0_08: NOT_REALIZED

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
  - REPRESENTATION_PROGRESS
  - FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
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
| The literal Q-projected consumer is one oriented full-Volterra functional | Accepted. | `[FINITE_CELL][PAPER]` |
| The numerical `2.5e-11` agreement proves the identity | No. It corroborates the finite algebra only. | `[FINITE_CELL][PAPER]` |
| Folding the nonperiodic first-moment kernel without extra data is legal | Killed; the winding shadow is exact and unavoidable. | `[FINITE_CELL][PAPER]` |
| The W02-minus-continuous-prime-main smooth source has size `sqrt(m)` | Killed. Its exact total variation is uniformly at most `6/pi`. | `[COFINAL_FAMILY][PAPER]` |
| Its total variation is exactly `6/pi` for every finite `m` | Rejected. It tends to `6/pi`; the universal ceiling is `6/pi`. | `[COFINAL_FAMILY][PAPER]` |
| The full oriented source is a finite signed measure of mass at most `6/pi` | Rejected. The Arch endpoint functional is not a finite measure. | `[COFINAL_FAMILY][PAPER]` |
| The complete nonarithmetic part has an `m`-independent functional bound on endpoint-vanishing tests | Accepted, in the mixed `sup + Lipschitz/L` test norm. | `[COFINAL_FAMILY][PAPER]` |
| All remaining arithmetic is one weighted von-Mangoldt Stieltjes discrepancy | Accepted after exact sign/domain lock in the next transaction. | `[COFINAL_FAMILY][PAPER]` |
| Consumer-strength compact rate follows | Not proved. | `[COFINAL_FAMILY][CONDITIONAL]` |

## FINAL PROPOSAL

The decision-changing result is not the asymptotic number `6/pi` by itself.  It
is the replacement

\[
\text{two source ledgers of size }\sqrt m
\quad\longrightarrow\quad
\text{one source functional with a universal smooth norm}
\]

before any inequality is applied.

Let `r=m^(-1/2)`.  On `(0,2*pi]` the continuous prime main exceeds the raw W02
density by

\[
\frac{L}{2\pi^2}(2-r)e^{-Lt/(4\pi)},
\]

while on `(2*pi,infinity)` only the W02 tail remains.  Their supports have
opposite signs, so the exact total variation is

\[
\boxed{
\|\sigma_{m,WP}^{smooth}\|_{TV}
=
\frac{2}{\pi}(1-r)(3-2r)
\le
\frac6\pi.
}
\]

The signed total mass is instead

\[
-\frac2\pi(1-r).
\]

Thus `6/pi` is a total-variation ceiling, not a signed mass and not the exact
finite-m value.

The reflected Arch term must remain in the category of endpoint-compensated
functionals.  From its exact density and `J(2*pi)=0`,

\[
|\langle R_*\mu_{arch},J\rangle|
\le
\frac{C_{arch}}{L}\operatorname{Lip}(J),
\qquad
C_{arch}:=
\int_0^\infty
u\frac{e^{u/2}}{\sinh u}\,du<\infty.
\]

Therefore the nonarithmetic source is uniformly bounded in the exact norm that
the Duhamel representation naturally supplies:

\[
|\Psi_m^{nonarith}|
\le
\frac6\pi\|J\|_\infty
+
\frac{C_{arch}}{L}\operatorname{Lip}(J).
\]

This is genuine progress.  But a bounded source is not a vanishing consumer:
`J=J_{y_m(z),q_m}` still depends on `m`, and its norm contains the graph inverse,
the Q-projected P59 kernel and the trial mode energy.

The only arithmetic object left is now explicit.  With

\[
E(x)=\psi(x)-x,
\qquad
 t_m(x)=\frac{2\pi\log(m/x)}{\log m},
\]

the next transaction must prove the exact Stieltjes partial-summation identity
with both boundary terms erased by

\[
J(t_m(m))=J(0)=0,
\qquad
J(t_m(1))=J(2\pi)=0.
\]

That is the cheapest test capable of deciding whether the new orientation has
actually changed the old prime exponent wall or has merely removed its largest
boundary term.

## STRONGEST ATTACK

The strongest objection is:

> A universal `6/pi` source bound sounds like the rate problem is solved.

It is not.  The bound controls the source while the test varies with `m`.  If

\[
\|J_m\|_\infty
\quad\text{or}\quad
\operatorname{Lip}(J_m)
\]

grows through `||Q C^{-1} kappa||`, the smooth contribution need not tend to
zero.  The arithmetic Stieltjes term may also reproduce the old retained-prime
wall after partial summation.  Neither issue is settled by bounded source mass.

The repaired claim is nevertheless substantial and durable:

\[
\boxed{
\text{the smooth W02/prime-main source no longer costs any positive power of }m.
}
\]

## CODEX DIRECTIVE

```text
NO LEAN OR CODEX EXECUTION AUTHORIZED.

NEXT PAPER-ONLY TASK:
  GOAL058_SELECTED_FERRERS_ORIENTED_STIELTJES_ENDPOINT_PARTIAL_SUMMATION_PREFLIGHT

DO EXACTLY:
  1. Lock the literal Stieltjes sign, 1/pi factor, interval and endpoint convention.
  2. Derive the endpoint-free integration-by-parts identity.
  3. Substitute exact Duhamel bounds for J and J' on y=Q*C^(-1)*kappa and q.
  4. Compare the resulting exponent ledger with report 49c3b916 after removing
     its old top-end boundary contribution.
  5. Return PASS only from the literal coupled compact rate.

FORBIDDEN:
  componentwise W02/Arch/Prime norms;
  calling the full source a finite measure;
  replacing the signed Stieltjes functional by an absolute envelope and then
  declaring the exact functional dead;
  treating failure of a sufficient PNT bound as proof that cancellation cannot occur;
  numerics or RH-strength prime estimates in a cofinal quantifier.
```

## META CLOSEOUT

**What became smaller?**

The source-scale obstruction shrank from two `sqrt(m)` ledgers to a universal
smooth functional plus one explicit Stieltjes discrepancy.

**What was killed?**

- `sqrt(m)` as an unavoidable smooth-source cost;
- a folded first-moment formula without a winding shadow;
- the statement that the full oriented source is a finite measure;
- `6/pi` as an exact finite-m signed mass.

**What must not be tried again?**

Separate norm estimates of W02, Arch and Prime, or another wrapper that renames
the same Stieltjes discrepancy without using the two endpoint zeros.

**Current smallest named gap?**

```text
ORIENTED_STIELTJES_DISCREPANCY_AGAINST_AN_ENDPOINT_VANISHING_TEST
```

**Next cheapest decisive test?**

Exact endpoint-free partial summation, followed by one coupled exponent ledger.

**Prior prediction fate?**

`P_ORIENTED_VOLTERRA_1` is confirmed and strengthened.  The representation is
more effective than predicted on the smooth source, but the consumer rate is
still open.

**Memory entry?**

```yaml
iteration:
  target: ORIENTED_FULL_VOLTERRA_CONSUMER_RATE
  status: PROGRESS
  failed_strategy: FOLDED_NONPERIODIC_FIRST_MOMENT_WITHOUT_SHADOW
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: ORIENTED_STIELTJES_DISCREPANCY_AGAINST_AN_ENDPOINT_VANISHING_TEST
  invariant_learned: preserve source orientation and the nonperiodic t*B channel
  forbidden_future_move: call 6/pi the exact full-source mass
  next_decisive_test: endpoint-free Stieltjes partial summation
```
