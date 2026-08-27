# STATUS: OPEN — PRIME-COUNT SCALE MATCH RATIFIED; COUNT-ONLY SHORTCUT REJECTED; PRIME-POWER ANNIHILATOR SELECTED

```yaml
PRIMARY: RUN_PRIME_POWER_ANNIHILATOR_CONSUMER_PREFLIGHT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-26-N

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PARENT_HEAD: eeb1877707b03962d57b6f36cf0e008564067a70
  PARENT_VERDICT_PATH: >-
    docs/routeB_bus/proshka/
    PROSHKA_VERDICT_REQ_2026_08_26_N_ORDERED_BETA_HOLD_POLARIZED_EXACT_CONSUMER_REPAIR_2026-08-27.md

WRITE_PROTOCOL:
  DIRECT_REPO_WRITE_AVAILABLE: true
  VERDICT_ONLY: true
  LEAN_SOURCE_WRITTEN: false
  KERNEL_VALIDATION_REQUIRED_FOR_THIS_COMMIT: false

ADJUDICATION:
  USER_PRIME_COUNT_INSIGHT: RATIFIED_AFTER_TYPE_REPAIR
  EXACT_IDENTITY_m_over_log_m_eq_prime_count: false
  ASYMPTOTIC_m_over_log_m_sim_prime_count: true
  SELECTED_SAMPLE_HEIGHT:
    exact: T_m = 2*pi*m/log(m)
    asymptotic: T_m ~ 2*pi*pi(m)
  SOURCE_ARITHMETIC_SUPPORT: PRIME_POWERS_NOT_ONLY_PRIMES
  PRIME_POWER_COUNT:
    exact: J_pp(m) = sum_{r>=1} pi(m^(1/r))
    asymptotic: J_pp(m) ~ m/log(m)
  EFFECTIVE_RECURRENCE_ORDER:
    statement: at_most_twice_the_number_of_distinct_effective_frequency_classes
    upper_bound: 2*J_pp(m)
    exact_equality_claimed: false
  OVERSAMPLING:
    selected_schedule: N=m
    sample_count: 2*m+1
    arithmetic_frequency_count: asymptotic_m_over_log_m
    factor: asymptotic_log_m

  COUNT_ONLY_CONSUMER_BOUND: REJECTED_C10
  PRIME_COUNT_EXPLICIT_FORMULA_USING_ZETA_ZEROS: FORBIDDEN_CIRCULAR_INPUT
  FINITE_EXACT_PRIME_COUNT_ALGORITHM: ALLOWED_FOR_DIAGNOSTIC_OR_FINITE_CERTIFICATE
  CHANGE_SELECTED_SCHEDULE_TO_PRIME_INDEXED: FORBIDDEN_WITHOUT_NEW_OWNER_PRECOMMIT_C09

  SPECIAL_LINE_INTERSECTION_CLAIM:
    status: QUARANTINED_PENDING_EXACT_OBJECT_LOCK
    reason: >-
      No source-locked declaration or formula identifying the user's line family
      and its intersection set was located.  The preflight must name the literal
      functions before using their intersections.

CURRENT_EXACT_CONSUMER:
  left_vector: x_k(z) = C_k^(-1) * kappa_k(z)
  right_vector: q_k = selected_Ferrers_trial_row
  residual: r_k = (M_k-a_k*I)q_k
  scalar: inner(x_k(z),r_k)
  channels:
    - diagonal_source_action
    - polarized_ordered_beta_cut_flux

SELECTED_REPRESENTATION:
  name: PRIME_POWER_ANNIHILATOR_ADJOINT_RANGE
  prime_frequency:
    z_q: exp(2*pi*i*log(q)/log(m))
    q_range: q=p^r<=m with vonMangoldt(q)!=0
  annihilator:
    form: product_over_distinct_effective_classes (S-z_q)*(S-conj(z_q))
    endpoint_and_conjugate_collisions: must_be_deduplicated
  exact_target: >-
    Represent the literal polarized consumer weight, including its diagonal
    companion, as an adjoint-annihilator image plus a controlled finite boundary
    term.  Then eliminate the prime bulk algebraically and reassemble the complete
    W02-Arch-Prime source action without componentwise norm splitting.

DECISION_CHANGING_OBSERVATION: >-
  The selected source row supplies 2m+1 mode samples but its prime contribution
  contains only about m/log(m) distinct prime-power frequencies.  Therefore it
  lies in a highly oversampled finite-exponential class and obeys many exact
  linear recurrence relations.  This is stronger and more useful than merely
  knowing pi(m).

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_PRIME_POWER_ANNIHILATOR_CONSUMER_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false
  CATALOG_QUERY_REQUIRED_BEFORE_SOURCE: true

NEXT_DISCRIMINATOR:
  PASS: PRIME_POWER_ANNIHILATOR_REDUCES_LITERAL_POLARIZED_CONSUMER_TO_CONTROLLED_BOUNDARY_MOMENTS
  HOLD: PRIME_POWER_RECURRENCE_EXACT_BUT_ADJOINT_PREIMAGE_OR_BOUNDARY_RATE_UNCONTROLLED
  FAIL: ANNIHILATOR_COEFFICIENT_GROWTH_OR_CONSUMER_RANGE_DEFECT_REIMPORTS_PRIME_WALL

MANDATORY_OUTPUTS:
  - exact_prime_power_support_and_effective_frequency_quotient
  - exact_J_pp_count_and_selected_height_relation
  - exact_finite_recurrence_for_prime_beta_and_prime_diagonal_sequences
  - exact_special_line_family_and_intersection_theorem_or_explicit_NO_MATCH
  - exact_polarized_consumer_weight_with_diagonal_channel
  - adjoint_range_decomposition_weight_equals_Astar_u_plus_boundary
  - coefficient_conditioning_and_boundary_budget
  - full_source_reassembly_without_component_norm_split
  - explicit_consumer_strength_compact_rate_ledger

FORBIDDEN:
  - replace_vonMangoldt_support_by_primes_only
  - write_T_m_equals_2*pi*pi(m)_exactly
  - use_Riemann_explicit_prime_counting_formula_as_an_unconditional_input
  - change_the_precommitted_selected_schedule_after_seeing_the_count
  - infer_weighted_signed_cancellation_from_pi(m)_alone
  - use_a_line_intersection_picture_without_literal_equations
  - componentwise_absolute_value_estimates_that_destroy_W02_Arch_Prime_cancellation
  - claim_recurrence_order_exact_without_collision_audit

CANDIDATE_REPRESENTATIONS:
  R1_PRIME_POWER_ANNIHILATOR_ADJOINT_RANGE:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 4/10
  R2_STIELTJES_PSI_INTEGRAL:
    rank: RUNNER_UP
    kill_power: 7/10
    proof_cost: 5/10
    object: >-
      Rewrite the prime component as an integral against d psi(x), preserving
      the exact consumer kernel.  Do not use an RH-conditional remainder.

REGISTERED_PREDICTIONS:
  P_ANNIHILATOR_1:
    probability: 0.55
    prediction: >-
      The exact recurrence closes, but the literal consumer weight has no
      polynomially controlled adjoint preimage; result HOLD.
  P_ANNIHILATOR_2:
    probability: 0.30
    prediction: >-
      The P59/Ferrers structure places the consumer weight in the annihilator
      adjoint range modulo finitely many boundary moments, yielding PASS.
  P_ANNIHILATOR_3:
    probability: 0.15
    prediction: >-
      Annihilator coefficients or inverse conditioning grow exponentially and
      the representation is killed as the old prime wall in disguise.

CLOSES:
  - PRIME_COUNT_TRANSITION_SCALE_CLASSIFICATION
  - PRIME_VS_PRIME_POWER_SUPPORT_REPAIR
  - COUNT_ONLY_CANCELLATION_SHORTCUT_KILL

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_POLARIZED_ORDERED_COMPLETED_BETA_SOURCE_ACTION_COMPACT_DECAY
  - LITERAL_CCM_DIAGONAL_SOURCE_ACTION_COMPACT_BOUND
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_GROUND_TO_TRIAL_LOCALLY_UNIFORM_CONVERGENCE

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. The user's scale observation is real

For the literal CCM prime central-column sequence, with `L=log m`,

\[
\beta_n^{\rm prime}
=-\frac1\pi
\sum_{q\le m}
\frac{\Lambda(q)}{\sqrt q}
\sin\!\left(\frac{2\pi n\log q}{\log m}\right).
\]

On the selected schedule the mode carrier is `-m,...,m`.  Hence the sampled
height is

\[
t_n=\frac{2\pi n}{\log m},
\qquad
T_m=\frac{2\pi m}{\log m}.
\]

The prime number theorem gives

\[
\pi(m)\sim\frac{m}{\log m},
\]

and therefore

\[
\boxed{T_m\sim2\pi\pi(m).}
\]

This is a genuine scale match.  It is not an exact identity.

### 2. The source counts prime powers

The source is weighted by the von Mangoldt function.  Its nonzero support is

\[
\mathcal Q_m=\{p^r\le m:p\text{ prime},\ r\ge1\}.
\]

The exact support count is

\[
J_{\rm pp}(m)
=\sum_{r\ge1}\pi(m^{1/r}),
\]

and

\[
J_{\rm pp}(m)
=\pi(m)+O(\sqrt m/\log m)
\sim\frac{m}{\log m}.
\]

Thus the user's asymptotic survives, but the exact finite object must count
prime powers, not only primes.  Replacing `J_pp` by `pi(m)` in a finite theorem
would drop the entries `4,8,9,...` and violate the source object.

### 3. Three different coordinates must not be conflated

There are three scales:

1. the integer sample index `n`;
2. the physical sample height `t_n=2*pi*n/log(m)`;
3. the recurrence degree, bounded by twice the number of distinct effective
   prime-power frequency classes.

The statement

```text
transition point = 2*pi*number of primes
```

is meaningful only after naming which of these coordinates carries the
transition.  In physical height the outer selected sample satisfies the
asymptotic above.  A recurrence transition at mode index `n≈2J_pp(m)` would
instead occur at height of order

\[
\frac{4\pi m}{(\log m)^2}.
\]

The preflight must type this before using the word `transition`.

### 4. The real opportunity is an exact annihilating filter

For each effective prime-power frequency define

\[
z_q=\exp\!\left(\frac{2\pi i\log q}{\log m}\right).
\]

The prime beta sequence is a finite linear combination of `z_q^n` and
`z_q^{-n}`.  Consequently an exact shift polynomial annihilates it:

\[
A_m(S)\beta^{\rm prime}=0.
\]

After endpoint and conjugacy collisions are removed,

\[
\deg A_m\le2J_{\rm pp}(m)\sim\frac{2m}{\log m}.
\]

But the selected cell contains `2m+1` samples.  The arithmetic signal is
therefore oversampled by a factor of order `log m`.

This is the decision-changing content of the user's observation.  The count
alone is not an estimate, but it proves that the prime source belongs to a
low-complexity finite-exponential class with many exact recurrence relations.

The same frequency set appears in the prime part of the diagonal sequence,
which is a finite cosine field.  Therefore one annihilator can potentially
remove the prime bulk from both channels of the exact mixed consumer.

### 5. How this could close the consumer

Let `omega` be the exact ordered mixed weight produced by

\[
x_k(z)=C_k^{-1}\kappa_k(z)
\]

and the selected trial row.  If one can prove

\[
\omega=A_m(S)^*u+b_{\partial}
\]

with polynomially controlled `u` and finite boundary data, then

\[
\langle\beta^{\rm prime},\omega\rangle
=\langle A_m(S)\beta^{\rm prime},u\rangle
 +\langle\beta^{\rm prime},b_{\partial}\rangle
=\langle\beta^{\rm prime},b_{\partial}\rangle.
\]

The prime bulk disappears exactly.  The proof must then reassemble the
archimedean and W02 parts and the diagonal channel in their literal signs.
No componentwise absolute-value estimate is allowed.

This is the cheapest route with a chance to turn the prime count into an exact
consumer theorem.

### 6. Why the prime-counting formula alone is insufficient

The active scalar contains amplitudes and phases:

\[
\frac{\Lambda(q)}{\sqrt q}
\exp\!\left(\frac{2\pi i n\log q}{\log m}\right).
\]

The scalar `pi(m)` remembers only how many primes occur.  It forgets the
weights, prime powers, phases, ordering and the exact test vector.  Therefore

\[
\pi(m)\text{ known exactly}
\not\Longrightarrow
\text{the required signed pairing is small}.
\]

This is a direct `C10 FUNCTIONAL-NOT-SURROGATE` guard.

Exact finite prime-counting algorithms may be used for finite diagnostics or
certificates.  A Riemann explicit formula for `pi(x)` is not an independent
input here: it contains the zeta zeros and would risk importing the target
back into its own proof.

The inverse approximation

\[
y=\frac{m}{\log m}
\quad\Longrightarrow\quad
m=-yW_{-1}(-1/y)
\]

is useful for scale design, but it is not an exact prime-count theorem and it
does not authorize changing the precommitted selected schedule.

### 7. The line-intersection claim is not yet typed

The user also points to a family of straight lines generated by a special
function, whose intersections are said to occur at the same points.  That
could be highly relevant, but no literal equations or source declaration were
identified in the audited corpus.

For the obvious phase-line candidate

\[
\ell_q(n)=\frac{2\pi n\log q}{\log m},
\]

intersections modulo `2*pi` satisfy an arithmetic resonance condition such as

\[
n\log(q_1/q_2)\in\log(m)\mathbb Z,
\]

not automatically `n=pi(m)`.

Therefore the picture cannot occupy a theorem quantifier until the preflight
returns:

```text
SPECIAL_LINE_FAMILY_LOCK:
  exact function;
  exact variables and units;
  exact intersection set;
  exact relation to prime powers and selected mode nodes;
  exact consumer map.
```

If the claimed intersections do match the effective prime-power frequencies,
they may provide the missing adjoint-range decomposition.  If not, they are a
visual analogy and are rejected by `C04 SAME-COORDINATES-TWO-LAWS`.

## FINAL PROPOSAL

Run one read-only discriminator.  Do not prove a new prime number theorem and
do not change the selected Ferrers schedule.

The target is:

\[
\boxed{
\texttt{PRIME\_POWER\_ANNIHILATOR\_REDUCES\_LITERAL\_POLARIZED\_CONSUMER}
}
\]

The preflight first builds the exact recurrence and then asks one decisive
question:

> Does the literal P59/Ferrers mixed consumer weight lie in the adjoint range
> of that recurrence modulo controlled boundary moments?

A PASS changes the route: the prime bulk is eliminated algebraically.  A HOLD
retains a precise structured representation but no rate.  A FAIL kills the
annihilator route if its inverse conditioning or boundary ledger reproduces
the original prime wall.

## STRONGEST ATTACK

Low recurrence degree is not the same as small consumer action.  For any
nonzero finite exponential sequence, a test weight can align with it and make
the pairing large.  The route succeeds only from a theorem about the literal
consumer weight, not from dimension counting.

A second attack is conditioning.  The coefficients of `A_m` may grow
exponentially when frequencies cluster.  Then the formal annihilator is exact
but useless asymptotically.  The preflight must export coefficient and inverse
bounds, not just the polynomial identity.

## CODEX DIRECTIVE

```text
NO LEAN, NUMERICS, ARISTOTLE, OR CODEX EXECUTION.

TASK_ID:
  GOAL058_SELECTED_FERRERS_PRIME_POWER_ANNIHILATOR_CONSUMER_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

READ:
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersHilbertPairing.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteAssetBank.lean
  docs/routeB_bus/LINUX_ORDERED_BETA_HILBERT_PAIRING_PREFLIGHT_GOAL058_2026-08-27.md
  docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_26_N_ORDERED_BETA_HOLD_POLARIZED_EXACT_CONSUMER_REPAIR_2026-08-27.md

BEFORE NAMING A SOURCE THEOREM:
  ./ask.sh "prime power annihilator recurrence polarized Hilbert consumer"

REQUIRED:
  1. Define the exact effective prime-power frequency set, including q=m zero
     frequency, conjugate collisions q1*q2=m, and duplicate roots.
  2. Prove the exact finite recurrence for both the prime beta sine sequence
     and the prime diagonal cosine sequence.
  3. Lock sample index, physical height and recurrence degree separately.
  4. Locate and type the user's special line family.  Return NO_MATCH rather
     than inventing it.
  5. Write the literal mixed consumer weight and diagonal companion.
  6. Decide whether it equals A_m(S)^*u plus finite boundary data.
  7. Export polynomial bounds for annihilator coefficients, u and every
     boundary moment.
  8. Reassemble W02-Arch-Prime without componentwise norm splitting.
  9. Propagate the result to the exact compact consumer budget.

PASS:
  PRIME_POWER_ANNIHILATOR_REDUCES_LITERAL_POLARIZED_CONSUMER_TO_CONTROLLED_BOUNDARY_MOMENTS

HOLD:
  PRIME_POWER_RECURRENCE_EXACT_BUT_ADJOINT_PREIMAGE_OR_BOUNDARY_RATE_UNCONTROLLED

FAIL:
  ANNIHILATOR_COEFFICIENT_GROWTH_OR_CONSUMER_RANGE_DEFECT_REIMPORTS_PRIME_WALL
```

## META CLOSEOUT

**What became smaller?**

The vague coincidence `m/log m looks like the prime count` became an exact
finite-exponential representation with recurrence degree at most
`2*J_pp(m)` and oversampling of order `log m`.

**What was killed?**

```text
m/log m = pi(m) exactly;
source support = primes only;
prime count alone controls the weighted signed consumer;
line intersections may be used without object lock;
prime-indexed schedule may replace the precommitted schedule post hoc.
```

**What must not be tried again?**

Do not use a counting asymptotic as a bound on the exact source action.  Do not
invoke a prime-count explicit formula containing zeta zeros inside a proof of
RH.

**Current smallest named gap**

```text
PRIME_POWER_ANNIHILATOR_ADJOINT_RANGE_WITH_CONTROLLED_BOUNDARY
```

**Next cheapest decisive test**

Derive the exact recurrence, then test membership of the literal mixed
consumer weight in its adjoint range.  No computation is needed before this
paper identity is settled.

**Prediction memory**

```yaml
iteration:
  target: SELECTED_FERRERS_POLARIZED_ORDERED_COMPLETED_BETA_SOURCE_ACTION_COMPACT_DECAY
  status: OPEN
  failed_strategy: count_only_prime_cancellation
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: PRIME_POWER_ANNIHILATOR_ADJOINT_RANGE_WITH_CONTROLLED_BOUNDARY
  invariant_learned: preserve_vonMangoldt_prime_powers_phases_and_full_source_signs
  forbidden_future_move: infer_consumer_smallness_from_pi_m_alone
  next_decisive_test: exact_adjoint_range_decomposition
```
