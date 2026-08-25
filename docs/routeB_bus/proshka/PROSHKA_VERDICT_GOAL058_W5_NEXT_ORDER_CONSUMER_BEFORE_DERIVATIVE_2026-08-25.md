# STATUS: CONDITIONAL — TAKE THE CONSUMER RATE LOCK BEFORE THE DERIVATIVE C1 SUPPLIER
```yaml
PRIMARY: W5_CONSUMER_RATE_LOCK_BEFORE_DERIVATIVE_C1
PRIMARY_COUNT: 1

CONFIRMED_GREEN_NODES:
  W5_L1_LOG_PACKET_MASS_RATE:
    source_commit: 96bba130f2efb37bd28dbd17eb89b0ff5739efee
    gate_commit: 52e81399d789da172c6ecfbe473f1e5cae3fc7d9
    theorem: selectedFerrersAbelLogZeroExtension_l1_rate_of_modeAndChiRates
    result: eventually_L1_le_B_plus_A_div_sqrt_lambda
    status: PROVED_CONDITIONAL_ON_F72_6
  W5_FULL_ENDPOINT_VALUE_RATE:
    source_commit: b4e20a83694920f216a21a737894a8c91b105dc0
    gate_commit: e2c6abc2ea130ac7220fe58a2b90a74fe46ba94c
    theorem: selectedFerrersAbelLogEndpointValues_rate_of_modeAndChiRates
    result: both_endpoints_le_96_plus_C1_plus_C2_div_sqrt_lambda
    status: PROVED_CONDITIONAL_ON_F72_6
  W5_REPAIRED_INTERNAL_SEAM_SUM_COFINAL_DECAY:
    commit: ac43234e9638ea9f748d89c2457323ab4f69cfeb
    status: PROVED_CONDITIONAL_ON_F72_6

JUMP_LEDGER:
  status: TENDS_TO_ZERO_CONDITIONALLY
  components:
    endpoint0: CLOSED
    endpointL: CLOSED
    seam: CLOSED

EXACT_W5_BUDGET:
  formula: C_k = 2 * (L1_k + (Derivative_k + Jump_k) / (2*pi))
  L1_status: BOUNDED_EVENTUALLY
  Jump_status: TENDS_TO_ZERO
  Derivative_status: OPEN

OPEN_QUESTIONS:
  - W5_LOG_DERIVATIVE_BUDGET_RATE
  - W5_COFINAL_BUDGET_CONSUMER_RATE_LOCK

ORDER_DECISION:
  first: W5_COFINAL_BUDGET_CONSUMER_RATE_LOCK
  second: W5_LOG_DERIVATIVE_BUDGET_RATE
  reason: >-
    The consumer theorem determines the weakest derivative rate that is actually
    needed. Proving a new C1 version of F72.6 before locking the consumer risks
    proving a stronger theorem than the route consumes.

DERIVATIVE_OBJECT:
  exact_decomposition: >-
    d/dx rep = (1/2) E_star(pkt) + E_star(Q) + shadow,
    with Q(y) = y * pkt'(y).
  zero_mass_Q: AVAILABLE_BY_INTEGRATION_BY_PARTS
  current_missing_input: uniform_C1_mode_rate_for_pkt_prime_minus_4H_prime
  new_owner_input_status: NOT_YET_JUSTIFIED

CONSUMER_DISCRIMINATOR:
  task: >-
    Read the exact first downstream consumer of
    selectedFerrersAbelLimit_shiftedEnergy_le_majorant and determine the weakest
    asymptotic condition it requires on C_k (or C_k^2).
  possible_outputs:
    - BOUNDED_CK_SUFFICES
    - CK_MAY_GROW_WITH_EXPLICIT_RATE
    - CK_MUST_DECAY
    - CONSUMER_NOT_YET_SOURCE_LOCKED
  forbidden: choose_sup_Ck_finite_by_preference

PREDICTION_REGISTER:
  P_W5_CONSUMER_1:
    probability: 0.72
    prediction: >-
      The exact downstream consumer needs no more than eventual boundedness of C_k,
      so the derivative target can be weakened to an eventual uniform bound rather
      than a full O(lambda^-1/2) decay theorem.
    fate: UNTESTED
  P_W5_DERIVATIVE_1:
    probability: 0.68
    prediction: >-
      If eventual boundedness is sufficient, a direct signed-E_star bound for Q
      will be cheaper than proving a full source C1 analogue of F72.6.
    fate: UNTESTED

PRIOR_PREDICTIONS:
  P_W5_L1_SIGNED_CANCELLATION: CONFIRMED
  P_W5_L1_3_DSTAR_FIRST_FAILURE: REFUTED

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

The source and gate receipts confirm that three of the four analytic components
of the W5 Fourier budget are now controlled: `L1_k` is eventually bounded,
`Endpoint0_k` and `EndpointL_k` decay like `lambda_k^(-1/2)`, and the repaired
internal seam decays. Therefore the complete jump ledger tends to zero. The only
uncontrolled analytic component is `Derivative_k`.

The exact budget is

\[
C_k=2\left(L1_k+\frac{Derivative_k+Jump_k}{2\pi}\right).
\]

However, the existing W5 theorem only says that the shifted-energy majorant is
proportional to `C_k^2`. It does not source-lock what the next consumer requires
of that quantity. The earlier cofinal-rate verdict explicitly left
`EXACT_ACCEPTABLE_COFINAL_GROWTH` open. Therefore the consumer must be read
before minting a stronger derivative supplier.

## FINAL PROPOSAL

Take `W5_COFINAL_BUDGET_CONSUMER_RATE_LOCK` first as a read-only theorem-shape
audit.

The audit must identify the first actual downstream theorem that consumes the
W5 shifted-energy bound and derive the weakest sufficient asymptotic condition
on `C_k` or `C_k^2`. No guessed requirement such as `sup_k C_k < infinity` is
allowed.

Only after that result should `W5_LOG_DERIVATIVE_BUDGET_RATE` be specified. If
bounded `C_k` is sufficient, the derivative target should be only eventual
boundedness. If the consumer tolerates growth, weaken it further. Only if the
consumer forces a vanishing rate should a full C1-F72.6 supplier be opened.

## STRONGEST ATTACK

The strongest objection is: the derivative decomposition already exposes a C1
mode error, so why not prove it now?

Because the C1 theorem is a new cofinal analytic input. The current source tree
only supplies C0 F72.6 control. Opening C1 before reading the consumer may add a
large theorem whose extra strength is unused. K2 and W9 both forbid that move.

A failure of a strong C1 sufficient condition would also not kill the derivative
budget: a signed-E_star estimate for `Q(y)=y pkt'(y)` might prove exactly the
weaker consumer-required statement without uniform pointwise C1 convergence.

## CODEX DIRECTIVE

```text
TASK: W5_COFINAL_BUDGET_CONSUMER_RATE_LOCK
MODE: READ_ONLY

Find the first exact downstream consumer of:
  selectedFerrersAbelLimit_shiftedEnergy_le_majorant
or of:
  selectedFerrersShiftedEnergyMajorant

Return:
1. exact theorem/file;
2. exact occurrence of the W5 shifted-energy quantity;
3. every multiplicative/additive cofinal factor surrounding it;
4. the weakest sufficient asymptotic condition on C_k or C_k^2;
5. whether eventual boundedness suffices;
6. whether any decay rate is actually required;
7. exact smallest derivative target implied by that condition.

Do not edit Lean.
Do not invent a consumer.
Do not assume sup_k C_k < infinity.
Do not open a C1-F72.6 theorem unless the consumer audit proves it is required.

SUCCESS:
  EXACT_ACCEPTABLE_COFINAL_GROWTH_SOURCE_LOCKED

FAILURE:
  W5_CONSUMER_NOT_SOURCE_LOCKED
```

## META CLOSEOUT

- What became smaller? The W5 analytic budget now has one open analytic component: `Derivative_k`.
- What was killed? The need to investigate endpoint values or seam further; the whole jump ledger tends to zero.
- What must not be tried again? Do not choose a derivative rate before reading the consumer.
- Current smallest named gap? `W5_COFINAL_BUDGET_CONSUMER_RATE_LOCK`.
- Next cheapest decisive test? Read the exact downstream consumer and extract the minimal rate requirement.
- Fate of prior predictions? Signed L1 mechanism confirmed; dStar-first-failure prediction refuted.
- Memory entry: consumer-first rate specification before C1 supplier construction.
