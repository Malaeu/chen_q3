# STATUS: CONDITIONAL — DIRECT SIGNED ROUTE REDUCED; CLOSE W5 CONDITIONALLY ON THE DERIVATIVE BUDGET

```yaml
PRIMARY: W5_DERIVATIVE_CONDITIONAL_CLOSURE_AFTER_D2
PRIMARY_COUNT: 1

SOURCE_LOCK:
  D2_COMMIT: 584b45d2091befc449451cc3e8964d84da50fa3b
  WALL_COMMIT: 2ce801a35f063be04676bc160f553502f2e35b25
  CONSUMER_DISCRIMINATOR: BOUNDED_CK_SUFFICES

DECISION:
  OPTION_A_MINIMAL_C1_AS_SOURCE_IMPORT: REJECT_UNVERIFIED
  OPTION_B_HIDDEN_SIGNED_MECHANISM: NOT_FOUND
  OPTION_C_CONDITIONAL_CLOSE: SELECTED

EXACT_OPEN_SUPPLIER:
  name: W5_LOG_DERIVATIVE_BUDGET_BOUNDED
  statement: >-
    exists D >= 0 such that eventually
    selectedFerrersAbelLogDerivativeBudget k <= D.
  scope: COFINAL_FAMILY
  verifier: CONDITIONAL

D1_D2:
  exact_signed_decomposition: PROVED_LEAN
  formula: >-
    d/dx rep = (1/2) rep + sqrt(u) * sum_active Q_k(n*u),
    Q_k(y)=y*pkt_k'(y).
  c1_input_used: false

IMMEDIATE_LEAN_REDUCTION:
  target: W5_DERIVATIVE_BUDGET_REDUCTION
  formula: >-
    DerivativeBudget_k <= (1/2)*L1_k
      + integral_0^L sqrt(u(x))*norm(sum_active Q_k(n*u(x))) dx.
  authorized: true

SOURCE_AUDIT:
  MEIXNER_SCHAEFKE_SATZ9:
    supplies: uniform_C0_fixed_mode_rate
    derivative_remainder_source_locked: false
  CCM_LEMMA_7_2:
    supplies: uniform_C0_mode_rate
    derivative_remainder_source_locked: false
  consequence: >-
    do not label a C1 estimate as a paper theorem or F72.6 consequence
    without a new proof/source.

MINIMAL_C1_CANDIDATE:
  status: UNPROVED_CANDIDATE_NOT_ACTIVE_SUPPLIER
  shape: >-
    exists C' >= 0, eventually for all y in the source window,
    norm(deriv(pkt_k) y - 4*deriv(explicitCCMLimitH) y)
      <= C' / sqrt(lambda_k).
  note: >-
    The lambda^(-1/2) exponent is accepted only as a candidate sufficient
    strength from the Linux reduction; it is not source-ratified until the
    exact comb arithmetic is kernel-checked.

CONSUMER:
  exact_requirement: EVENTUAL_BOUNDEDNESS_ONLY
  reason: SelectedPhysicalFourierEnergyControl uses IsBoundedUnder atTop
  caveat: discrete_continuum_energy_bridge_may_still_be_needed

PREDICTIONS:
  P_W5_CONSUMER_1: CONFIRMED
  P_W5_DERIVATIVE_1:
    fate: REFUTED_AS_COMPLETE_ROUTE
    surviving_part: D1_D2_exact_signed_reduction
    failure: norm_inside_integral_blocks_signed_IBP

CLOSES:
  - W5_DERIVATIVE_ROUTE_SELECTION
  - W5_FALSE_DIRECT_SIGNED_IBP_CLOSURE
OPENS:
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED

NEXT_LOAD_BEARING_GAP: W5_LOG_DERIVATIVE_BUDGET_BOUNDED

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

D2 is kernel-green and proves the exact signed derivative decomposition without a C1 input. The subsequent wall analysis is correct: the W5 derivative budget integrates the norm of the derivative, so integration by parts or cancellation of the signed integral does not control the integral of the norm. The direct signed route therefore does not close the budget.

The current Meixner–Schäfke usage card source-locks Satz 9 only as a uniform C0 approximation theorem on [-1,1]; it does not source-lock a derivative remainder. CCM Lemma 7.2 likewise supplies the C0 rate used by F72.6. Therefore a C1 estimate must not be imported as if already present in the paper corpus.

The consumer discriminator has already shown that eventual boundedness of C_k is sufficient. Since L1 is eventually bounded and the jump ledger tends to zero, the exact remaining analytic supplier should be named at consumer strength:

```text
W5_LOG_DERIVATIVE_BUDGET_BOUNDED:
  exists D >= 0, eventually DerivativeBudget_k <= D.
```

This avoids prematurely upgrading the route to a stronger pointwise C1 theorem.

## FINAL PROPOSAL

Proceed with the unconditional Lean reduction already in progress:

```text
DerivativeBudget_k
  <= (1/2) * L1_k
     + integral sqrt(u) * norm(Q-comb_k(u)).
```

After that reduction compiles, close the W5 cofinal budget assembly conditionally on `W5_LOG_DERIVATIVE_BUDGET_BOUNDED`. Do not add a public C1-F72.6 premise to the W5 theorem.

If a future supplier is sought, the first candidate may be the pointwise derivative-error estimate

```text
norm(pkt'_k(y) - 4 H'(y)) <= C' / sqrt(lambda_k)
```

uniformly on the source window, but this is currently a candidate sufficient theorem, not a verified source import. Its exact exponent should be admitted only after the comb-to-budget arithmetic is formalized.

## STRONGEST ATTACK

The strongest objection is that the proposed C1 estimate may be stronger than needed and is not stated by the cited source. This objection is valid. The repair is exactly the conditional closure above: expose the derivative budget itself as the missing supplier and allow any later mechanism — C1, ODE interpolation, variation, or another source-faithful estimate — to discharge it.

## CODEX DIRECTIVE

```text
NEXT LOCAL TARGET:
  prove the unconditional derivative-budget reduction only.

INPUT:
  existing D2 exact signed derivative decomposition.

OUTPUT:
  DerivativeBudget_k <= (1/2)*L1_k + weighted integral of norm(Q-comb).

FORBIDDEN:
  no C1 premise;
  no signed-IBP claim for integral of norm;
  no theorem weakening;
  no route promotion.

SUCCESS:
  kernel-green reduction with standard axiom triple.

FAILURE_CODE:
  W5_DERIVATIVE_BUDGET_REDUCTION_LEAN_GAP
```

## META CLOSEOUT

- Smaller: the derivative problem is now one exact supplier, not an undefined C1 wall.
- Killed: direct signed IBP as a closure mechanism.
- Do not retry: treating a signed integral identity as a total-variation bound.
- Current smallest named gap: `W5_LOG_DERIVATIVE_BUDGET_BOUNDED`.
- Next cheapest decisive test: kernel-check the unconditional budget reduction, then audit candidate suppliers against that exact consumer-strength target.
