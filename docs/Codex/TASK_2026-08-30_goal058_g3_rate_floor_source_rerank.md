# Codex task — Goal 058 G3 rate/floor source rerank

Date: 2026-08-30
Status: `ACTIVE_STRATEGIC_SOURCE_REVIEW`
Parent: Goal 058 / G3 prolate rate and projected denominator floor

## Exact conflict

The live Route B execution state still names
`G3_PROLATE_RATE_CENTRAL_OVERLAP_DENOMINATOR_FLOOR` and asks Codex to build the
normalized two-mode prolate packet, the CCM Lemma 7.2 rate, the central overlap,
and the denominator floor.

Later kernel-green modules already close the receiver side conditionally:

- `selectedFerrers_directCylinderRate_of_explicitSatz9RawRates` transports an
  explicit raw Satz 9 rate;
- `selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates`
  transports explicit finite-Fourier eigenvalue-defect rates;
- `selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger` closes the
  projected norm floor and bounded normalizer from those rate inputs.

Therefore another receiver or denominator-floor wrapper would be redundant.
The remaining load-bearing question is whether the exact paper-rate inputs may
be formalized, admitted through an approved source interface, or require the
current G3 front to be killed and reranked.

## Required action

1. Keep the existing conditional Lean theorems and their honesty guards.
2. Do not introduce a project axiom or relabel a citation as a Lean proof.
3. Obtain one independent strategic verdict through
   `REQ-2026-08-30-G3RATEFLOOR`.
4. Execute only the theorem-sized first action selected by that verdict.
5. Reconcile `ROUTE_B_EXECUTION_STATE.json`, route documentation, mapper and
   current task only after the verdict is byte-bound and operative.

## Boundaries

- Preserve the six-field phase key and the same living Proshka chat.
- Do not edit or stage foreign mode-four files or foreign control/map deltas.
- No finite-cell promotion, Route promotion, or RH claim.
- `PX_RH_CLAIM: NOT_MADE`.
