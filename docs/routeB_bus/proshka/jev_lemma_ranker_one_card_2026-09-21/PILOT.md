# Jev one-card pilot — NOT RUN (TypeSafe down)

```yaml
STATUS: WAITING_SERVICE
API_CALL: false
MODEL_PIN: jev-1.13.0
SCOPE: ONE_CHOICE_ON_FROZEN_LIST
JUDGE: false
ROUTE_PROMOTION: false
RH_CLAIM: false
```

When TypeSafe is up: one Choice, this state, these 10 options. Compare to the
`ask.sh` order below. Jev may only permute attempts. It does not accept a
proof, kill a branch, or change the target.

## State (send only this card, not the repo)

Paper identity G4–G7: Mellin of the compact Ferrers packet equals the
normalized Fourier row of the same `prolateCombination`, no quadrature.
Need to swap the Ferrers series with the source-window integral, then match
existing `c_n`.

## Choice question

Which declaration should be checked first for that swap-and-match?

## Frozen options (do not add names at call time)

| id | declaration | file |
|---|---|---|
| A | `mode4FerrersSeries_hasSumUniformlyOn` | `D0Mode4FerrersCoefficientAbsoluteSummability.lean:216` |
| B | `mode4FerrersSeries` (def + Summable \|a\|) | same file |
| C | `windowedMellin_finiteEStarCore_eq_dirichlet_sum` | `EStarWindowedMellinCrosswalk.lean:256` |
| D | `windowedMellin_finiteEStarCore_eq_sum` | same file, just above |
| E | `prolateCombination_windowFiniteSupport` | `D0PstarActualProlateEStarMemLp.lean:50` |
| F | `sourcePositiveIndexFinset` | same file:34 |
| G | `c_n` | `D0KTrialStage3.lean:81` |
| H | `kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow` | `D0PstarProjectedMellinCoordinate.lean:44` |
| I | `TrialNonzero` on `prolateCombination` | `D0ProlateKTrialSource.lean:52` |
| J | `integral_prolateCombination_eq_zero` | `ProlateCombinationMuntzRegularity.lean` |

## Baseline without Jev (`ask.sh` 2026-09-21, Lean hits; q3_docs stale)

Order I would try:

1. A — uniform sum, justifies interchange on `[-1,1]`
2. B — the series object
3. C then D — Mellin of finite `E_star` already swapped
4. E then F — compact support, finite k-sum
5. G then H — existing coefficient row
6. I — needed only for the normalized `c_n`
7. J — packet mass zero (`d_0=0`), not the swap itself

Missing from the shelf: Lean G4 (closed Mellin of `t^d`). That is the first
thing to write, not a 11th Choice option.

## Gate

Owner key + explicit OK to send this card. Pin `jev-1.13.0`. Log request,
response, version. On failure or downtime: keep the baseline order.
