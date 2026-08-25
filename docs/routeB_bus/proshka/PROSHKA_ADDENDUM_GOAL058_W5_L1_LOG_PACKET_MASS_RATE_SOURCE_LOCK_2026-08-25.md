# STATUS: CONDITIONAL — W5_L1_SOURCE_LOCK_ADDENDUM_AND_EXISTING_INVERSION_BIND
```yaml
PRIMARY: BIND_W5_L1_RACED_NOTE_AND_REJECT_NEW_POISSON_SUPPLIER
DOCUMENT_ROLE: APPEND_ONLY_SOURCE_LOCK_CORRECTION

ORIGINAL_VERDICT:
  COMMIT: bc5cc52428135aefdd56065cf195c6edc6ef4b23
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_L1_LOG_PACKET_MASS_RATE_2026-08-25.md
  GIT_BLOB: dfdcdf6193fdfaa8d6cf6d2ee3f9183925033c73
  DECLARED_REVIEW_BASE: 3a6ba17fac54a443a8674d35816bafd73d8904aa

RACE:
  ACTUAL_VERDICT_PARENT: 7b4443a4e0a27edb69da8fa9a8a175cc294a8c59
  RACED_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  RACED_CLAIM: left_half_requires_new_poisson_summation_supplier
  SOURCE_LOCK_STATUS: NOW_AUDITED

ADJUDICATION:
  SIGNED_ESTAR_LOCALIZATION_PROBE: ACCEPT_AS_DIAGNOSTIC_ONLY
  RIGHT_HALF_GAUSSIAN_ROUTE: VALID_BUT_NOT_LOAD_BEARING_ALONE
  LEFT_HALF_NEW_POISSON_WALL: REJECTED
  EXISTING_PUBLIC_SUPPLIER: Q3.RouteB.D0Pstar.E_star_explicitCCMLimitH_inv
  EXISTING_SUPPLIER_STATEMENT: E_star_H(u_inverse)_eq_E_star_H(u)_for_u_pos
  CONSEQUENCE: right_half_decay_transports_exactly_to_left_half
  ORIGINAL_TRY_VERDICT_CHANGED: false

SCOPE: COFINAL_FAMILY
VERIFIER: LEAN_PLUS_SOURCE_AUDIT
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

LEAN_EDIT: false
CODEX_AUTHORIZATION: unchanged_from_original_verdict
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## SOURCE-LOCK CORRECTION

The original verdict was authored after auditing `3a6ba17f`, but the branch advanced to `7b4443a4` before the verdict commit landed. The latter note is now explicitly included in the audit. `[COFINAL_FAMILY][PAPER]`

The numerical picture in `7b4443a4` is consistent with the selected representation: the signed target comb is localized near multiplicative scale one, whereas the sum of term norms is a wrong surrogate. The displayed decimals remain calibration only. `[FINITE_CELL][CONDITIONAL]`

## KILL OF THE NEW LEFT-HALF WALL

The note says that `u <= 1` requires a new Poisson-summation theorem not present in the tree. That diagnosis is false for the exact target used here. The repository already exports

```lean
E_star_explicitCCMLimitH_inv (u : ℝ) (hu : 0 < u) :
  E_star explicitCCMLimitH u⁻¹ = E_star explicitCCMLimitH u
```

from `D0PstarExplicitCCMLimitFourier.lean`. `[ABSTRACT][LEAN]`

Therefore an upper bound for `u >= 1` transfers exactly to `0 < u <= 1` by replacing `u` with `u⁻¹`. No new summation formula, zero-mass supplier, or paper import is required for the L1 node. `[COFINAL_FAMILY][LEAN]`

The original directive remains authoritative:

```text
right-side inverse-four / Gaussian decay
+ exact public inversion
+ public full-error split and rates
+ exact log-window measure transport
→ L1_k <= B + A / sqrt(lambda_k).
```

## META CLOSEOUT

- **Smaller gap:** the alleged left-half Poisson wall is removed.
- **Killed:** `W5_SIGNED_ESTAR_NEW_POISSON_SUPPLIER_GAP`.
- **Do not retry:** reconstructing a second Poisson theorem when exact inversion already supplies the left half.
- **Current smallest gap:** `W5_L1_LOG_WINDOW_MEASURE_TRANSPORT_GAP`.
- **Prediction fate:** the original L1 predictions are unchanged; no retroactive repair.
