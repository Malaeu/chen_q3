# Proshka verdict — Goal 058 G3 mode-four Hermitian negative-count stability repair

Date: `2026-08-14`

Capture: normalized from the completed response in the standing Proshka chat.
Natural reasoning time shown by the UI: `7m 14s`.

## Primary verdict

```yaml
PRIMARY: REPAIR_EXACT_PUBLIC_HEAD_AND_COMPLETE_PLANT_SUITE
PRIMARY_COUNT: 1
SOURCE_AUDIT:
  LEAN_SHA256_VERIFIED: 0405c186fb204c126fff698efe1f214b54d07b60a95eeaf9f34928d4bf9c7aef
  CLOSEOUT_SHA256_VERIFIED: cc7fee41ffd0cb524c4cd86710cf030a7b6138016988ada9d7e4388348977671
  CORE_PROOF_ARCHITECTURE: ACCEPTED
  TRANSACTION_ACCEPTED: false
REPAIR_REASONS:
  - EXTRA_PUBLIC_BINDER_hK_WEAKENS_AUTHORIZED_HEAD
  - PUBLIC_SURFACE_HAS_TWO_THEOREMS_INSTEAD_OF_ONE
  - ONLY_SINGULAR_LIMIT_PLANT_IS_MATERIALIZED
  - PLANTS_P2_P3_P4_P5_ARE_NOT_EVIDENCED_BY_THE_TWO_AUTHORITATIVE_FILES
COMMIT_AUTHORIZED: false
PUSH_AUTHORIZED: false
NEXT_LEAF_AUTHORIZED: false
G1: OPEN
G3: OPEN
ROUTE_STATE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
RH_CLAIM: false
SCOPE: ABSTRACT
VERIFIER: LEAN
STOP: G3_HERMITIAN_NEGATIVE_COUNT_STABILITY_PUBLIC_CONTRACT_REPAIR_REQUIRED
SUCCESS: G3_HERMITIAN_NEGATIVE_COUNT_EVENTUAL_STABILITY_PROVED_EXACT_CONTRACT
```

## Authorized repair only

Owned paths:

- `Q3/Proofs/RouteB/D0Mode4HermitianNegativeCountStability.lean`
- `ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_G3_MODE4_HERMITIAN_NEGATIVE_COUNT_STABILITY_CLOSEOUT_2026-08-14.md`

The public theorem must have no `hK : 1 <= K` binder.  A private
positive-dimension helper may retain it, while the single public theorem must
split on `K = 0` and discharge the empty carrier directly.

The production module must expose exactly one public theorem and zero public
definitions.  The singular-limit plant must therefore be private (or live in
a temporary plant harness).

The required plant suite is:

1. singular nonsingular-limit guard: `[-1/(d+1)] -> [0]`, count `1 -> 0`;
2. determinant convergence is not matrix convergence: alternate
   `diag(-1,-1)` and `diag(1,1)`, determinant always `1`, counts `2/0`;
3. determinant sign is not the count: `diag(-1,-1,1)` and
   `diag(1,1,1)` both have positive determinant, counts `2/0`;
4. Hermitian guard: a real nonsymmetric rotation matrix must be rejected;
5. fixed-carrier guard: `Matrix (Fin (d+1)) (Fin (d+1))` cannot be passed
   directly to the fixed-`K` production theorem.

Required plant stop codes:

```text
G3_INERTIA_STABILITY_SINGULAR_LIMIT_GUARD_DROPPED
G3_INERTIA_STABILITY_MATRIX_TENDSTO_REPLACED_BY_DET
G3_INERTIA_STABILITY_DET_SIGN_NOT_COUNT
G3_INERTIA_STABILITY_HERMITIAN_GUARD_DROPPED
G3_INERTIA_STABILITY_FIXED_CARRIER_DROPPED
```

After repair the closeout must truthfully record:

```yaml
EXACT_AUTHORIZED_HEAD: PASS
PUBLIC_THEOREMS: 1
PUBLIC_DEFINITIONS: 0
PLANTS: 5_OF_5_PASS
SINGULAR_LIMIT_GUARD: LOAD_BEARING
MATRIX_TENDSTO_NOT_DET_TENDSTO: PASS
DET_SIGN_NOT_EXACT_COUNT: PASS
HERMITIAN_GUARD: PASS
FIXED_CARRIER_GUARD: PASS
```

Validation required: direct Lean, target build, full build, `q3_check.sh`,
forbidden-token scan, exact public-surface audit, single public theorem axiom
print, and `git diff --check`.

Stop after validation.  No commit, push, next crosswalk leaf, endpoint count,
G1/G3 closure, Route B promotion, or RH claim is authorized.
