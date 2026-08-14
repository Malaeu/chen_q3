# Goal 058 G3 — mode-four derivative-interface repair

Date: 2026-08-14

Status: PROVED — ACCEPT

## Pin and boundary

- Repository: `/Users/emalam/GitHub/rh_lean_01_2026`
- Branch: `rh_clean`
- Execution base: `252dbdee754e08cd68f900523fb3103750c099ee`
- Base equals `origin/rh_clean`: yes
- Strict startup: `P9_STRICT_PASS`
- Route B status: `CHECK: OK`
- Owned Lean file only:
  `Q3/Proofs/RouteB/D0Mode4FerrersRegularEvenProlateSolution.lean`

This transaction repairs a semantic interface.  It does not prove interior
zero simplicity and does not close G3 or G1.

## Blocker found before implementation

`Mode4FerrersRegularEvenProlateSolution` stored `contDiffOn_two_open` and an
ODE written with the formal functions
`mode4FerrersFirstDerivativeSeries` and
`mode4FerrersSecondDerivativeSeries`.  It did not store identities connecting
those functions to the actual first and second derivatives.  Ordinary
absolute coefficient summability cannot supply those identities by itself.

The existing constructor can derive the missing identities, but only while it
still has the source guards `hm`, `hK`, `hsep`, `hΛ` and the exact tail splice.
After construction those guards were intentionally no longer available.

## Architecture review

Mythos selected `A_STRENGTHEN_STRUCTURE_WEIGHTED_SUMMABILITY` as the primary
route, with the architectural requirement that the clean downstream theorem
head remain `(S, hx, hz)`.  Its decisive observation was that the constructor
boundary was discarding information required by every later ODE consumer.

Proshka then performed a natural 12m27s repair audit and refined the public
contract:

- `PRIMARY: REPAIR_A_STRENGTHEN_DERIVATIVE_INTERFACE`
- Option A selected.
- Option B rejected as a local minimum with global API debt.
- Option C rejected because no field-only supplier exists on disk.
- Store the two semantic `HasDerivAt` facts, not raw weighted summability.
- Do not implement `interior_zero_simple` in this transaction.

This refinement is implemented literally.  Weighted summability remains
private constructor scaffolding.

## Exact repair

The public structure now stores:

```lean
ferrersSeries_hasDerivAt_firstDerivativeSeries :
  ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
    HasDerivAt
      (mode4FerrersSeries coefficients)
      (mode4FerrersFirstDerivativeSeries coefficients x)
      x

firstDerivativeSeries_hasDerivAt_secondDerivativeSeries :
  ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
    HasDerivAt
      (mode4FerrersFirstDerivativeSeries coefficients)
      (mode4FerrersSecondDerivativeSeries coefficients x)
      x
```

The existing constructor obtains the private weight-two bound from
`mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice` and uses
the existing public suppliers:

- `mode4FerrersSeries_hasDerivAt_of_mem_Ioo`
- `mode4FerrersFirstDerivativeSeries_hasDerivAt_of_mem_Ioo`

For each `x ∈ (-1,1)` it chooses the strict local window
`r = (|x| + 1) / 2`, so `0 < r < 1` and `x ∈ (-r,r)`.  No hypothesis or
conclusion of the constructor changed, and no new direct import was added.

## Falsifier gates

1. `coefficients_abs_summable` alone is not used as a derivative budget.
2. Raw weighted summability is not exposed as a public structure field.
3. The constructor guards are not leaked into the downstream public API.
4. The formal derivative series are not identified with actual derivatives by
   `contDiffOn_two_open`; the two identities are separately kernel checked.

## Validation

- Direct Lean elaboration: PASS.
- Owned Lean SHA256:
  `4e0e09e10dc539af64daf772c16d70173da8e14b4bccb315a498e851fa356937`.
- Axiom print for the public constructor:
  `[propext, Classical.choice, Quot.sound]`.
- Target build: PASS, 7770 jobs.
- Full build: PASS, 7817 jobs.
- `scripts/q3_check.sh`: PASS (`q3_check ok`).
- `sorry` / `axiom` / `admit` scan of the owned Lean file: clean.
- `git diff --check`: PASS.

## Nonclaims

- `NO_INTERIOR_ZERO_SIMPLICITY_YET`
- `NO_ZERO_COUNT`
- `NO_ORDERED_PSI4_IDENTIFICATION`
- `NO_ROOT_EXISTENCE`
- `NO_PHYSICAL_SCALE`
- `NO_MODE_ZERO`
- `NO_FINITE_FOURIER_EIGENRELATION`
- `NO_ACTUAL_PROLATEPAIR`
- `NO_LEMMA_7_2`
- `NO_G3`
- `NO_G1`
- `NO_ROUTE_B_PROMOTION`
- `NO_RH`

Next named leaf after judge acceptance:
`G3_MODE4_FERRERS_INTERIOR_ZERO_SIMPLICITY`, with the clean theorem head
`(S, hx, hz)`.

## Proshka code verdict

Natural review time: 3m36s.

- `PRIMARY: ACCEPT`
- `two_semantic_HasDerivAt_fields: ACCEPTED`
- `weighted_summability_private: ACCEPTED`
- constructor hypotheses and conclusion unchanged: confirmed
- direct imports unchanged: confirmed
- downstream API breakage: false
- hidden derivative assumption: false
- isolated two-file commit: authorized
- push to `origin/rh_clean`: authorized

The authorized next single source leaf is
`G3_MODE4_FERRERS_INTERIOR_ZERO_SIMPLICITY`.
