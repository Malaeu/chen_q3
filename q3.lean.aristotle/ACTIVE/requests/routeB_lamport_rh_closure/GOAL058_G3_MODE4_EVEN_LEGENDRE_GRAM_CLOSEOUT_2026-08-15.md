# Goal 058 G3 — exact even ordinary-Legendre Gram closeout

Date: 2026-08-15
Branch: `rh_clean`
Pinned HEAD at entry: `d55a82458656`
Route state: `CHALLENGER_NOT_RH`

## External ruling lock

- Proshka request packet:
  `.playwright-mcp/GOAL058_G3_POST_SCALE_FINITE_LEGENDRE_FORM_PROSHKA_REQUEST_2026-08-15.txt`
- request SHA-256:
  `e124bc96cdc7cb12bc4bd5438cebae21e3424115cf894a1848ddbb42699ab8c8`
- first captured verdict JSON SHA-256:
  `c2510d23851767ec3b76b6d70b27b4f49ecacf76943e5c6a584f79a68ea7e684`
- first decoded text SHA-256:
  `d264f66327ae0bb68123232718bcc17fb0e5dd283854630841d9e4150d46efb1`
- continuation JSON SHA-256:
  `2f62bfba211481884583aad0d03dd1fb5d91bee9ccbb3487e8734352d0f138e1`
- continuation decoded text SHA-256:
  `463a4720b1b55d7b4ead6ac23e16b9ff02cedaba53ff8a6c3ad369caaecf0ca4`
- exact primary: `A_GRAM_LEAF`
- Aristotle authorization: `G3_MODE4_EVEN_LEGENDRE_GRAM` only
- commit authorization: false
- push authorization: false

The first web response was physically truncated after the L2 factor check.
A same-chat continuation supplied the missing derivative/form signs, theorem
heads, circularity audit, Aristotle boundary, and nonclaims.  The pre-existing
composer draft `wer ist da` was restored byte-for-byte and was not sent.

## Production artifact

- file:
  `Q3/Proofs/RouteB/D0Mode4OrdinaryLegendreGram.lean`
- SHA-256:
  `16bca750455c9b24904fae127249d6b312ee88f6868439d44eb7c5e1fbe5b02b`
- bytes / lines / final LF: `13001 / 328 / yes`
- direct imports:
  - `Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreXSquaredAction`
  - `Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreIntervalBound`
  - `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`

The explicit `IntervalBound` import is a disk-evidence repair to the Proshka
import sketch: the current tree exports the Legendre ODE from that module, not
transitively from `XSquaredAction`.

Public heads proved exactly:

```lean
theorem mode4OrdinaryLegendre_even_gram
    (q r : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      mode4OrdinaryLegendre (2 * q) x *
        mode4OrdinaryLegendre (2 * r) x) =
      if q = r then 2 / (((4 * q + 1 : ℕ) : ℝ)) else 0

theorem mode4OrdinaryLegendre_even_derivative_gram
    (q r : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) *
        (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x *
        (mode4OrdinaryLegendrePolynomial (2 * r)).derivative.eval x) =
      if q = r then
        (((2 * q : ℕ) : ℝ) * (((2 * q + 1 : ℕ) : ℝ))) *
          (2 / (((4 * q + 1 : ℕ) : ℝ)))
      else 0
```

Proof architecture:

1. Wronskian flux from the two exact polynomial ODEs proves all off-diagonal
   Gram entries zero; the endpoint value vanishes literally through
   `1 - x^2`.
2. The exact `X` action, including the `n = 0` branch, gives the norm
   recurrence and base value, hence `2/(2n+1)`.
3. A second flux integration-by-parts identity multiplies the Gram entry by
   `n(n+1)`, yielding the weighted derivative Gram theorem.

No selected PSWF, root, zero count, minimizer, positivity premise, Ferrers
solution field, numerical quadrature, or later finite-form theorem is used.

## Kernel and plant validation

- direct `lake env lean`: PASS
- named target build: PASS, `2628 jobs`
- full `lake build`: PASS, `7817 jobs`
- `q3_check`: PASS
- `git diff --check`: PASS
- forbidden scan (`sorry`, `admit`, `exact?`, custom `axiom`, `unsafe`,
  `native_decide`): no hits
- public axioms: exactly `[propext, Classical.choice, Quot.sound]`

Scratch plant file:

- `/tmp/Goal058EvenGramPlants.lean`
- SHA-256:
  `d1f07f1159dd0a4e6c07a988dee4722b7279aefdbcf46043a5b3b942695673fd`
- direct Lean: PASS
- controls: `(q,r)=(0,0)`, `(0,1)`, `(1,1)` all PASS
- mutant replacing `1-x^2` by `1+x^2` at degree two: REJECTED
- every plant axioms: exactly the standard triple

## Aristotle transport record

- request file:
  `aristotle_input/goal058_g3_mode4_even_legendre_gram_2026_08_15.md`
- request SHA-256:
  `e57db1f72a0d834a446ba7b8935afd79c749cc832348f3107dc0c786b7c8d4ed`
- project:
  `036bf9ec-0307-48a8-8143-fc2fbfb357a2`
- task:
  `5ff02020-d5ff-432e-92af-42de2ce2c040`
- status at local kernel completion: `IN_PROGRESS`
- supplier status: `NOT_USED_AS_SUPPLIER`; local proof completed independently

The first CLI attempt never created a project because the full local `.lake`
made a 1.05 GB archive above Aristotle's 100 MB limit.  The successful retry
used a temporary source-only closure of the five exact Q3 dependency modules.

## Honest boundary

- `G1_STATUS: OPEN`
- `G3_STATUS: OPEN`
- `NO_P0_ZERO_FREE`
- `NO_GLOBAL_MINIMIZER`
- `NO_NODAL_COUNT`
- `NO_ORDERED_PSI4`
- `NO_G3_CLOSURE`
- `NO_G1_CLOSURE`
- `NO_ROUTE_PROMOTION`
- `NO_RH_CLAIM`

Current stop after this closeout:

`G3_MODE4_FINITE_LEGENDRE_QUADRATIC_FORM_AND_P0_MINMAX_NOT_YET_PROVED`

Per the Proshka ruling, the next finite-form theorem requires a separate
review.  No commit or push was made.
