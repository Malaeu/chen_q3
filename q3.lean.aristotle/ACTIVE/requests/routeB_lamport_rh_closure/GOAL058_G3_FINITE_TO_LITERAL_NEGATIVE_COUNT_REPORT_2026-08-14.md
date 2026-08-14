# Goal 058 G3 — eventual finite-to-literal negative-count transport

Date: 2026-08-14

## Verdict boundary

`G3_MODE4_FINITE_TO_LITERAL_NEGATIVE_COUNT_TRANSPORT_PROVED`

This is a bounded fixed-endpoint transport theorem only:

`[COFINAL_FAMILY][CONDITIONAL][LEAN]`

It does not provide a numerical negative count, endpoint nonsingularity,
classical mode indexing, G3 or G1 closure, Route B promotion, or RH.

## Production artifact

File:

`q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FiniteToLiteralNegativeCount.lean`

SHA-256:

`feb50777a50fa78c9fbdc60ee3fb583a53844bba754cc0433e77c7f3302f8709`

The file has one direct import:

```lean
import Q3.Proofs.RouteB.D0Mode4FiniteBlockInertiaAdditivity
```

It adds one public theorem:

```lean
theorem
    mode4ActualFiniteJacobiTruncation_negativeCount_eventually_eq_hermitianSchurMatrix
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hdet :
      (mode4HermitianSchurMatrix mProject Λ K).det ≠ 0) :
    ∀ᶠ d in Filter.atTop,
      mode4HermitianNegativeEigenvalueCount
          (mode4ActualFiniteJacobiTruncation mProject Λ K d)
          (mode4ActualFiniteJacobiTruncation_isHermitian mProject Λ K d)
        =
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ)
```

## Exact proof composition

The proof consumes exactly the three judge-selected inputs:

1. `mode4ActualFiniteJacobiTruncation_negativeCount_eq_schurApprox`;
2. `mode4BackwardTailSchurApprox_tendsto_literal`;
3. `mode4HermitianNegativeEigenvalueCount_eventually_eq_of_tendsto_of_det_ne_zero`.

The fixed-carrier stability theorem gives eventual equality between the finite
Schur approximations and the literal Hermitian Schur matrix.  The accepted
finite block-inertia theorem rewrites each finite actual truncation count to
the finite Schur count.  Their transitive composition proves the displayed
eventual equality.

The determinant hypothesis is not manufactured or discharged.  It remains an
explicit load-bearing assumption at the fixed endpoint.

## Control and validation

The initial preflight exposed stale semantic and cartographer receipts before
this file was written.  The root executor temporarily removed the owned file,
refreshed the semantic receipt and inventory, committed the inventory refresh,
and obtained clean-tree startup exit `0` with `P9_STRICT_PASS`, cartographer
current, and no discrepancies at commit `7e8848e7`.  The identical owned bytes
were then restored.

Validation:

- direct `lake env lean`: PASS;
- target `lake build Q3.Proofs.RouteB.D0Mode4FiniteToLiteralNegativeCount`:
  PASS, 7756 jobs;
- `bash scripts/q3_check.sh <file>`: PASS;
- forbidden scan for `sorry`, `admit`, `exact?`, `unsafe`, or declared
  `axiom`: no hits;
- final LF and whitespace checks: PASS;
- public theorem axioms: `[propext, Classical.choice, Quot.sound]`;
- no `sorryAx`.

## Planted guards

Scratch-only file:

`/tmp/Goal058Mode4FiniteToLiteralNegativeCountPlants.lean`

SHA-256:

`f3107618dc70e543972f955c14fbbd9d095d90113161caf68fe6a40421c5ad60`

Direct Lean: PASS.  All three plant theorems use only standard axioms.

1. `MODE4_FINITE_TO_LITERAL_HDET_REQUIRED`
   proves that negative one-cell matrices `[-1/(d+1)]` converge to the
   singular zero cell while their negative count stays `1` and the limit
   count is `0`.  The `det ≠ 0` endpoint guard is load-bearing.
2. `MODE4_FINITE_TO_LITERAL_NUMERICAL_COUNT_NOT_SUPPLIED`
   exhibits nonsingular one-cell endpoints with negative counts `0` and `1`.
   The transport theorem does not manufacture a numeral.
3. `MODE4_FINITE_TO_LITERAL_EVENTUAL_NOT_POINTWISE`
   gives a sequence with one exceptional negative first cell and a constant
   positive nonsingular tail.  Convergence yields eventual equality, not
   pointwise equality for every depth.

## Exact remaining wall

The theorem transports an independently supplied literal Schur negative count
back to sufficiently deep actual finite truncations.  It supplies neither the
literal count nor the ordered-spectrum/index crosswalk.

The strongest surviving G3 wall remains:

`SOURCE_COUNTS_AND_INDEX4_IDENTIFICATION_MISSING`

An honest next source leaf must establish the required literal fixed-endpoint
negative counts (or an equivalent classical ordered-even-spectrum count) with
exact index, shift, reversal, and zero-offset accounting.  It may then feed the
existing `2/3` root receiver.  No finite diagnostic or conditional receiver
may be relabelled as that source theorem.

Stop code:

`FINITE_TO_LITERAL_NEGATIVE_COUNT_TRANSPORT_PROVED_SOURCE_COUNTS_AND_INDEX4_IDENTIFICATION_MISSING`
