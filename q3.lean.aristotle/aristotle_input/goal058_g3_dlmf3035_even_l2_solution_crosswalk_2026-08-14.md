# Goal 058 G3 — Aristotle request: DLMF 30.3.5 characteristic iff normalized ℓ² solution

TARGET_ID: G3_DLMF3035_CHARACTERISTIC_IFF_NORMALIZED_L2_LEFT_SOLUTION

PRIMARY_CLASS: BOUNDED_SOURCE_OBJECT_CROSSWALK

## Source lock

```yaml
REPOSITORY: Malaeu/chen_q3
BRANCH: rh_clean
SOURCE_HEAD: 5a67fdeb51595d7bf055850de1ad32af59db6e3d
ROUTE: CHALLENGER_NOT_RH
G1: OPEN
G3: OPEN
PX_RH_CLAIM: NOT_MADE
```

Required supplier hashes:

```text
5ee718a3868f0698712a296ab37ec09469de07bcb5b88b94b26c5cd4bbe4919c
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4DLMF3035EvenCharacteristicSource.lean

0822a3593ce11984bca31c2c619420af02868447a5a31c54db5697d8a3d1ab06
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4DLMF3035EvenRightBranchCrosswalk.lean
```

Abort rather than adapt if either supplier hash differs.  A later executor
commit which changes only this request, logs, or derived receipts is not a
reason to mutate the theorem.

Primary source convention inherited from the allowed import:

- NIST DLMF 30.3.5 and 30.3.7;
- order zero and even degrees `k = 2*q`;
- `G = gamma^2`;
- project `Lambda =` DLMF `lambda`;
- split degree is exactly `2 * (K - 1)`, so the first right coefficient has
  degree `2*K`.

## Owned file

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4DLMF3035EvenL2SolutionCrosswalk.lean
```

Create or modify only this file.

## Direct import policy

The owned file must have exactly this one direct import:

```lean
import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenCharacteristicSource
```

No other direct Q3 import is allowed.  Mathlib declarations available
transitively through this import may be used.

The following two convenient later declarations are intentionally **not** in
the allowed import closure and must not be imported or referenced:

```text
mode4TailCoefficientRow_sq_summable
mode4HermitianTail_sqSummable_solution_unique_up_to_scale
```

This absence was kernel-checked before dispatch.  If their underlying bounded
arguments are needed, prove private local lemmas from the definitions and
contraction/right-tail facts already available through the allowed import.

## Exact existing inputs

The allowed import supplies these exact objects:

```lean
noncomputable def mode4DLMF3035EvenLeftPair
    (G Λ : ℝ) : ℕ → ℝ × ℝ

noncomputable def mode4DLMF3035EvenRightRatio
    (G Λ : ℝ) (K : ℕ) : ℝ

noncomputable def mode4DLMF3035EvenCharacteristicEquation
    (G Λ : ℝ) (splitDegree : ℕ) : Prop

theorem mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20) :
    mode4DLMF3035EvenRightRatio
        (mode4JacobiG mProject) Λ K =
      mode4RightTailLimit mProject Λ K

theorem mode4RightTailLimit_eq_tailMap_succ
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20) :
    mode4RightTailLimit mProject Λ K =
      mode4TailMap
        (mode4JacobiG mProject) Λ K
        (mode4RightTailLimit mProject Λ (K + 1))
```

Also use any coefficient positivity, contraction, invariant-interval,
finite-left recurrence, and right-tail limit facts that are genuinely in the
transitive environment of the single allowed import.

## Exact new public definition and theorem

The output file must contain exactly this public definition:

```lean
/-- Normalized left coefficient selected by the parity boundary
`a₋₁ = 0`, `a₀ = 1`. -/
noncomputable def mode4DLMF3035EvenLeftCoefficient
    (G Λ : ℝ) (q : ℕ) : ℝ :=
  (mode4DLMF3035EvenLeftPair G Λ q).2
```

It must prove exactly this public theorem without adding binders:

```lean
namespace Q3.RouteB

theorem
    mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20) :
    mode4DLMF3035EvenCharacteristicEquation
        (mode4JacobiG mProject) Λ (2 * (K - 1))
      ↔
    Summable
      (fun q : ℕ =>
        ‖mode4DLMF3035EvenLeftCoefficient
            (mode4JacobiG mProject) Λ q‖ ^ 2) := by
  -- proof
```

Do not change `Summable`, the square, the normalization, the split, or any
production hypothesis.  Do not weaken the biconditional.

## Required proof mechanism

Forward direction:

1. unfold only the independent characteristic predicate and normalized
   finite-left recurrence;
2. at exact split `2*(K-1)`, use the pole-safe match to splice the normalized
   finite-left row to the infinite contraction-selected right ratio;
3. prove from the allowed-import facts that the resulting right tail decays
   sufficiently for the squared coefficients to be summable;
4. add the finite prefix without changing the global normalized row.

Reverse direction:

1. start from square summability of the exact normalized left row;
2. derive the required tail decay/non-dominant branch property;
3. use the recurrence and contraction/right-tail uniqueness available from
   the allowed import, or prove the required bounded uniqueness privately;
4. conclude the division-free pole-safe matching equality at split
   `2*(K-1)`.

The proof must operate on the literal DLMF recurrence.  It may not travel
through the project root equation.

## Forbidden assumptions, declarations, and shortcuts

- no occurrence of `mode4RootFunction` in the owned file;
- do not use
  `mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero`;
- no supplied matching root;
- no supplied arbitrary coefficient row;
- no finite terminal right tail in place of the infinite ratio;
- no endpoint counts `2/3`;
- no mode index or `psi4` selector;
- no `mode4ClassicalEvenEigenvalue` or convergence to it as a binder;
- no finite negative-count stability as an infinite-spectrum theorem;
- no actual prolate-mode constructor, finite-Fourier relation, G1 floor,
  Route export, or RH declaration;
- no new axiom, `opaque`, `sorry`, `admit`, `exact?`, or `native_decide`.

## Anti-circularity plants and rejection codes

The production proof and public surface must reject each mutation:

```text
P-G3-1 ROOTFUNCTION_DEFINITION
  define characteristic equation as mode4RootFunction = 0
  -> G3_DLMF3035_SOURCE_EQUATION_TAUTOLOGICAL

P-G3-2 FINITE_TAIL
  replace mode4RightTailLimit by one terminal-zero finite fraction
  -> G3_DLMF3035_FINITE_TAIL_SURROGATE

P-G3-3 DOMINANT_BRANCH
  drop square summability and accept any recurrence row
  -> G3_DLMF3035_DOMINANT_BRANCH_NOT_EXCLUDED

P-G3-4 ZERO_ROW
  remove a_0 = 1 normalization so the zero row satisfies the recurrence
  -> G3_DLMF3035_ZERO_SOLUTION_TAUTOLOGY

P-G3-5 SPLIT
  replace 2*(K-1) by 2*K
  -> G3_DLMF3035_SPLIT_INDEX_MISMATCH

P-G3-6 COUNT_TO_SPECTRUM
  infer the result from finite nonsingular count stability
  -> G3_FINITE_COUNT_DOES_NOT_IDENTIFY_INFINITE_SPECTRUM

P-G3-7 SHIFT
  use chi = Lambda or DLMF lambda = Lambda + G in the recurrence object
  -> G3_DLMF3035_PROJECT_SHIFT_MISMATCH
```

The plants may be compile-checked private declarations or a separate concise
report, but the production theorem and owned file are the primary output.

## Axiom gate

The file must end with:

```lean
#print axioms mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable
```

Allowed public axioms:

```text
propext
Classical.choice
Quot.sound
```

Forbidden: `sorryAx`, any new project axiom, `opaque`, and `native_decide`.

## Expected output

On success, return the complete contents of the single owned Lean file and
the code:

```text
G3_DLMF3035_CHARACTERISTIC_IFF_NORMALIZED_L2_LEFT_SOLUTION_PROVED
```

If the theorem cannot be closed from the single allowed import, do not mutate
the statement or add an import.  Return exactly one typed stop plus the
smallest missing Lean lemma signature:

```text
G3_DLMF3035_LEFT_COEFFICIENT_INDEX_MISMATCH
G3_DLMF3035_POLE_SAFE_SPLICE_GAP
G3_DLMF3035_SQSUMMABLE_TAIL_UNIQUENESS_GAP
G3_DLMF3035_DOMINANT_BRANCH_NOT_EXCLUDED
G3_DLMF3035_ROOTFUNCTION_CIRCULARITY
G3_DLMF3035_FINITE_TAIL_SURROGATE
G3_DLMF3035_VALIDATION_FAILED
```

## Validation commands

```bash
cd /Users/emalam/GitHub/rh_lean_01_2026
test "$(shasum -a 256 \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenCharacteristicSource.lean \
  | awk '{print $1}')" = \
  "5ee718a3868f0698712a296ab37ec09469de07bcb5b88b94b26c5cd4bbe4919c"

cd q3.lean.aristotle
lake env lean Q3/Proofs/RouteB/D0Mode4DLMF3035EvenL2SolutionCrosswalk.lean
lake build Q3.Proofs.RouteB.D0Mode4DLMF3035EvenL2SolutionCrosswalk
lake build

cd ..
bash scripts/q3_check.sh \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenL2SolutionCrosswalk.lean

rg -n \
  '\bsorry\b|\badmit\b|exact\?|native_decide|^[[:space:]]*axiom\b|^[[:space:]]*opaque\b' \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenL2SolutionCrosswalk.lean

rg -n \
  'mode4RootFunction|mode4ClassicalEvenEigenvalue|negativeCount|endpoint.*count|psi4|IsActualProlateModePair|finiteFourier|CanonicalRHRoute|rh_of_' \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenL2SolutionCrosswalk.lean

git diff --check -- \
  q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenL2SolutionCrosswalk.lean
```

## Nonclaims

```text
NO_JACOBI_SPECTRUM_IINF_SOLUTION_SET_IFF
NO_ENDPOINT_COUNTS
NO_INDEX4_IDENTIFICATION
NO_ACTUAL_PROLATE_PAIR
NO_FINITE_FOURIER_EIGENRELATION
NO_CCM_LEMMA_7_2
NO_G1
NO_G3
NO_ROUTE_B_PROMOTION
NO_RH
```
