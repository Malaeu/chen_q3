# Goal 058 G1/G3 post-DLMF-characteristic — Proshka verdict

Captured: 2026-08-14

Natural reasoning time: 3m 59s transport stop, then 7m 04s substantive
adjudication after the exact inline retry.

Transport:

- existing Proshka living chat for
  `PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13`;
- immutable request commit `5d1c8e78` initially returned `CACHE_MISS` to
  Proshka and produced no mathematical adjudication;
- the exact 5,748-character UTF-8 request was then pasted inline with local
  SHA-256
  `09fc6bcf6900069c61ee98d830a976b46f4f2acb16e2aa3dd45002c323aae992`;
- `Answer now` was visible and was never clicked.

The body below is transcribed from the completed final assistant block.  Only
browser layout whitespace and math line wrapping were normalized.

---

Ы.

## G3_ROUTE_DECISION: `JACOBI_INERTIA`

Выбираю не полный `DIFFERENTIAL_SPECTRUM`, а независимый бесконечный
Jacobi/ℓ²-carrier, потому что текущий tree уже имеет literal DLMF 30.3.7
coefficients, независимые left/right branches и pole-safe characteristic
predicate. Сначала надо доказать:

```text
characteristic equation
↔ normalized parity-boundary recurrence row is square-summable.
```

Затем отдельный source theorem связывает этот ℓ²-spectrum с
`mode4ClassicalEvenEigenvalue`. Одна лишь inertia/count-jump лестница стену не
сокращает: без ℓ²-spectral identification она только переименовывает
отсутствующий solution-set theorem. Текущий adapter уже честно отделяет
independent characteristic object от `mode4RootFunction`; полный solution-set
iff пока отсутствует.

## G3_EXACT_NEXT_HEAD

```lean
namespace Q3.RouteB

/-- Normalized left coefficient selected by the parity boundary
`a₋₁ = 0`, `a₀ = 1`. -/
noncomputable def mode4DLMF3035EvenLeftCoefficient
    (G Λ : ℝ) (q : ℕ) : ℝ :=
  (mode4DLMF3035EvenLeftPair G Λ q).2

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
            (mode4JacobiG mProject) Λ q‖ ^ 2)
```

Механизм: matching at split splices the normalized finite-left row to the
unique square-summable right branch; conversely square summability plus tail
uniqueness forces the pole-safe matching equation. Используются
`mode4RightTailLimit`, its Riccati uniqueness,
`mode4TailCoefficientRow_sq_summable`, and square-summable Hermitian-tail
uniqueness. Split остаётся `2*(K-1)`, не `2*K`.

Следующий, ещё не готовый source theorem:

```lean
theorem mode4DLMF3035EvenLeftCoefficient_sqSummable_iff_finiteLimitSpectrum
    (G Λ : ℝ) (hG : 0 < G) :
    Summable
        (fun q =>
          ‖mode4DLMF3035EvenLeftCoefficient G Λ q‖ ^ 2)
      ↔
    ∃ j : ℕ, mode4ClassicalEvenEigenvalue G j = Λ
```

## G3_ANTICIRCULARITY_PLANTS

```text
P-G3-1 ROOTFUNCTION_DEFINITION:
  define characteristic equation as mode4RootFunction = 0
  → G3_DLMF3035_SOURCE_EQUATION_TAUTOLOGICAL

P-G3-2 FINITE_TAIL:
  replace mode4RightTailLimit by one terminal-zero finite fraction
  → G3_DLMF3035_FINITE_TAIL_SURROGATE

P-G3-3 DOMINANT_BRANCH:
  drop square summability and accept any recurrence row
  → G3_DLMF3035_DOMINANT_BRANCH_NOT_EXCLUDED

P-G3-4 ZERO_ROW:
  remove a₀=1 parity normalization so the zero row satisfies everything
  → G3_DLMF3035_ZERO_SOLUTION_TAUTOLOGY

P-G3-5 SPLIT:
  replace 2*(K-1) by 2*K
  → G3_DLMF3035_SPLIT_INDEX_MISMATCH

P-G3-6 COUNT_TO_SPECTRUM:
  infer solution-set iff from finite nonsingular count stability
  → G3_FINITE_COUNT_DOES_NOT_IDENTIFY_INFINITE_SPECTRUM

P-G3-7 SHIFT:
  use χ=Λ or DLMF λ=Λ+G in the recurrence object
  → G3_DLMF3035_PROJECT_SHIFT_MISMATCH
```

## G1_ROUTE_DECISION

`ACTUAL_DEGREE_0_4_PROLATE_MODE_EXISTENCE_AND_SELECTION_FIRST`.

CCM Lemma 7.2 cannot be the first producer because it must apply to an already
source-locked actual `h₀,λ`, `h₄,λ` pair. An arbitrary rate binder would be a
receiver. The independent even-head coercivity theorem remains a parallel G1
obligation, but it does not manufacture the missing source trial. No missed
supplier exists: `IsActualProlateModePair` is already kernel-checked only as a
contract, and the loose-pair plant proves the old `ProlatePair` fields do not
imply actuality.

## G1_EXACT_NEXT_HEAD

```lean
namespace Q3.RouteB.D0Pstar

theorem exists_actualProlateModePair_at_m
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ P : ProlatePair,
      P.pw.lambda = Real.sqrt m ∧
      IsActualProlateModePair P
```

После этого production constructor обязан выбрать `S.pair i` только через
`i.m`, не через `i.N`, и вывести:

```lean
theorem exists_actualProlateKTrialSourceData :
    ∃ S : ProlateKTrialSourceData,
      ∀ i : PairIndex,
        IsActualProlateModePair (S.pair i)
```

Inputs: `m ≥ 2`, source parameter `λ = √m`, pinned singular
Sturm–Liouville/PSWF existence and ordering.

Output: один real-valued degree-0/degree-4 normalized pair on the unchanged
`ProlatePair`, with parity, zero counts 0/4, orthogonality, physical equation,
and nonzero restricted finite-Fourier eigenrelations encoded by
`IsActualProlateModePair`.

Primary-source pins: Osipov TR1450, Theorems 1 and 3; Slepian–Pollak, printed
pages 57–62; DLMF §§30.3–30.4 for ordered characteristic values and
normalization. Bonami–Karoui is not needed for this existence head.

Not outputs: Lemma 7.2 rate, CCM ground gap, even-head floor, schedule, or
tracking.

## DEPENDENCY_DAG

```text
G3:
  independent DLMF characteristic predicate
    → normalized ℓ² Jacobi-solution crosswalk          [next bounded leaf]
    → Jacobi spectrum / finite-iInf solution-set iff  [source theorem]
    → strict ordered carrier + endpoint separators
    → literal Schur counts 2/3 and nonsingularity
    → internal crossing label p=2
    → differential/PSWF degree-4 name crosswalk
    → actual ψ4 object

G1 / trial source:
  actual degree-0/4 ProlatePair constructor
    → CCM Lemma 7.2 O(λ⁻²) for that exact pair
    → E_star/window comparison
    → odd-contamination decay + central nondegeneracy
    → fixed-shift/Rayleigh transport
    ┐
    ├→ full q⊥ complement floor → simple/even ground + tracking
    ┘
  independent even-tail/even-head coercivity
    → same full q⊥ complement floor

separate:
  restricted finite-Fourier relation is not supplied by the Jacobi
  characteristic theorem and remains its own source edge.
```

Thus Jacobi inertia shortens the G3 root/count seam, but does not replace the
eventual actual-mode and finite-Fourier construction.

## ARISTOTLE_BOUNDARY

`ARISTOTLE_SUBMISSION_AUTHORIZED` only for the G3 ℓ²-crosswalk in field 2. The
full Jacobi-spectrum/iInf theorem and the G1 actual-mode constructor are
`NOT_READY`.

```yaml
TARGET: G3_DLMF3035_CHARACTERISTIC_IFF_NORMALIZED_L2_LEFT_SOLUTION

OWNED_FILE: >-
  q3.lean.aristotle/Q3/Proofs/RouteB/
  D0Mode4DLMF3035EvenL2SolutionCrosswalk.lean

ALLOWED_IMPORTS:
  - Q3.Proofs.RouteB.D0Mode4DLMF3035EvenCharacteristicSource

FORBIDDEN_ASSUMPTIONS_OR_IMPORTS:
  - mode4RootFunction in the proof
  - supplied matching root
  - endpoint counts 2/3
  - mode index or psi4 selector
  - mode4ClassicalEvenEigenvalue convergence as a binder
  - finite negative-count stability as an infinite-spectrum theorem
  - arbitrary coefficient row
  - finite terminal right tail
  - Route/RH exports

EXACT_PUBLIC_HEAD: >-
  mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable

SUCCESS: >-
  G3_DLMF3035_CHARACTERISTIC_IFF_NORMALIZED_L2_LEFT_SOLUTION_PROVED

TYPED_STOPS:
  - G3_DLMF3035_LEFT_COEFFICIENT_INDEX_MISMATCH
  - G3_DLMF3035_POLE_SAFE_SPLICE_GAP
  - G3_DLMF3035_SQSUMMABLE_TAIL_UNIQUENESS_GAP
  - G3_DLMF3035_DOMINANT_BRANCH_NOT_EXCLUDED
  - G3_DLMF3035_ROOTFUNCTION_CIRCULARITY
  - G3_DLMF3035_FINITE_TAIL_SURROGATE
  - G3_DLMF3035_VALIDATION_FAILED
```

## G1_STATUS / G3_STATUS / STOP_CODES

```yaml
G1_STATUS: OPEN
G3_STATUS: OPEN
G1_STOP_CODE: >-
  G1_ACTUAL_PROLATE_MODE_PAIR_LEMMA72_EVEN_HEAD_FLOOR_AND_COUPLED_SCHEDULE_MISSING
G3_STOP_CODE: >-
  G3_CHARACTERISTIC_OBJECT_ADAPTER_PROVED_L2_SOLUTION_AND_FINITE_LIMIT_SPECTRUM_CROSSWALK_MISSING
ROUTE: CHALLENGER_NOT_RH
NO_G1_CLOSE: true
NO_G3_CLOSE: true
NO_ROUTE_PROMOTION: true
NO_RH_CLAIM: true
```
