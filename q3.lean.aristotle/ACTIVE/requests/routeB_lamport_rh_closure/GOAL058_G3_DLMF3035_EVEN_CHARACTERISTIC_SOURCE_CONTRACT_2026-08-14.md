# Goal 058 G3 — DLMF 30.3.5 even-characteristic source contract

Date: 2026-08-14

Repository: `/Users/emalam/GitHub/rh_lean_01_2026`

Branch: `rh_clean`

Audited pin:
`9d23f5d817ad7e06e88b7a26ff94144adb67fcba`

Origin alignment at entry: `HEAD = origin/rh_clean`, divergence `0/0`.

Lane: `CHALLENGER / NOT_RH`

Mode: one source contract only; no production Lean, Aristotle, commit, push,
Route/Bus/runtime edit, or claim promotion.

## Verdict

```yaml
TARGET: GOAL058_G3_DLMF3035_EVEN_CHARACTERISTIC_SOURCE_CONTRACT

EXACT_SOURCE_EQUATION: LOCKED
PROJECT_UNIT_INDEX_DICTIONARY: LOCKED
INTERNAL_FINITE_LIMIT_DICTIONARY: LOCKED_AT_PAPER_CONTRACT_LEVEL

RIGHT_BRANCH_DISCRIMINATOR:
  DLMF3035_RIGHT_BRANCH_CROSSWALK_READY
RIGHT_BRANCH_SCOPE:
  READY_TO_MATERIALIZE_IN_CURRENT_LAMBDA_LE_20_CONTRACTION_DOMAIN
RIGHT_BRANCH_CURRENT_LEAN_DECLARATION: false

SOURCE_SOLUTION_SET_THEOREM:
  G3_DLMF3035_SOURCE_THEOREM_NOT_LEAN_MATERIALIZED

G1: OPEN
G3: OPEN
ARISTOTLE: NOT_AUTHORIZED
ROUTE_PROMOTION: false
RH_CLAIM: false
```

The previous root-crosswalk wall is now split into two independent pieces.
The right infinite fraction can be connected to the existing project tail
without circularity. The external DLMF solution-set theorem itself is still
not a kernel-checked Lean supplier.

## 1. Knowledge preflight

Exact query:

```text
DLMF 30.3.5 even characteristic equation recessive right continued fraction mode4RightTailLimit crosswalk
```

Command:

```text
./ask.sh --deep "DLMF 30.3.5 even characteristic equation recessive right continued fraction mode4RightTailLimit crosswalk"
```

Result: exit `0`. The exact current candidates were the already known
finite-spectrum crosswalk, the conditional DLMF 30.8.4/30.8.5 coefficient-row
receiver, and the newly archived Proshka verdict. No existing
`mode4DLMF3035EvenCharacteristicEquation` or 30.3.5 solution-set theorem was
found. Retrieval matches are candidates, not proof.

## 2. Primary-source byte locks

Official source: NIST DLMF Version 1.2.7, release date 2026-06-15.

| Source | Stable URL | Fetched bytes SHA-256 |
|---|---|---|
| DLMF 30.3.5 TeX | <https://dlmf.nist.gov/30.3.E5.tex> | `f8cb8ef56617c5c4ecfa99749aaf1867b706825ab8162d414eb592b1dcce171a` |
| DLMF 30.3.7 alpha TeX | <https://dlmf.nist.gov/30.3.E7a.tex> | `d9a5681e54bbd001a9a83cea0179fc2e85bf95982a65ebaf69e06441638962e8` |
| DLMF 30.3.7 beta TeX | <https://dlmf.nist.gov/30.3.E7b.tex> | `676f7b323938c236b4b80c97e9679535f9de6a963a7254ddeda570b1d21987f9` |
| DLMF 30.3.7 gamma TeX | <https://dlmf.nist.gov/30.3.E7c.tex> | `638b32eef5f601de7e3e694933f27273e39b16152adfa6c816f49c9770b7030c` |
| DLMF 30.16.3 TeX | <https://dlmf.nist.gov/30.16.E3.tex> | `35b0b61b184dd56ecd3b17a20de6f9e13f00533b56fbfa0b4a6e544820629e4d` |
| DLMF 30.3 HTML, including solution-set prose | <https://dlmf.nist.gov/30.3> | `c75e27a41430f1c606f05cea86e3b0131a3f695eb86275649cf1b3aeb2bf958c` |
| DLMF 30.16 HTML, including the selector | <https://dlmf.nist.gov/30.16> | `f6f0f1d99b1ae7e023f1ec5c3bfbc21344e268706dad0d5fe89bda6782d8c5ad` |

The TeX bytes fetched during this transaction are recorded below without a
change of variables.

### DLMF 30.3.5

```tex
\[\beta_{p}-\lambda-\cfrac{\alpha_{p-2}\gamma_{p}}{\beta_{p-2}-\lambda-\cfrac{%
\alpha_{p-4}\gamma_{p-2}}{\beta_{p-4}-\lambda-\cdots}}=\cfrac{\alpha_{p}\gamma%
_{p+2}}{\beta_{p+2}-\lambda-\cfrac{\alpha_{p+2}\gamma_{p+4}}{\beta_{p+4}-%
\lambda-\cdots}},\]
```

For an even nonnegative split `p`, the official surrounding text identifies
the complete solution set as `lambda_(m+2j)^m(gamma^2)`, `j >= 0`. At `p=0`
the finite fraction on the left is zero; otherwise it terminates at the
matching parity boundary.

### DLMF 30.3.7

```tex
\[\alpha_{k}=\gamma^{2}\frac{(k+2m+1)(k+2m+2)}{(2k+2m+3)(2k+2m+5)},\]
\[\beta_{k}=(k+m)(k+m+1)-2\gamma^{2}\frac{(k+m)(k+m+1)-1+m^{2}}{(2k+2m-1)(2k+2m+3)},\]
\[\gamma_{k}=\gamma^{2}\frac{(k-1)k}{(2k+2m-3)(2k+2m-1)}.\]
```

### DLMF 30.16.3

```tex
\[\lambda^{m}_{n}\left(\gamma^{2}\right)=\lim_{d\to\infty}\alpha_{p,d},\]
```

The selector in the official page is

```text
pDLMF = floor((n-m)/2) + 1.
```

## 3. Exact unit and index dictionary

Use exactly:

```text
DLMF order m                     = 0
DLMF coefficient degree k       = 2*q
DLMF gamma^2                     = G
project Lambda                   = DLMF lambda
differential energy chi          = Lambda + G

project matching index K         = q of the first right-tail ratio
DLMF split degree                = 2*(K-1)
DLMF split degree is not         = 2*K

internal carrier index jLean     = 0,1,2,...
DLMF differential degree n       = 2*jLean
DLMF one-based finite selector   = jLean+1
```

The DLMF split degree and the carrier index are different variables. They may
not be silently identified.

At `m=0`, `k=2*q`, and `gamma^2=G`, DLMF 30.3.7 specializes to

```text
alpha_(2q)              = mode4JacobiUpper G q
beta_(2q) - Lambda      = mode4JacobiCenter G Lambda q
gamma_(2q)              = mode4JacobiLower G q.
```

These are literal algebraic identities. The current tree already contains the
same formulas through `mode4JacobiLower`, `mode4JacobiCenter`,
`mode4JacobiUpper`, and the DLMF 30.8 Legendre coefficient crosswalk. What is
not yet present is the source-addressed 30.3.7 spelling.

## 4. Independent source object contract

The future source module must not import or mention `mode4RootFunction` in the
definition of its source equation.

Required literal coefficient definitions:

```lean
noncomputable def mode4DLMF3037Alpha (G : ℝ) (k : ℕ) : ℝ
noncomputable def mode4DLMF3037Beta  (G : ℝ) (k : ℕ) : ℝ
noncomputable def mode4DLMF3037Gamma (G : ℝ) (k : ℕ) : ℝ
```

Required independent ingredients:

```text
mode4DLMF3035EvenLeftPair:
  the finite parity-boundary recurrence, normalized by a_(-1)=0, a_0=1,
  using only the literal 30.3.7 coefficients.

mode4DLMF3035EvenRightRatio:
  the terminal-independent limit of the explicit finite right fractions
  r_q = gamma_(2q) /
          (beta_(2q) - Lambda - alpha_(2q) * r_(q+1)),
  using only the literal 30.3.7 coefficients.
```

Pole-safe characteristic predicate:

```lean
noncomputable def mode4DLMF3035EvenCharacteristicEquation
    (G Λ : ℝ) (splitDegree : ℕ) : Prop
```

Semantic definition:

```text
Even splitDegree;
K = splitDegree/2 + 1;
the normalized finite left row and independent right ratio satisfy
  leftPair(K).2 = rightRatio(K) * leftPair(K).1.
```

This is the cross-multiplied, removable-pole-safe form of DLMF 30.3.5. A
separate theorem must connect it to the displayed nested fractions wherever
the finite denominators are nonzero. Consecutive finite continuants cannot
both vanish, so the pole-safe form does not create an extra project root.

Forbidden definition:

```lean
mode4DLMF3035EvenCharacteristicEquation ... :=
  mode4RootFunction ... = 0
```

That mutation is the desired crosswalk disguised as a source object.

## 5. Right-branch discriminator

```text
DLMF3035_RIGHT_BRANCH_CROSSWALK_READY
```

This means ready to materialize, not already present under a DLMF 30.3.5
name.

Exact noncircular supplier chain in the current production domain:

1. `mode4BackwardTail` is the finite composition of the explicit project
   maps, with an arbitrary terminal value.
2. `mode4BackwardTail_tendsto_rightTailLimit` proves terminal-independent
   convergence in the certified invariant cone.
3. `mode4RightTailLimit_eq_tailMap_succ` proves the all-index Riccati law.
4. `mode4RightTailLimit_eq_of_invariantCone_riccatiOrbit` proves uniqueness of
   any coherent ratio orbit in `[0,1/2]`.
5. `mode4TailCoefficientRow_sq_summable` constructs a square-summable row from
   those ratios.
6. `mode4HermitianTail_sqSummable_solution_unique_up_to_scale` proves that the
   symmetric square-summable branch is unique up to scale.

After the three literal 30.3.7 coefficient identities above, the DLMF right
ratio map is definitionally the same rational map as `mode4TailMap`. Therefore
the independent DLMF terminal-zero approximants agree term by term with
`mode4BackwardTail`, and their limits agree with `mode4RightTailLimit`.

The bounded theorem head is:

```lean
theorem mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    mode4DLMF3035EvenRightRatio
        (mode4JacobiG mProject) Λ K =
      mode4RightTailLimit mProject Λ K
```

The proof may use coefficient rewriting plus the existing contraction limit.
It may not use the characteristic equation, a root, an endpoint count, or the
desired solution-set theorem.

## 6. Finite-left and project-root adapter

The independent 30.3.7 finite-left recurrence has the same initial pair and
same transfer law as `mode4LeftPair`. Thus the following local theorem is
algebraic after source-object materialization:

```lean
theorem mode4DLMF3035EvenLeftPair_eq_mode4LeftPair
    (G Λ : ℝ) (K : ℕ) :
    mode4DLMF3035EvenLeftPair G Λ K =
      mode4LeftPair G Λ K
```

Combining the left and right crosswalks gives, only in the certified project
domain:

```lean
theorem mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    mode4DLMF3035EvenCharacteristicEquation
        (mode4JacobiG mProject) Λ (2 * (K - 1))
      ↔
    mode4RootFunction mProject K Λ = 0
```

This theorem is a local adapter, not the DLMF solution-set supplier.

## 7. Source solution-set theorem

DLMF 30.3.5 supplies the even characteristic solution set. DLMF 30.16.3
identifies the same zero-based project carrier index with DLMF's one-based
finite selector.

Required source theorem head:

```lean
namespace Q3.RouteB

theorem mode4DLMF30163_3035_evenCharacteristicSolutions
    (G Λ : ℝ)
    (hG : 0 < G)
    (K : ℕ)
    (hK : 1 ≤ K) :
    mode4DLMF3035EvenCharacteristicEquation
        G Λ (2 * (K - 1))
      ↔
    ∃ j : ℕ,
      mode4ClassicalEvenEigenvalue G j = Λ
```

Status:

```text
PAPER-PROVED SOURCE STATEMENT
NOT A CURRENT LEAN THEOREM
```

The right branch is no longer the smallest blocker. The blocker is the
solution-set theorem itself: the current tree has no independent formal DLMF
eigenvalue carrier or general Jacobi/continued-fraction spectral theorem from
which this exact iff follows. Adding the iff as a hypothesis would create a
receiver, not the supplier.

The internal finite-limit dictionary is source-locked as follows:

```text
mode4ClassicalEvenEigenvalue G j
  = limit of the zero-based j-th literal DLMF 30.16.1 finite eigenvalue
  = DLMF lambda_(2*j)^0(G) by DLMF 30.16.3.
```

The second equality is still a paper contract, not a current equality between
two independently defined Lean objects.

## 8. Later determinant adapter

Only after the source theorem exists, the exact production theorem is:

```lean
theorem mode4HermitianSchurMatrix_det_eq_zero_iff_exists_classicalEvenEigenvalue
    (mProject K : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    (mode4HermitianSchurMatrix mProject Λ K).det = 0
      ↔
    ∃ j : ℕ,
      mode4ClassicalEvenEigenvalue
          (mode4JacobiG mProject) j = Λ
```

Its local suppliers are already exact:

```text
det_mode4HermitianSchurMatrix_eq_schurContinuant
mode4SchurContinuant_eq_upperProd_mul_rootFunction
mode4JacobiUpper_prod_pos
```

The source module must remain independent of the project root. A later local
adapter module may import:

```lean
import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierHeadUpper
import Q3.Proofs.RouteB.D0Mode4PSWFLegendreCanonicalIdentification
import Q3.Proofs.RouteB.D0Mode4SchurHermitianSymmetrization
import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenCharacteristicSource
```

Forbidden direct imports remain endpoint-count theorems, Goal 026 brackets,
root-existence receivers, ordered-psi4 constructors, and Route/RH exports.

## 9. Mandatory plants

| Plant | Mutation | Required stop |
|---|---|---|
| P1 | define the source equation by `mode4RootFunction = 0` | `G3_DLMF3035_SOURCE_EQUATION_TAUTOLOGICAL` |
| P2 | use `Lambda + G` as DLMF lambda | `G3_DLMF3035_PROJECT_SHIFT_MISMATCH` |
| P3 | use split degree `2*K` | `G3_DLMF3035_SPLIT_INDEX_MISMATCH` |
| P4 | use the odd solution family | `G3_DLMF3035_EVEN_INDEX_MISMATCH` |
| P5 | replace the infinite right fraction by one terminal-zero finite tail | `G3_DLMF3035_FINITE_TAIL_SURROGATE` |
| P6 | use endpoint counts `2/3`, an existing bracket, or a supplied root | `G3_DLMF3035_ENDPOINT_COUNT_CIRCULARITY` |
| P7 | prove only classical eigenvalue implies project root | `G3_DLMF3035_ROOT_CROSSWALK_ONE_DIRECTION_ONLY` |

Additional pole plant:

| Plant | Mutation | Required stop |
|---|---|---|
| P8 | define the source object only by raw division and silently discard removable poles | `G3_DLMF3035_FINITE_LEFT_POLE_UNPOLICED` |

## 10. Aristotle boundary and exact next gap

```text
ARISTOTLE_NOT_AUTHORIZED
```

The missing object is a source theorem, not a bounded local algebra adapter.
Supplying it as an Aristotle binder would preserve the gap while renaming it.

The first future production transaction must materialize an independent
`D0Mode4DLMF3035EvenCharacteristicSource.lean`. Its acceptance requires:

```text
literal 30.3.7 coefficient objects;
independent finite-left and infinite-right fractions;
the pole-safe 30.3.5 characteristic predicate;
the paper-backed complete solution-set iff;
the DLMF 30.16.3 zero-based/one-based carrier dictionary;
all P1--P8 plants.
```

The current smallest named gap is:

```text
DLMF3035EvenCharacteristicSourceSolutionSetMaterialization
```

Typed stop:

```text
G3_DLMF3035_SOURCE_THEOREM_NOT_LEAN_MATERIALIZED
```

Nonclaims:

```text
G1 OPEN
G3 OPEN
NO ENDPOINT COUNTS IN LEAN
NO INDEXED DIFFERENTIAL MODE CONSTRUCTION
NO ARISTOTLE SUBMISSION
NO ROUTE PROMOTION
NO RH CLAIM
```
