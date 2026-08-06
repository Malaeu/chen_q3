# STATUS: OPEN — DIRECT ORTHONORMAL-BASIS PROJECTION RECONSTRUCTION SELECTED

```yaml
PRIMARY: G6_S2_P_M_N_FINITE_FOURIER_RECONSTRUCTION_SELECTED
PRIMARY_COUNT: 1

OPERATIVE_CLASS: TRY_G6_S2_D0_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION
OPERATIVE_CLASS_COUNT: 1
SELECTED_ROUTE: A_ORTHONORMAL_BASIS_SPAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  PIN: a04753e0c435006768fde50fd546acdccf1ee0cf
  ORIGIN_HEAD_EQUALS_PIN: true
  COMMIT: "[MacOS][rh_clean][Docs] Research Goal 056 projection reconstruction"

PHASE_4C:
  RESULT: G6_S2_D0_LOG_WINDOW_TRANSPORT_AND_V_MODES_ORTHONORMAL_PROVED
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean
  TRACKED_SHA256: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
  SOURCE_CONTENT_MATCH: true
  INDEPENDENT_BYTE_REHASH_BY_REVIEWER: false
  PUBLIC_THEOREMS:
    - integral_comp_logWindow_dStar
    - V_n_m_orthonormal
  PUBLIC_DEFINITIONS: 0
  VALIDATION_LEDGER_MATCH: true

ARSENAL:
  MANDATE_ACCEPTED: true
  DECK_SHA256_VERIFIED_FROM_MATERIALIZATION_LEDGER:
    018dbf6b5be6f21b2346ac29bf910d7c898d0352b72f9b67cfddf6865243839d
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

TRANSACTION:
  NAME: G6_S2_D0_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION
  OWNED_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0FiniteProjectionReconstruction.lean
  SOLE_PROJECT_IMPORT: Q3.Proofs.RouteB.D0LogWindowMeasureTransport
  DIRECT_MATHLIB_IMPORT: Mathlib.Analysis.InnerProductSpace.PiL2
  NAMESPACE: Q3.RouteB.D0Pstar
  PUBLIC_DEFINITIONS: 0
  PUBLIC_THEOREMS: 1
  PRIVATE_PRODUCTION_DECLARATIONS: 0
  LOCAL_LET_AND_HAVE_HELPERS_ONLY: true

TARGET_THEOREM:
  coe_P_m_N_apply_eq_sum_inner_V_n_m_smul

STOP: G6_S2_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION_MISSING
SUCCESS: G6_S2_P_M_N_FINITE_FOURIER_RECONSTRUCTION_PROVED

DIRECT_DOWNSTREAM_CONSUMER:
  Q3.RouteB.D0Pstar.selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
DIRECT_DOWNSTREAM_CONSUMER_AUTHORIZED: false

PHASE_KEY_CHANGE: false
NEW_CHAT: false

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_SUBMISSION: NONE
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Source and Phase-4C verification

`origin/rh_clean` resolves exactly to full commit `a04753e0c435006768fde50fd546acdccf1ee0cf`, with the stated research-only commit message. The commit changes only `INSIGHTS.md` and records this precise reconstruction target; it does not contain a hidden implementation.   `[ABSTRACT][PAPER]`

The production Phase-4C file is present at the pin. It proves:

```lean
theorem integral_comp_logWindow_dStar ...
theorem V_n_m_orthonormal ...
```

and introduces no public definition. The source keeps the exact `du/u` measure, logarithmic orientation, normalization, and conjugate-linear-first frequency difference.  `[ABSTRACT][LEAN]`

The tracked closeout records the supplied production SHA-256, direct Lean, target build 7754, full build 7817, `q3_check`, five fired plants, zero holes and forbidden imports, 10/10 proof-database declarations, 67/67 orchestration tests, strict Spine, three valid SQLite databases, and exactly the standard axiom triple for both public theorems. It also explicitly leaves projection reconstruction open and names the present target as the sole next consumer.  `[ABSTRACT][LEAN]`

The active runtime retains the same Goal-056 G6/S2 phase key and the existing conversation handle. This transaction changes neither source family nor terminal consumer and therefore does not open a new phase or chat.  `[COFINAL_FAMILY][PAPER]`

The uploaded historical Connes note concerns a separate finite companion program, not this D0 projection-reconstruction leaf; it is excluded from the proof basis of this adjudication. 

## 2. Exact project object

The project definitions already make the desired formula literal:

```lean
def modeSet (i : PairIndex) : Finset ℤ :=
  Finset.Icc (-(i.N : ℤ)) (i.N : ℤ)

def E_m_N (i : PairIndex) : Submodule ℂ (H_m i) :=
  Submodule.span ℂ (V_n_m i '' (modeSet i : Set ℤ))

def P_m_N (i : PairIndex) : H_m i →L[ℂ] E_m_N i :=
  (E_m_N i).orthogonalProjection
```

with the finite-dimensional and complete-space instances installed internally.   `[ABSTRACT][LEAN]`

There is no project theorem exposing the full reconstruction at the current pin. Repository search finds the name only in the Phase-4C goal/verdict and research notes, not as a Lean declaration.  `[ABSTRACT][PAPER]`

## 3. A–C comparison

| Route                                                          | Cancellation/source fidelity                                                    | New obligations                                                                                                                | Verdict                     |
| -------------------------------------------------------------- | ------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------ | --------------------------- |
| **A. `OrthonormalBasis.span` + `orthogonalProjection_eq_sum`** | Uses the literal modes, literal `modeSet`, literal `E_m_N`, and literal `P_m_N` | One exact subtype/span normalization and one ambient coercion                                                                  | **SELECTED**                |
| **B. Projection uniqueness**                                   | Mathematically valid                                                            | Must separately prove candidate membership, then perform span induction for orthogonality, with manual conjugation bookkeeping | Rejected by `MINIMAL_LEMMA` |
| **C. Named weakening or repaired statement**                   | Would be justified only by a real source/type mismatch                          | None exists: source and Mathlib coefficient conventions already coincide                                                       | Rejected as unnecessary     |

Mathlib v4.26 supplies the exact projection formula:

```lean
protected theorem OrthonormalBasis.orthogonalProjection_eq_sum
    {U : Submodule 𝕜 E} [CompleteSpace U]
    (b : OrthonormalBasis ι 𝕜 U) (x : E) :
    U.orthogonalProjection x =
      ∑ i, inner 𝕜 (b i : E) x • b i
```

The coefficient is `inner basisVector x`, not `inner x basisVector`.  `[ABSTRACT][LEAN]`

The project independently fixes the coefficient convention as:

```lean
c_n ... n :=
  inner ℂ (V_n_m i n)
    (kTrial_m_N ... : H_m i)
```

so there is no conjugation repair to make.  `[ABSTRACT][LEAN]`

This exact agreement is decisive. A custom uniqueness proof would merely re-prove Mathlib’s projection theorem while adding a fresh opportunity to reverse the complex inner product.

## 4. Exact selected theorem

```lean
theorem coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
    (i : PairIndex) (f : H_m i) :
    (P_m_N i f : H_m i) =
      ∑ n ∈ modeSet i,
        inner ℂ (V_n_m i n) f • V_n_m i n := by
  ...
```

`[ABSTRACT][CONDITIONAL]`

No extra assumption is permitted. In particular, the theorem must not require:

```text
f ∈ E_m_N i
f = gTrial_m ...
TrialNonzero
N > 0
real-valued coefficients
finite-cell specialization
```

It is the generic orthogonal-projection formula for every `PairIndex` and every ambient vector.

## 5. Owned file and imports

Owned production file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0FiniteProjectionReconstruction.lean
```

Sole project import:

```lean
import Q3.Proofs.RouteB.D0LogWindowMeasureTransport
```

Required direct Mathlib API import:

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
```

`D0LogWindowMeasureTransport` does not itself need `OrthonormalBasis`; therefore the new file should import the defining Mathlib module explicitly rather than depend on accidental transitive exposure. The repository is pinned to Mathlib v4.26.0 at commit `2df2f015…`.  `[ABSTRACT][LEAN]`

Namespace:

```lean
namespace Q3.RouteB.D0Pstar
```

Production surface:

```yaml
public_definitions: 0
public_theorems: 1
private_declarations: 0
```

The basis and its application identity remain local `let`/`have` objects inside the theorem.

## 6. Exact proof route

### Step 1 — install the literal carrier instances

Use the same instances already demonstrated in `D0AnchorFloor`:

```lean
letI : FiniteDimensional ℂ (E_m_N i) :=
  FiniteDimensional.span_of_finite ℂ
    ((modeSet i).finite_toSet.image (V_n_m i))

letI : CompleteSpace (E_m_N i) :=
  FiniteDimensional.complete ℂ (E_m_N i)
```

That existing module already uses these instances with the same projection and confirms the project’s inner-product orientation for the zero mode.  `[ABSTRACT][LEAN]`

### Step 2 — construct the exact basis of `E_m_N`

Pinned Mathlib defines:

```lean
OrthonormalBasis.span
  (h : Orthonormal 𝕜 v')
  (s : Finset ι') :
  OrthonormalBasis s 𝕜
    (Submodule.span 𝕜 (s.image v' : Set E))
```

and proves that its ambient value at subtype index `n : s` is exactly `v' n`.  `[ABSTRACT][LEAN]`

Use:

```lean
let b : OrthonormalBasis (modeSet i) ℂ (E_m_N i) := by
  simpa only [E_m_N, Finset.coe_image] using
    OrthonormalBasis.span (V_n_m_orthonormal i) (modeSet i)
```

The only carrier conversion is:

```text
((modeSet i).image (V_n_m i) : Set (H_m i))
=
V_n_m i '' (modeSet i : Set ℤ).
```

That is exactly the `Finset.coe_image` normalization used internally by `OrthonormalBasis.span`; no new surrogate submodule is introduced.  `[ABSTRACT][LEAN]` **[C04]**

Record locally:

```lean
have hb_apply (n : modeSet i) :
    ((b n : E_m_N i) : H_m i) = V_n_m i n := by
  ...
```

using `OrthonormalBasis.span_apply`.

### Step 3 — invoke the projection formula once

Use:

```lean
have hproj := b.orthogonalProjection_eq_sum f
```

This returns the exact equality in `E_m_N i`.

### Step 4 — return to the ambient carrier

Apply the subtype coercion to `H_m i`, unfold only `P_m_N`, and normalize:

```text
Submodule.coe_sum
Submodule.coe_smul
hb_apply
subtype/Fintype sum over `modeSet i`
```

The subtype-indexed sum is converted to:

```lean
∑ n ∈ modeSet i, ...
```

by the standard subtype/attached-Finset sum normalization; `Finset.sum_attach` is available in the pinned big-operator layer.

No pointwise `Lp` representative, integral, Mellin transform, or `rawFplus` theorem is needed.

## 7. Convention locks

### Coefficient orientation

Required:

```lean
inner ℂ (V_n_m i n) f
```

Forbidden:

```lean
inner ℂ f (V_n_m i n)
```

Mathlib is conjugate-linear in the first argument; these are conjugates, not interchangeable. `[ABSTRACT][LEAN]`

### Finite boundary

Required:

```lean
modeSet i = Finset.Icc (-(i.N : ℤ)) (i.N : ℤ)
```

Both endpoints are included, including the upper mode `+N`.  `[ABSTRACT][LEAN]`

### Carrier

Required:

```lean
E_m_N i
```

as already defined. No separately named “equivalent Fourier span” may replace it.

### Projection

Required:

```lean
P_m_N i
```

not the identity, not an arbitrary finite-rank operator, and not a projection onto a shifted or pruned mode family.

### Output category

The final equality is in ambient `H_m i`, after coercing the subtype-valued projection. It is not merely an equality between coordinate vectors or an equality inside an independently reconstructed submodule. **[C04][C10]**

## 8. K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  ambient_carrier: H_m i
  exact_submodule: E_m_N i
  exact_projection: P_m_N i
  index_finset: modeSet i
  index_boundary: Icc (-N) N
  basis_family: V_n_m i
  basis_restriction: subtype_of_modeSet_i
  coefficient_orientation: inner_V_n_f
  scalar_action: complex_smul_in_H_m
  output: ambient_coercion_of_projection
```

Any change to one of these fields after a plant fires is a new transaction, not a repair.

## 9. Mandatory plants

### `P056M-1 — coefficient orientation`

Mutation:

```lean
inner ℂ f (V_n_m i n)
```

in place of:

```lean
inner ℂ (V_n_m i n) f
```

Concrete witness:

```text
N = 0,
f = I • V_0.
```

The correct coefficient is `I`; the mutated coefficient is `-I`.

Required result:

```text
G6_S2_FINITE_PROJECTION_COEFFICIENT_ORIENTATION_MISMATCH
```

`[FINITE_CELL][LEAN]`

### `P056M-2 — upper mode boundary`

Mutation:

```text
(modeSet i).erase (i.N : ℤ)
```

Concrete witness:

```text
N = 1,
f = V_1.
```

The literal projection returns `V_1`; the mutated finite sum omits it.

Required result:

```text
G6_S2_FINITE_PROJECTION_MODESET_BOUNDARY_MISMATCH
```

`[FINITE_CELL][LEAN]`

### `P056M-3 — literal carrier`

Mutation:

```text
project onto span of (modeSet i).erase 0
```

instead of the literal `E_m_N i`.

Concrete witness:

```text
N = 1,
f = V_0.
```

Required result:

```text
G6_S2_FINITE_PROJECTION_CARRIER_MISMATCH
```

`[FINITE_CELL][LEAN]` **[C10]**

### `P056M-4 — basis normalization`

Mutation:

```text
use an arbitrary stdOrthonormalBasis of E_m_N i
```

instead of:

```text
OrthonormalBasis.span (V_n_m_orthonormal i) (modeSet i).
```

The generic projection sum remains mathematically valid, but it no longer reduces to the literal `V_n_m` coefficients and therefore cannot prove the target theorem.

Required result:

```text
G6_S2_FINITE_PROJECTION_BASIS_NORMALIZATION_MISMATCH
```

`[ABSTRACT][LEAN]` **[C04]**

### `P056M-5 — projection versus identity`

Mutation:

```lean
f
```

in place of:

```lean
(P_m_N i f : H_m i).
```

Concrete witness:

```text
N = 0,
f = V_1.
```

The finite projection onto the zero-mode span is zero, while the identity returns `V_1`.

Required result:

```text
G6_S2_FINITE_PROJECTION_NOT_IDENTITY
```

`[FINITE_CELL][LEAN]`

All five plants mutate distinct facts: conjugation, endpoint inclusion, submodule identity, basis normalization, and projection semantics.

## 10. Validation gates

Required gates:

```text
SOURCE LOCK
- HEAD = origin/rh_clean = a04753e0c435006768fde50fd546acdccf1ee0cf
- Phase-4C source SHA matches 59c6d9...
- no source file changed underneath the transaction

LEAN
- direct Lean on D0FiniteProjectionReconstruction.lean
- dedicated target build
- full build
- q3_check PASS

TAINT
- zero sorry
- zero admit
- zero exact?
- zero native_decide
- zero declared axiom
- zero opaque proof certificate
- zero Float
- zero import from aristotle_output
- zero import from ACTIVE/RequestProject

SURFACE
- exactly one public theorem
- zero public definitions
- zero private production declarations

PLANTS
- P056M-1 through P056M-5 all fire
- temporary mutation files removed

AXIOMS
- #print axioms
  Q3.RouteB.D0Pstar.coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
- exact result:
  [propext, Classical.choice, Quot.sound]

PROJECT INFRASTRUCTURE
- proof DB reimport; every declaration from the new file marked proven
- strict Spine PASS:
  python3 orchestrator/spine.py --strict --reason goal-close
- orchestration tests: 67/67 PASS
- SQLite integrity:
  knowledge.db = ok
  aristotle_proofs.db = ok
  observability.db = ok
- observability source count and stale count reported
- git diff --check
- exact git status
```

The strict Spine command is part of the repository’s documented CLI.  `[ABSTRACT][PAPER]`

## 11. Direct downstream consumer — not authorized

Exactly one downstream theorem is named:

```text
Q3.RouteB.D0Pstar.
  selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
```

Its job will be to specialize the reconstruction to the selected normalized projected trial and identify its exact Mellin/Fourier coordinate with Phase 4A’s literal `selectedRawTransformCoordinate`.

It is **not authorized in this batch**.

That future theorem must still handle:

```text
the selected parent/extract index;
the `Lp` representative;
the `x = log(lambda*u)` coordinate;
the centered phase;
the rawFplus reflection;
the selected normalizer.
```

Reconstruction removes only the abstract-projection part. `[COFINAL_FAMILY][CONDITIONAL]`

## 12. Dependency edge removed on success

Before this theorem, the route contains an unresolved edge:

```text
abstract orthogonal projection P_m_N
    ↓
literal finite Fourier coefficient polynomial
```

After success, that edge becomes a proved equality:

```text
P_m_N f
=
Σ inner(V_n,f) V_n.
```

Consequently, every subsequent linear coordinate of the projected vector can be reduced to a finite mode sum without re-opening projection geometry.

This is **PROOF_PROGRESS**, not wrapper progress:

* it proves an unconditional equality for every `PairIndex` and every `f : H_m i`;
* it removes an actual dependency edge;
* no hypothesis, structure, alias, or future budget is introduced;
* the result is directly consumed by the object-first residual program.

## 13. Strongest attack

> `OrthonormalBasis.span` constructs a basis of
> `span ((modeSet i).image V_n_m)`.
> How do we know the proof has not silently moved from the literal project carrier `E_m_N i` to an isomorphic surrogate?

This is the only serious implementation risk.

The answer must be a literal equality, not an equivalence:

```text
Finset image as a Set
=
Set image of the coerced Finset
```

followed by the existing definition of `E_m_N`.

The implementation may use:

```lean
Finset.coe_image
```

and definitional unfolding of `E_m_N`.

It may not introduce:

```text
E_m_N'
FourierSpan
EquivalentGalerkinSpace
a separately transported projection
```

If the exact carrier does not normalize, the transaction stops with:

```text
G6_S2_FINITE_PROJECTION_BASIS_CARRIER_NORMALIZATION_GAP
```

It does not weaken the theorem to a projection on a newly named equal-looking span. That is the C04/C10 firewall.

## 14. Final proposal

Select route A and prove exactly one theorem.

The registered prediction is:

```text
The theorem closes in one bounded file through
OrthonormalBasis.span + orthogonalProjection_eq_sum.

The only likely Lean friction is normalization of:
  Finset.image ↔ Set.image,
  subtype sum ↔ Finset sum,
  E_m_N-valued sum ↔ ambient H_m-valued sum.
```

No new mathematics, conditional input, test-class change, or analytic estimate is required.

### Meta closeout

**What became smaller?**

```text
full residual crosswalk
```

is reduced to:

```text
projection reconstruction
→ projected-coordinate identity
→ full-object/Gwin identity
→ residual crosswalk.
```

**What was killed?**

* custom projection-uniqueness proof as the primary route;
* any named weakening;
* arbitrary orthonormal-basis substitution;
* conjugate-swapped coefficients;
* a surrogate Galerkin carrier.

**What must not be tried again?**

Do not re-prove orthogonal-projection uniqueness by span induction while the exact Mathlib basis theorem applies.

**Current smallest named gap:**

```text
G6_S2_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION_MISSING
```

**Next cheapest decisive step after success:**

```text
selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate
```

It remains unauthorized.

**Prediction fate:**

```text
Prior prediction:
  after Phase 4C, projection reconstruction becomes a small leaf.
  CONFIRMED BY SOURCE/API AUDIT; theorem not yet compiled.

Prior prediction:
  coefficient orientation remains source-sensitive.
  CONFIRMED: project and Mathlib both use inner(V_n,f).
```

```yaml
iteration:
  target: finite_P_m_N_projection_reconstruction
  status: OPEN
  failed_strategy: custom_projection_uniqueness_before_using_exact_orthonormal_basis_API
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: G6_S2_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION_MISSING
  invariant_learned: literal E_m_N carrier and inner_V_n_f orientation must survive subtype normalization
  forbidden_future_move: replace E_m_N with an isomorphic auxiliary Fourier span
  next_decisive_test: direct Lean compilation of the one-theorem basis proof with all five plants
  progress_class: PROOF_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_G6_S2_D0_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION

TRANSACTION:
  G6_S2_D0_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: a04753e0c435006768fde50fd546acdccf1ee0cf
  expected_phase4C_sha256: 59c6d9a3a3a3c77427997665216e3ff797b9e2dc925cb63e5e9e6df0df64905b
  expected_mathlib_rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0FiniteProjectionReconstruction.lean

IMPORTS:
  project:
    - Q3.Proofs.RouteB.D0LogWindowMeasureTransport
  mathlib:
    - Mathlib.Analysis.InnerProductSpace.PiL2

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 0
  theorems: 1
  private_production_declarations: 0

TARGET_THEOREM: |
  theorem coe_P_m_N_apply_eq_sum_inner_V_n_m_smul
      (i : PairIndex) (f : H_m i) :
      (P_m_N i f : H_m i) =
        ∑ n ∈ modeSet i,
          inner ℂ (V_n_m i n) f • V_n_m i n := by
    ...

REQUIRED_PROOF_ROUTE:
  - install the exact FiniteDimensional and CompleteSpace instances for E_m_N i
  - construct OrthonormalBasis.span from V_n_m_orthonormal i and modeSet i
  - normalize its carrier to literal E_m_N i using E_m_N and Finset.coe_image
  - record exact basis application with OrthonormalBasis.span_apply
  - invoke OrthonormalBasis.orthogonalProjection_eq_sum exactly once
  - unfold only P_m_N
  - coerce the subtype equality back to H_m i
  - normalize the subtype-indexed sum to the literal Finset double sum
  - preserve coefficient orientation inner(V_n_m i n, f)

FORBIDDEN_PROOF_ROUTE:
  - custom uniqueness proof via eq_starProjection_of_mem_of_inner_eq_zero
  - new auxiliary Fourier span
  - arbitrary stdOrthonormalBasis
  - inner f (V_n_m i n)
  - theorem weakening
  - specialization only to gTrial_m
  - rawFplus or Gwin reasoning
  - Phase4B contract proof
  - compact-open decay
  - SlotS2

K6_OBJECT_PRECOMMIT:
  ambient_carrier: H_m i
  exact_submodule: E_m_N i
  exact_projection: P_m_N i
  exact_finset: modeSet i
  exact_boundary: Icc_negative_N_positive_N
  exact_basis: V_n_m i restricted to modeSet i
  exact_coefficient: inner_V_n_f
  exact_output: ambient_coercion

MANDATORY_PLANTS:
  P056M_1_COEFFICIENT_ORIENTATION:
    mutation: inner_f_V_n
    witness: N_0_and_f_eq_I_smul_V0
    expected: G6_S2_FINITE_PROJECTION_COEFFICIENT_ORIENTATION_MISMATCH

  P056M_2_MODESET_BOUNDARY:
    mutation: erase_positive_N
    witness: N_1_and_f_eq_V1
    expected: G6_S2_FINITE_PROJECTION_MODESET_BOUNDARY_MISMATCH

  P056M_3_LITERAL_CARRIER:
    mutation: project_to_span_with_zero_mode_erased
    witness: N_1_and_f_eq_V0
    expected: G6_S2_FINITE_PROJECTION_CARRIER_MISMATCH

  P056M_4_BASIS_NORMALIZATION:
    mutation: replace_span_basis_by_arbitrary_orthonormal_basis
    expected: G6_S2_FINITE_PROJECTION_BASIS_NORMALIZATION_MISMATCH

  P056M_5_PROJECTION_NOT_IDENTITY:
    mutation: replace_P_m_N_f_by_f
    witness: N_0_and_f_eq_V1
    expected: G6_S2_FINITE_PROJECTION_NOT_IDENTITY

VALIDATION:
  - verify HEAD origin equality before editing
  - verify Phase4C SHA before editing
  - direct Lean on D0FiniteProjectionReconstruction.lean
  - dedicated target build
  - full build
  - q3_check PASS
  - taint and forbidden-import scan
  - exactly one public theorem
  - zero public definitions
  - zero private production declarations
  - all five plants fire
  - remove all temporary mutation files
  - print axioms for the public theorem
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database reimport
  - require every declaration from the new file marked proven
  - run 67 orchestration tests
  - run python3 orchestrator/spine.py --strict --reason goal-close
  - require strict Spine PASS
  - run SQLite integrity on knowledge.db
  - run SQLite integrity on aristotle_proofs.db
  - run SQLite integrity on observability.db
  - require all three equal ok
  - git diff --check
  - exact git status report

STOP:
  G6_S2_FINITE_ORTHOGONAL_PROJECTION_RECONSTRUCTION_MISSING

SUCCESS:
  G6_S2_P_M_N_FINITE_FOURIER_RECONSTRUCTION_PROVED

FAILURE_CODES:
  - G6_S2_FINITE_PROJECTION_BASIS_CARRIER_NORMALIZATION_GAP
  - G6_S2_FINITE_PROJECTION_COE_SUM_NORMALIZATION_GAP
  - G6_S2_FINITE_PROJECTION_COEFFICIENT_ORIENTATION_MISMATCH
  - G6_S2_FINITE_PROJECTION_MODESET_BOUNDARY_MISMATCH
  - G6_S2_FINITE_PROJECTION_CARRIER_MISMATCH
  - G6_S2_FINITE_PROJECTION_BASIS_NORMALIZATION_MISMATCH
  - G6_S2_FINITE_PROJECTION_NOT_IDENTITY
  - G6_S2_FINITE_PROJECTION_PLANT_INERT
  - LEAN_BUILD_FAIL

DIRECT_DOWNSTREAM_CONSUMER_NOT_AUTHORIZED:
  Q3.RouteB.D0Pstar.selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate

DO_NOT_MODIFY:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0LogWindowMeasureTransport.lean
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzCenteredCoordinateLock.lean
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
  - Q3.Main
  - Goal_055
  - Bus_010

FORBIDDEN:
  - raw_Gwin_equality
  - proof_of_Phase4B_contract
  - compact_open_decay
  - SlotS2
  - Aristotle_submission
  - route_promotion
  - PX_claim
  - RH_claim
  - fresh_Proshka_chat

PHASE:
  phase_key_change: false
  reuse_existing_chat: true

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
