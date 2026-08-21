# STATUS: CONDITIONAL — SOURCE-PURE EVEN-SPECTRUM ARISTOTLE RUN AUTHORIZED; DIRECT PROJECT-INHABITANT SUBMISSION KILLED
```yaml
PRIMARY: RUN_MS_SATZ1_M0_FIXED_G_EVEN_REGULAR_SPECTRUM
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-R

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: d3fbfc4c9fb22545c9f4cd3374ab2307ffedd141
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_BLOB: 10d28e871a19c45b322f251bb0f3765b10e8d812
  BOOK_INTERFACE_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1BookRegularSpectrumSourceInterface.lean
  BOOK_INTERFACE_BLOB: a23e9e10fd78299e60fd0e7fe19ebb2aad970e6f
  REGULAR_SOLUTION_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersRegularEvenProlateSolution.lean
  REGULAR_SOLUTION_BLOB: 62de75f6aa29e5f83c0a2beef79bf7f8bf297ecc
  CHARACTERISTIC_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4DLMF3035EvenCharacteristicSource.lean
  CHARACTERISTIC_BLOB: fb7f7ad7b9286ee0faaf03056376245306599728
  SOURCE_CARD_PATH: docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md

QUEUE_DISCIPLINE:
  OPEN_REQUESTS_FOUND: [REQ-2026-08-22-R]
  OLDER_OPEN_REQUESTS: []
  QUEUE_STATUS_MUTATED: false

DIRECT_ANSWERS:
  send_current_BookRegularEvenSpectrum: KILL_C04_C10
  send_full_project_context: false
  send_full_m_general_Satz1: false
  selected_source_theorem: M0_FIXED_G_EVEN_REGULAR_SPECTRUM_ENUMERATION
  selected_input_mode: INFORMAL_MARKDOWN_FORMALIZATION
  selected_context: IMPORT_MATHLIB_ONLY
  split_inside_one_paid_run: true
  separate_paid_parity_run: false
  separate_paid_existence_only_run: false

ARISTOTLE:
  OWNER_AUTHORIZED: true
  MAX_BUDGET_USD: 425
  RUN_AUTHORIZED_BY_THIS_VERDICT: true
  SUBMISSION_PERFORMED_BY_PROSHKA: false
  SUBMISSION_OWNER: LINUX_BODY_AFTER_HARVEST
  MODE: FORMALIZE_MARKDOWN
  ONE_DEEP_RUN: true
  TARGET_FILE_SUGGESTION: q3.lean.aristotle/aristotle_input/req_r_ms_satz1_m0_even_spectrum_2026_08_22.md
  NEGATE_STATE: REFORMULATE

REPRESENTATION:
  CURRENT_INTERFACE: OVERTYPED_AND_MIXED
  SELECTED_REPAIR: PURE_EVEN_SPECTRUM_SUPPLIER_PLUS_SEPARATE_DLMF_ADAPTER
  SYNTHETIC_ODD_BRANCH_INTERPOLATION: FORBIDDEN_C10
  FULL_ALL_PARITY_SOURCE_THEOREM: RUNNER_UP_NOT_AUTHORIZED

TARGET:
  NAME: MS_SATZ1_M0_FIXED_G_EVEN_REGULAR_SPECTRUM
  SCOPE: ABSTRACT
  VERIFIER: CONDITIONAL
  PARAMETER: FIXED_REAL_G
  ORDER: m_equals_zero
  OUTPUT: STRICTLY_INCREASING_EXHAUSTIVE_EVEN_REGULAR_EIGENVALUE_SEQUENCE
  PROJECT_OBJECTS_IN_TARGET: none

MILESTONES:
  M0_EXACT_REGULAR_EVEN_PREDICATE: REQUIRED
  M1_GREEN_WRONSKIAN_AND_ONE_DIMENSIONALITY: HARVESTABLE
  M2_EVEN_SELFADJOINT_DISCRETE_EXHAUSTIVE_SPECTRUM: LOAD_BEARING
  M3_STRICT_ENUMERATION_RANGE_EQUALITY: SUCCESS_GATE
  M4_FULL_PARITY_AND_ANALYTIC_G_CURVES: NOT_REQUIRED

ACCEPTANCE:
  FULL_ACCEPT:
    - no_sorry
    - no_admit
    - no_new_axiom_or_constant
    - compiles_in_pinned_Aristotle_Mathlib
    - axiom_profile_standard_triple_only
    - exact_degenerate_endpoint_problem
    - strictMono_sequence
    - exact_range_equality_with_regular_even_spectrum
  PARTIAL_ACCEPT:
    - at_least_one_hole_free_named_milestone_compiles
    - final_hole_does_not_count_as_closed
  REFORMULATE:
    - negate_state_or_valid_counterexample
    - regularity_predicate_proved_too_weak_or_too_strong
  REJECT:
    - regular_interval_epsilon_trim_surrogate
    - finite_matrix_or_polynomial_surrogate
    - compact_resolvent_assumed_as_hypothesis
    - singular_endpoint_replaced_by_p_positive_on_closed_interval
    - synthetic_odd_branch
    - nonexistent_Mathlib_theorem
    - custom_project_import
    - axiom_profile_beyond_standard_triple

PLANTS:
  G_ZERO_CONSTANT:
    input: G=0_f=1
    expected: even_regular_eigenvalue_Lambda=0
  G_ZERO_ODD_EXCLUSION:
    input: G=0_f=x
    expected: regular_but_not_even_Lambda=2_not_in_even_spectrum
  G_ZERO_QUADRATIC:
    input: G=0_f=(3*x^2-1)/2
    expected: even_regular_eigenvalue_Lambda=6
  ENDPOINT_LOG_BRANCH:
    input: Legendre_second_kind_log_singular_solution
    expected: excluded_by_closed_endpoint_regularity
  SHIFT_DISCRIMINATOR:
    expected: project_Lambda_not_Lambda_plus_G

REGISTERED_PREDICTIONS:
  P_R_1:
    claim: direct_project_inhabitant_submission_would_return_category_mismatch_surrogate_or_hidden_assumption
    probability: 0.90
  P_R_2:
    claim: source_pure_even_spectrum_run_returns_at_least_one_hole_free_Green_Wronskian_or_simplicity_lemma
    probability: 0.72
  P_R_3:
    claim: full_strict_exhaustive_enumeration_compiles_in_one_run
    probability: 0.28
  P_R_4:
    claim: most_likely_first_load_bearing_failure_is_singular_endpoint_compact_resolvent_or_compact_embedding
    probability: 0.76
  RETROACTIVE_REPAIR: false

CANDIDATE_REPRESENTATIONS:
  R1_EVEN_HALF_INTERVAL_FORM:
    status: SELECTED
    kill_power: 10/10
    proof_cost: 8/10
    object: even_sector_on_0_1_with_Neumann_at_0_and_regular_natural_endpoint_at_1
  R2_FULL_SATZ1_ALL_PARITY:
    status: RUNNER_UP_NOT_AUTHORIZED
    kill_power: 10/10
    proof_cost: 10/10
    object: full_lambda_n_zero_G_branch_with_parity_and_analytic_parameter_curves
  R3_EVEN_LEGENDRE_JACOBI_OPERATOR:
    status: PLAN_B_REPRESENTATION_SHIFT
    kill_power: 8/10
    proof_cost: 8/10
    object: diagonal_Legendre_operator_plus_bounded_tridiagonal_perturbation

MINIMAL_MISSING_IDENTITY:
  NAME: MS_SATZ1_M0_FIXED_G_EVEN_REGULAR_SPECTRUM
  STATEMENT: >-
    For every fixed real G, the set of real Lambda admitting a nonzero even
    solution regular at both endpoints of
    -((1-x^2)f')' - G(1-x^2)f = Lambda f
    is exactly the range of one strictly increasing sequence Nat -> Real.

CLOSES:
  - REQ_R_ARISTOTLE_GOAL_SLICING
  - REQ_R_ACCEPTANCE_POLICY
  - REQ_R_PLAN_B_FORMALIZATION_ORDER
OPENS: []

NEXT_LOAD_BEARING_GAP: MS_SATZ1_M0_FIXED_G_EVEN_REGULAR_SPECTRUM
NEXT_CHEAPEST_DECISIVE_TEST: ARISTOTLE_DEEP_RUN_SOURCE_PURE_EVEN_SPECTRUM

FAILURE_CODES:
  - REQ_R_C04_PROJECT_SOURCE_CATEGORY_MIX
  - REQ_R_C10_SYNTHETIC_ODD_BRANCH_SURROGATE
  - REQ_R_SINGULAR_ENDPOINT_REPLACED_BY_REGULAR_INTERVAL
  - REQ_R_COMPACT_RESOLVENT_ASSUMED_NOT_PROVED
  - REQ_R_EXISTENCE_WITHOUT_EXHAUSTIVENESS
  - REQ_R_FINITE_TRUNCATION_USED_FOR_UNIVERSAL_SPECTRUM
  - REQ_R_LAMBDA_VS_LAMBDA_PLUS_G_SHIFT
  - REQ_R_ARISTOTLE_PARTIAL_ONLY

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: false
ARISTOTLE_AUTHORIZED_NOW: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
SCOPE: ABSTRACT
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
```

## ROUTE MAP

### Direct verdict

Do **not** send the current Lean structure `BookRegularEvenSpectrum` to
Aristotle.

That structure is a valid Q3 adapter, but it is not a pure statement of the book
theorem. It contains the Q3-local predicate
`mode4DLMF3035EvenCharacteristicEquation`, the project cutoff `20`, and the
project split degree. Its full `branch : ℕ → ℝ` is also stronger than the
actual consumers: all characteristic and selected-theta consumers use only
`branch (2*r)`. `[ABSTRACT][LEAN]`

A direct submission would ask Aristotle to solve three different obligations at
once:

```text
Meixner–Schäfke regular-spectrum theorem
+ DLMF continued-fraction membership
+ Q3 cutoff/split adapter.
```

That is the exact C04 failure warned about by the request. A successful-looking
answer could close a local surrogate while leaving the source theorem or the
adapter unproved. **[C04]**

The opposite shortcut is also forbidden: from an even sequence `μ_r`, do not
manufacture unused odd values by inserting midpoints and then claim a source
branch `branch n`. Such a function can satisfy the current fields while its odd
entries are not source eigenvalues. That is a semantic C10 surrogate, even if
Lean accepts it. **[C10]**

### Selected source object

Use the exact fixed-parameter, order-zero, even regular endpoint problem.
For `G, Λ : ℝ`, write

\[
\operatorname{RegEvenEig}_G(\Lambda)
\]

when there exist real functions `f, f₁, f₂` such that:

1. `f` is nonzero and even;
2. `f` is continuous on `[-1,1]`;
3. on `(-1,1)`, `f' = f₁` and `f₁' = f₂` in the `HasDerivAt` sense;
4. on `(-1,1)`,
   \[
   -(1-x^2)f_2(x)+2xf_1(x)+Gx^2f(x)=(\Lambda+G)f(x);
   \]
5. the natural endpoint flux tends to zero:
   \[
   (1-x^2)f_1(x)\to0
   \quad(x\to1^-),
   \qquad
   (1-x^2)f_1(x)\to0
   \quad(x\to-1^+).
   \]

The operator form is exactly

\[
-\frac{d}{dx}\bigl((1-x^2)f'(x)\bigr)
-G(1-x^2)f(x)=\Lambda f(x).
\]

The two displayed equations are algebraically identical. Keeping both in the
prompt is the unit/shift firewall: the project eigenvalue is `Λ`, not `Λ+G`.
`[ABSTRACT][PAPER_PLUS_LEAN_SOURCE_AUDIT]`

The paid target is:

\[
\boxed{
\forall G\in\mathbb R\ \exists\mu_G:\mathbb N\to\mathbb R,
\quad \operatorname{StrictMono}(\mu_G),
\quad \operatorname{range}(\mu_G)
 =\{\Lambda:\operatorname{RegEvenEig}_G(\Lambda)\}.
}
\]

This is the exact source theorem the current consumers need after a local
interface repair. It is a corollary of Meixner–Schäfke §3.22 Satz 1, but it does
not drag the all-`m` theorem, analytic parameter curves, the odd spectrum, DLMF
continued fractions, or Q3 objects into Aristotle. `[ABSTRACT][PAPER]`

### Why the interface must become even-only

The current source interface stores a full branch and then immediately derives

```text
r ↦ branch (2*r)
```

as the strictly increasing sequence consumed downstream. The selected-theta
file uses only degrees `0,2,4`. No current proof consumes an odd branch value.
`[ABSTRACT][LEAN]`

After a successful Aristotle result, the source adapter should therefore expose
something equivalent to:

```lean
structure BookRegularEvenSpectrumEven (G : ℝ) where
  evenBranch : ℕ → ℝ
  evenBranch_strictMono : StrictMono evenBranch
  evenBranch_regular : ∀ r, RegEvenEig G (evenBranch r)
  regular_evenBranch : ∀ Λ, RegEvenEig G Λ → ∃ r, evenBranch r = Λ
```

The DLMF forward field and the project root-to-regular-solution reverse field
remain a **separate adapter**. This is not theorem weakening: it removes odd
source cargo that no consumer uses and prevents fake interpolation.
`[ABSTRACT][CONDITIONAL]`

If the owner forbids this local interface repair, the runner-up is the full
all-parity version of Satz 1. It is source-faithful but substantially more
expensive because it must prove that parity alternates with the global spectral
index. That runner-up is not authorized by this verdict.

### Slicing inside the one paid run

Do not buy four unrelated runs. Use one deep run with ordered, independently
harvestable milestones:

1. **Exact endpoint predicate and Green/Wronskian identity.**  Prove all boundary
   terms for the degenerate coefficient `1-x²`; do not replace the problem by
   `[-1+ε,1-ε]`.
2. **One-dimensionality of a regular even eigenspace.**  This is the cheapest
   source-level lemma and is harvestable even if the spectrum theorem fails.
3. **Self-adjoint lower-bounded even-sector realization with discrete exhaustive
   spectrum.**  This is the load-bearing floor.
4. **Strict enumeration and exact range equality.**  This is the paid success
   gate.

A separate parity task is unnecessary because the target is already the even
sector. An existence-only answer is not enough: the current hole needs the
reverse implication, so exhaustiveness must remain in the same target.

## FORMAL OR INFORMAL INPUT

Use **informal Markdown submitted through `aristotle formalize`**, with an exact
mathematical statement and `import Mathlib` only.

Do not upload the Q3 project directory and do not import any Q3 module. Aristotle
must not see `BookRegularEvenSpectrum`, the continued-fraction predicate, the
cutoff, or the selected theta values. Those belong to the post-proof adapter.

The request correctly notes that Mathlib has no named singular
Sturm–Liouville theorem ready to apply. Do not invent one in the prompt. Give
Aristotle instead:

- the exact differential equation;
- the endpoint/domain predicate;
- the final sequence/range theorem;
- the ordered local milestones;
- the prohibition against assuming compact resolvent or a regular-endpoint
  theorem whose leading coefficient is positive on the closed interval.

Aristotle may discover and use any real theorem from the pinned Mathlib. A
Mathlib lemma is **not** rejected merely because this prompt did not name it.
It is rejected only if it does not exist in the pinned environment, its
hypotheses do not cover the degenerate endpoints, or it silently assumes the
load-bearing conclusion.

## ACCEPTANCE POLICY

### Full acceptance

The output is fully accepted only if all of the following hold:

```text
no sorry / admit;
no new axiom, constant, opaque theorem, or custom project import;
compiles in the pinned Aristotle Mathlib;
#print axioms of the final theorem is exactly the standard triple
  [propext, Classical.choice, Quot.sound];
the coefficient 1-x² is allowed to vanish at ±1;
regularity is imposed at the actual endpoints, not on a trimmed interval;
there is one StrictMono sequence Nat → Real;
its range is exactly all and only regular-even eigenvalues.
```

### Partial acceptance

An output with holes in the final theorem is a draft. Hole-free compiled helper
lemmas from milestones 1 or 2 may be harvested. They do not close the source
supplier.

An existence theorem without exact exhaustiveness, or a finite-dimensional
approximation without a universal finite-to-global bridge, is partial only.

### Reformulation

A valid `negate_state` or counterexample means `REFORMULATE`, not route death.
The first question is whether the regularity predicate omitted or overconstrained
the natural endpoint domain.

### Hard rejection

Reject the output if it does any of the following:

- assumes a generic regular Sturm–Liouville theorem requiring `p>0` on the
  closed interval and substitutes `p=1-x²`;
- replaces the problem by every fixed trimmed interval and never proves the
  endpoint limit;
- assumes compact resolvent, discrete spectrum, simplicity, or exhaustiveness;
- proves only a finite Jacobi matrix theorem;
- introduces a source branch by interpolating odd entries;
- imports Q3 or adds a custom axiom;
- leaves `sorryAx` or any axiom beyond the standard triple.

## REGISTERED PLANTS

The result must survive four cheap semantic controls.

1. At `G=0`, `f(x)=1` is an even regular eigenfunction with `Λ=0`.
2. At `G=0`, `f(x)=x` has `Λ=2` but is odd and must not enter the even spectrum.
3. At `G=0`, `(3x²-1)/2` is even regular with `Λ=6`.
4. The logarithmically singular Legendre second-kind branch is an interior ODE
   solution but must be excluded by endpoint regularity.

The first and third detect the `Λ` versus `Λ+G` shift; the second detects a
parity leak; the fourth detects a trimmed-interval or interior-only surrogate.

## PLAN B — FORMALIZE THE BOOK PROOF

If Aristotle does not close the exhaustive spectrum theorem, do not immediately
split intervals or write a project axiom. Read and formalize the source in this
order.

### Reading order

1. Open §1.5 at its first definition, not at its final theorem. Transcribe the
   exact differential expression, endpoint class, scalar product, and every
   quantifier.
2. Transcribe hypotheses `1.–8.` verbatim into a ledger. Do not infer their
   content from the spheroidal verification on p.235.
3. Follow every lemma used by the §1.5 theorem and classify its role:
   Green identity, boundary form, self-adjointness/closedness, compactness or
   oscillation, reality, simplicity, and exhaustiveness.
4. Read printed pp.234–235 and map each of the eight hypotheses separately to
   the spheroidal coefficients at `m=0`. Record the exact source line for every
   check.
5. Read Satz 1 only after that map is complete. Record the normalization
   `λ_n^0(0)=n(n+1)` and the parity convention.
6. Keep DLMF 30.3.5 outside the book proof. It supplies the separate forward
   characteristic membership. Do not use the finite determinant discussion as
   an iff theorem; the source card already records spurious determinant roots.

The first Plan-B artifact must be a paper ledger, not Lean source:

```text
MS15_HYPOTHESES_1_8_LEDGER

columns:
  hypothesis number;
  verbatim statement;
  printed/PDF page;
  theorem in §1.5 that consumes it;
  spheroidal substitution;
  proof on pp.234–235;
  intended Lean predicate;
  status.
```

### Formalization floors and prices

| Floor | Exact work | Cost |
|---|---|---:|
| `B0_MS15_SOURCE_OBJECT_LOCK` | Definitions, units, endpoint class, hypotheses 1–8 verbatim | 2/10 |
| `B1_MS15_GREEN_BOUNDARY_IDENTITY` | Integration by parts and vanishing singular endpoint bracket | 5/10 |
| `B2_MS15_REAL_SIMPLE_REGULAR_EIGENVALUES` | Reality and Wronskian/simplicity | 5/10 |
| `B3_MS15_DISCRETE_EXHAUSTIVE_SPECTRUM` | Closed/self-adjoint realization plus compactness or the book's equivalent oscillation theorem | 9/10 |
| `B4_MS15_EVEN_SECTOR_ENUMERATION` | Restrict/refine to the even sector and build `StrictMono` range equality | 4/10 after B3 |
| `B5_SPHEROIDAL_HYPOTHESES_1_8_INSTANCE` | Verify the eight source hypotheses for `m=0`, fixed `G` | 4/10 |
| `B6_DLMF_AND_Q3_ADAPTER` | DLMF forward membership plus project root-to-regular-solution reverse bridge | 5/10 |

The dominant wall is B3. The remaining floors should not be allowed to hide it.

### Two Plan-B representations

**R1 — even half-interval form.** Work on `[0,1]`, use the even condition as the
Neumann condition at zero, and retain the natural regular endpoint at one.
This removes parity from the spectral theorem. Kill power `10/10`; cost `8/10`.

**R3 — even Legendre/Jacobi coefficient operator.** Use the diagonal Legendre
operator and the bounded tridiagonal spheroidal perturbation, prove discrete
simple spectrum in coefficient space, then prove the coefficient-to-regular
solution iff. Kill power `8/10`; cost `8/10`. This is the scheduled
representation shift if the endpoint form is the actual blocker.

## FINAL PROPOSAL

Run exactly one paid Aristotle task:

```text
MS_SATZ1_M0_FIXED_G_EVEN_REGULAR_SPECTRUM
```

Use a source-pure Markdown input, `import Mathlib` only, and the exact endpoint
predicate above. Success is strict exhaustive enumeration of the even regular
spectrum. Do not ask Aristotle to inhabit the current Q3 structure.

After a successful result:

```text
pure even spectrum theorem
+ separate DLMF forward-membership port
+ existing project root-to-regular-solution bridge
→ even-only book adapter
→ selected-theta equality.
```

No axiom is authorized at any point.

## STRONGEST ATTACK

A reviewer can object:

> Your selected theorem does not construct the current
> `BookRegularEvenSpectrum`, because that structure contains a full branch and
> a Q3 characteristic predicate.

Correct. That mismatch is the reason for the representation shift, not a hidden
omission. The current structure is stronger and less pure than its consumers.
Proving the unused odd branch or manufacturing it by interpolation would spend
more mathematics or create a C10 surrogate. The post-Aristotle step must repair
the adapter to store the even branch directly.

If that interface repair is disallowed, this verdict's selected task is only a
partial supplier and the full all-parity Satz 1 becomes necessary. No statement
in this verdict claims otherwise.

The second attack is the singular endpoint:

> A standard regular Sturm–Liouville theorem on a compact interval does not
> apply because `1-x²` vanishes at both endpoints.

Correct. This is the predicted load-bearing failure. Any output that evades it
by trimming the interval is rejected. A real proof must control the endpoint
boundary form and prove the discrete exhaustive realization in the singular
class.

## ARISTOTLE DIRECTIVE

Copy the following as the complete Markdown input for the one authorized deep
run.

```markdown
# Fixed-parameter even regular spheroidal spectrum, order m = 0

## Goal

Formalize in Lean 4 with **only** `import Mathlib` the source-pure theorem below.
Do not import Q3 and do not introduce any axiom, constant, opaque theorem,
`sorry`, or `admit`.

For fixed real numbers `G` and `Λ`, call `Λ` a regular-even spheroidal
eigenvalue if there exist real functions `f`, `f1`, and `f2` such that:

1. `f` is not the zero function;
2. `f` is even;
3. `f` is continuous on `Set.Icc (-1) 1`;
4. for every `x ∈ Set.Ioo (-1) 1`,
   `HasDerivAt f (f1 x) x` and `HasDerivAt f1 (f2 x) x`;
5. for every `x ∈ Set.Ioo (-1) 1`,

   `-(1 - x^2) * f2 x + 2*x*f1 x + G*x^2*f x = (Λ + G)*f x`;

6. the natural flux tends to zero at both endpoints:

   `(1-x^2) * f1 x → 0` as `x → 1` from the left, and
   `(1-x^2) * f1 x → 0` as `x → -1` from the right.

The displayed ODE is equivalently

`- d/dx ((1-x^2) f'(x)) - G*(1-x^2)*f(x) = Λ*f(x)`.

Prove:

```lean
∀ G : ℝ, ∃ μ : ℕ → ℝ,
  StrictMono μ ∧
  Set.range μ = {Λ : ℝ | RegularEvenSpheroidalEigenvalue G Λ}
```

You may choose an equivalent Lean definition of
`RegularEvenSpheroidalEigenvalue`, but it must preserve the exact endpoint,
evenness, differentiability, and ODE quantifiers above.

## Ordered milestones

Prove and name intermediate lemmas in this order so that a partial result can be
harvested:

1. the exact Green/Lagrange or Wronskian identity with the degenerate coefficient
   `1-x^2`, including the actual endpoint limits;
2. one-dimensionality of a regular even eigenspace at a fixed eigenvalue;
3. a lower-bounded self-adjoint even-sector realization with discrete exhaustive
   spectrum, or a fully proved equivalent ODE theorem;
4. the final `StrictMono` sequence and exact range equality.

The final theorem is the goal. Milestones 1 and 2 are useful partial results but
do not count as completion.

## Mandatory semantic controls

- At `G = 0`, `f(x)=1` is an even regular eigenfunction with `Λ=0`.
- At `G = 0`, `f(x)=x` has `Λ=2` but is odd and must not enter the even spectrum.
- At `G = 0`, `(3*x^2-1)/2` is even regular with `Λ=6`.
- A logarithmically singular Legendre second-kind solution must be excluded by
  endpoint regularity.

These controls fix the sign, the `Λ` versus `Λ+G` shift, parity, and the endpoint
class.

## Forbidden shortcuts

- Do not replace `[-1,1]` by `[-1+ε,1-ε]` without proving the endpoint limit.
- Do not apply a regular Sturm–Liouville theorem requiring a strictly positive
  leading coefficient on the closed interval.
- Do not assume compact resolvent, discreteness, exhaustiveness, or simplicity.
- Do not replace the theorem by finite matrices, finite Legendre truncations, or
  numerical evidence.
- Do not construct unused odd branch values by interpolation.
- Do not use any project definition or project theorem.

Any Mathlib theorem you use may be discovered during the proof, but it must
exist in the pinned environment and its hypotheses must be instantiated
explicitly for this singular endpoint problem.
```

Submission command after the Linux body materializes the input file:

```bash
WORKDIR: repository root
source .venv/bin/activate
aristotle formalize \
  q3.lean.aristotle/aristotle_input/req_r_ms_satz1_m0_even_spectrum_2026_08_22.md
```

After completion, the Linux body must record the project ID, download the
archive, and run:

```bash
rg -n "sorry|admit|axiom|constant" <extracted-output>
rg -n "exact\\?" <extracted-output> || true
```

Compilation and `#print axioms` are mandatory before any integration.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION.

The next transaction is the owner-authorized Aristotle run above.
Codex must not build a parallel source interface or pre-emptively weaken the
current hole while that run is pending.
```

## META CLOSEOUT

**What became smaller?**

The mixed four-field Q3 hole was separated into one source-pure mathematical
supplier and one later adapter. The paid target is now one exact theorem rather
than “formalize Sturm–Liouville”.

**What was killed?**

- direct submission of `BookRegularEvenSpectrum`;
- full-project context submission;
- a separate parity run;
- existence without exhaustiveness;
- synthetic odd-branch interpolation.

**What must not be tried again?**

Do not ask Aristotle to prove a Q3 adapter and the source theorem in one object.
Do not hide the endpoint degeneracy behind a theorem for a regular interval.

**Current smallest named gap?**

```text
MS_SATZ1_M0_FIXED_G_EVEN_REGULAR_SPECTRUM
```

**Next cheapest decisive test?**

The single source-pure deep Aristotle run with the endpoint and `G=0` plants
precommitted above.

**Fate of prior predictions?**

The prior W13.7 prediction that the first book port failure would be an
interface/provenance shape is supported: the current typed hole mixes the book,
DLMF, and Q3 adapter. The analytic source theorem itself remains open. No
retroactive repair was made.

**Memory entry**

```yaml
iteration: REQ-2026-08-22-R
target: book regular spectrum supplier
status: PROGRESS
failed_strategy: direct project-structure submission
cognitive_operator_used: REPRESENTATION_SHIFT
new_gap_name: MS_SATZ1_M0_FIXED_G_EVEN_REGULAR_SPECTRUM
invariant_learned: source theorem and project adapter must remain separate
forbidden_future_move: synthesize odd source values or trim singular endpoints
next_decisive_test: owner-authorized source-pure Aristotle deep run
```
