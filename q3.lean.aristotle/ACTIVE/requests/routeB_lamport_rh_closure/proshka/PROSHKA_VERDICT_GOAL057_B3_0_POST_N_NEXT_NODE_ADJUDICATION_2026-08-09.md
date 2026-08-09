# STATUS: OPEN — B3.0O SHIFTED ARCHIMEDEAN SQUARE-ROOT WEIGHT PREFLIGHT SELECTED; PRODUCTION FORBIDDEN

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT
OPERATIVE_CLASS_COUNT: 1

BINARY_RULING: SELECTED_FOR_UNTRACKED_PREFLIGHT
PRODUCTION_AUTHORIZED: false
TRACKED_REPOSITORY_MUTATION_AUTHORIZED: false
ROUTE_STATE_MUTATION_AUTHORIZED: false
ARISTOTLE_SUBMISSION_AUTHORIZED: false

TRANSACTION:
  ID: GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT
  MODE: UNTRACKED_EXACT_LEAN_PREFLIGHT
  SAME_LIVING_CHAT: true
  PHASE_KEY_CHANGE: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  CONTROLLING_REQUEST:
    path: PROSHKA_REQUEST_GOAL057_B3_0_POST_N_NEXT_NODE_ADJUDICATION_2026-08-09.txt
    observed_sha256: 6166f58c224bcfd7e3e311918b503276816ed235e4c6aab9900ff7fb603d31ef
    observed_bytes: 9598
    observed_wc_lines: 273
    final_LF: true
    utf8: PASS
    read_byte_for_byte: true

  HEAD:
    expected: 745c00672781a01ce0d0878f95ebe91ca1bbc7e3
    observed_origin_rh_clean: 745c00672781a01ce0d0878f95ebe91ca1bbc7e3
    commit_message: "[MacOS][rh_clean][RouteB] Close Goal 057 B3.0N arch symbol lower bound"
    status: PASS

  STAGED_PATCH:
    expected_sha256: 291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b
    independently_rehashed_by_judge: false
    preflight_recheck_required: true
    preservation_required: true

CURRENT_STATE:
  stage: RB-GOAL-057-B3-0N-CLOSED
  obligation: GOAL057_B3_0_POST_N_NEXT_NODE_ADJUDICATION
  successor_previously_authorized: false
  B3_0M: CLOSED
  B3_0N: CLOSED
  B3_0: OPEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

CANDIDATE_COMPARISON:
  A_SHIFTED_SYMBOL_NONNEGATIVE_PRIMITIVE:
    ruling: KILLED_AS_STANDALONE_PUBLIC_WRAPPER
    reason: B3_0N_already_proves_the_exact_nonnegativity_and_the_expression_can_be_inlined
    mathematical_falsehood_claimed: false

  B_SHIFTED_SQRT_MULTIPLIER_MEASURABLE_PRIMITIVE:
    ruling: SELECTED
    reason:
      - first_new_nonlinear_object_after_B3_0N
      - exact_form_domain_weight
      - totalized_Real_sqrt_requires_the_B3_0N_sign_certificate
      - fixes_form_domain_vs_operator_domain_category_before_any_domain_definition

  C_SHIFTED_ARCH_MULTIPLIER_FORM_DOMAIN_PRIMITIVE:
    ruling: RETAINED_AS_EXACT_NEXT_GAP
    dependency: B3_0O
    authorized_now: false

  D_FINITE_MODE_SPAN_IN_SHIFTED_DOMAIN:
    ruling: RETAINED_AFTER_C
    dependency:
      - B3_0O
      - B3_0P_domain
      - scalar_sqrt_shift_domination
    authorized_now: false

  E_BOUNDED_WHOLE_SPACE_W02_EXTENSION:
    ruling: NOT_SELECTED
    reason: independent_larger_ambient_source_construction

  F_BOUNDED_WHOLE_SPACE_PRIME_EXTENSION:
    ruling: NOT_SELECTED
    reason: independent_larger_ambient_source_construction

  G_CLOSED_SHIFTED_ARCH_FORM:
    ruling: KILLED_AS_CURRENT_OVERBUNDLE
    reason: bundles_weight_domain_density_and_closedness_before_the_weight_primitive_is_checked

SELECTED_CHILD:
  ID: GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT
  SCRATCH_PATH:
    q3.lean.aristotle/Goal057B3_0O_ShiftedSqrtMultiplier_Scratch.lean
  FUTURE_PRODUCTION_PATH_NOT_AUTHORIZED:
    q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchSqrtWeight.lean

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarExactArchSymbolLowerBound
  - Q3.Proofs.A_Star_Properties

NAMESPACE:
  Q3.RouteB.D0Pstar

CANDIDATE:
  filename: GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_CANDIDATE_2026-08-09.lean
  sha256: b1641e36554b66131bb04b14b606b94557a8f004a686fad73b51378e72360bba
  bytes: 2116
  wc_lines: 59
  final_LF: true
  forbidden_token_matches: 0
  judge_reran_Lean: false
  status: EXACT_BYTES_PINNED_REQUIRES_DIRECT_LEAN

PUBLIC_SURFACE_CEILING:
  definitions:
    - sourceArchimedeanShiftedSqrtWeight
  theorems:
    - sourceArchimedeanShiftedSqrtWeight_continuous
    - sourceArchimedeanShiftedSqrtWeight_measurable
    - sourceArchimedeanShiftedSqrtWeight_nonneg
    - sourceArchimedeanShiftedSqrtWeight_sq
  total_public_declarations: 5

PRIVATE_SURFACE_CEILING:
  definitions: 0
  theorems:
    - sourceArchimedeanMultiplier_continuous_for_shiftedSqrt
  total_private_declarations: 1

SEMANTIC_CONTRACT:
  exact_weight: sqrt(sourceArchimedeanMultiplier_plus_B3_0N_shift)
  shift:
    abs_log_pi_plus_log_4_plus_6
  global_quantifier: forall_real_t
  exact_square_identity: true
  exact_continuity: true
  exact_measurability: true
  exact_nonnegativity: true

  form_domain_defined: false
  operator_domain_defined: false
  equality_with_D0_2_claimed: false
  ambient_source_form_defined: false
  associated_operator_defined: false
  W02_ambient_extension_defined: false
  Prime_ambient_extension_defined: false

PREFLIGHT_STOP:
  GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_FAILED

PREFLIGHT_SUCCESS:
  GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_PROVED

NEXT_GAP_NOT_AUTHORIZED:
  GOAL057_B3_0P_SHIFTED_ARCH_MULTIPLIER_FORM_DOMAIN_PRIMITIVE

CHECKPOINT_EFFECT:
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  effect_after_preflight_success: STRICTLY_ADVANCED_NOT_CLOSED
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL_UNTIL_EXACT_LEAN_PREFLIGHT
PROGRESS_CLASS: REPRESENTATION_PROGRESS
CHILD_PROGRESS_IF_PROVED: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

FINAL_BOUNDARY:
  ROUTE: CHALLENGER_NOT_RH
  ACTIVE_BUS_GOAL: 057
  BUS_010: VOID
  GOAL_055: HOLD
  G2_CCM: FROZEN
  H4A1B: OPEN
  ARISTOTLE_SUBMISSION: NONE
  ROUTE_PROMOTION: false
  PX_RH_CLAIM: NOT_MADE
  SOLE_OWNER_GATE: PX_RH_CLAIM
```

## 1. Source-lock ruling

The controlling request was read byte-for-byte. Its observed lock is SHA-256 `6166f58c…d31ef`, 9,598 bytes, 273 `wc` lines, valid UTF-8, with a final LF. It fixes B3.0N as closed, B3.0 as open, the current checkpoint as advanced but not closed, and expressly forbids production authorization in this verdict.  `[ABSTRACT][PAPER]`

The live `rh_clean` branch points exactly to `745c00672781a01ce0d0878f95ebe91ca1bbc7e3`, whose commit message is the B3.0N lower-bound closeout.  `[ABSTRACT][PAPER]`

The physical execution state independently records:

```text
RB-GOAL-057-B3-0N-CLOSED
GOAL057_B3_0_POST_N_NEXT_NODE_ADJUDICATION
OPEN_ADJUDICATION_REQUIRED_NO_SUCCESSOR_AUTHORIZED
```

and preserves the coarse ledger at `0 closed / 10 remaining`.  `[ABSTRACT][PAPER]`

## 2. Operative ruling

[
\boxed{
\texttt{TRY_GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT}
}
]

Candidate **B** is the smallest lawful successor.

Candidate A is not false, but as an independent public transaction it would mostly rename the expression already controlled by B3.0N. The exact shift can be inlined into the square-root weight. Its continuity follows from the already-proved normalization through `a_star`; its nonnegativity is exactly B3.0N. A standalone A file would add a public alias without changing the next proof category. `[ABSTRACT][LEAN]`

Candidate B introduces a genuinely new object:

[
w_{\mathrm{arch}}(t)
====================

\sqrt{
m_{\mathrm{arch}}(t)
+
\bigl(|\log\pi|+\log4+6\bigr)
}.
]

This is not merely another name for B3.0N. The square root is the exact weight needed by the **form domain**, and Lean’s real square root is totalized on negative arguments. Consequently, the exact identity

[
w_{\mathrm{arch}}(t)^2
======================

m_{\mathrm{arch}}(t)
+
\bigl(|\log\pi|+\log4+6\bigr)
]

is available only because B3.0N proves that the argument is nonnegative globally. That makes the B3.0N dependency falsifiable and load-bearing. Mathlib’s pinned real-square-root API explicitly distinguishes `sq_sqrt`, which requires nonnegativity, from the totalized identity involving `max x 0`.   `[ABSTRACT][LEAN]`

## 3. Mandatory questions

### 3.1 Is Candidate A a real dependency?

**Not as a standalone public child.**

B3.0N already proves the only nontrivial signed fact:

[
0\le
m_{\mathrm{arch}}(t)
+
\bigl(|\log\pi|+\log4+6\bigr)
\quad\forall t\in\mathbb R.
]

`[ABSTRACT][LEAN]`

Continuity of the unshifted multiplier is reconstructed directly from

[
m_{\mathrm{arch}}(t)=-\frac{a_\star(t)}{2\pi}
]

and the production theorem `Q3.a_star_continuous_thm`.  `[ABSTRACT][LEAN]`

A separate shifted-symbol alias would therefore be public scaffolding. The selected B child keeps the exact expression visible inside the first object that changes the mathematics: its square-root form weight. **[C10]**

### 3.2 What should carry the later multiplication domain?

The smallest correct carrier is:

```lean
Submodule ℂ (H_m i)
```

whose membership predicate is a `MemLp` statement:

```lean
x ∈ shiftedArchFormDomain i
↔
MemLp
  (fun t =>
    (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
      ((sourceLogWindowFourierL2Isometry i x :
          Lp ℂ 2 volume) : ℝ → ℂ) t)
  2 volume
```

`[ABSTRACT][CONDITIONAL]`

The distinctions are:

* a raw `Set` does not package the linear closure required of a form domain;
* `MemLp` is the correct predicate inside the carrier, not the outer mathematical object;
* a `Submodule` records the correct complex-linear category;
* an unbounded multiplication-operator domain is a later, stronger object.

Pinned Mathlib supplies the required closure primitives, including `MemLp.zero`, `MemLp.add`, scalar multiplication, and a.e.-equality transport. The project is pinned to Mathlib v4.26.0.   `[ABSTRACT][LEAN]`

Candidate C is therefore lawful after B, but it is not selected in this transaction.

### 3.3 Square-root weight or full shifted symbol?

The **form domain** uses

[
\boxed{
\sqrt{m_{\mathrm{arch}}+C},\Phi_i x\in L^2.
}
]

The later **multiplication-operator domain** uses

[
\boxed{
(m_{\mathrm{arch}}+C),\Phi_i x\in L^2.
}
]

These domains are generally different.

For the diagonal operator (Ae_n=n e_n) on (\ell^2(\mathbb N)), the form domain is

[
\sum_n n|x_n|^2<\infty,
]

whereas the operator domain is

[
\sum_n n^2|x_n|^2<\infty.
]

For (x_n=(n+1)^{-3/2}), the first sum converges and the second diverges. Thus form-domain membership cannot be promoted to operator-domain membership. `[ABSTRACT][PAPER]`

This is an exact C04 category boundary. D0.2 separately types the source object as a lower-semibounded form with a generally proper dense form domain, while D0.3 requires an additional representing-vector condition before the associated operator may be applied.   `[ABSTRACT][PAPER]`

### 3.4 Does fixed-mode weighted (L^2) immediately put (E_{m,N}) in the form domain?

**It makes the result inexpensive after Candidate C, but one scalar bridge is still required.**

B3.0B3 proves, for each literal mode,

[
m_{\mathrm{arch}}\widehat V_n\in L^2.
]

`[ABSTRACT][LEAN]`

B3.0L supplies the unweighted whole-line (L^2) image of every mode and an isometry on all of (H_m), while its pointwise Fourier identification remains restricted to literal basis modes.  `[ABSTRACT][LEAN]`

Writing (s=m_{\mathrm{arch}}+C\ge0), one has the elementary pointwise estimate

[
\sqrt{s}\le s+1\le |m_{\mathrm{arch}}|+C+1.
]

Hence

[
|\sqrt{s},\widehat V_n|
\le
|m_{\mathrm{arch}}\widehat V_n|
+
(C+1)|\widehat V_n|.
]

The two right-hand terms are in (L^2); `MemLp.add` and scalar closure then give form-domain membership for each mode, and finite-sum closure gives the whole (E_{m,N}). This should be a separate D child because it consumes the domain and proves a new quantifier statement. `[FINITE_CELL][CONDITIONAL]`

It does **not** imply that every (x\in H_m) lies in the form domain. An unbounded weight can contain every basis vector in its domain while excluding some infinite (L^2) combinations.

### 3.5 Which child first makes closedness materially easier?

Candidate **B**.

Closedness of the shifted multiplication form is governed by the multiplication operator

[
M_{w_{\mathrm{arch}}},\qquad
w_{\mathrm{arch}}=\sqrt{m_{\mathrm{arch}}+C}.
]

Candidate B fixes this weight, its continuity, its measurability, its nonnegativity, and its exact square. Candidate A merely gives the radicand another name. Candidate C then packages the pullback domain through B3.0L. `[ABSTRACT][CONDITIONAL]`

### 3.6 When should equality with D0.2 be proved?

**After** constructing the canonical multiplier form and proving its analytic properties.

The lawful order is:

```text
exact shifted square-root weight;
weighted-L2 form domain;
shifted multiplication form;
density and closedness;
bounded W02 and Prime perturbations;
exact agreement with the source form on the source core;
closure/uniqueness argument identifying the constructed form with D0.2.
```

D0.2 is the source-locked target specification. It must guide signs, domains, and the finite-core equality, but it must not be accepted as a premise asserting that a convenient newly defined weighted domain is already the source domain.  `[ABSTRACT][PAPER]`

### 3.7 Four decisive falsifiers

**Form-domain/operator-domain collapse.** Use the diagonal (\ell^2) example above. Any theorem identifying the square-root domain with the full-multiplier domain must fail with:

```text
B3_0_FORM_DOMAIN_OPERATOR_DOMAIN_COLLAPSE
```

`[ABSTRACT][PAPER]`

**Arbitrary-vector quantifier drift.** In (\ell^2), every basis vector (e_n) belongs to the form domain of the weight (n), but the vector (x_n=1/n) lies in (\ell^2) and fails

[
\sum_n n|x_n|^2<\infty.
]

Therefore fixed-mode membership does not imply all-(H_m) membership. Required stop:

```text
B3_0_ARBITRARY_VECTOR_WEIGHTED_DOMAIN_OVERCLAIM
```

`[ABSTRACT][PAPER]`

**Premise surrogate.** Adding

```lean
hshift : ∀ t, 0 ≤ sourceArchimedeanMultiplier t + C
```

and proving the square identity from `hshift`, rather than consuming B3.0N, must fail with:

```text
SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION
```

**[C10]**

**Finite Riesz substituted for ambient multiplication.** Let

[
A=
\begin{pmatrix}
0&1\
1&0
\end{pmatrix},
\qquad
E=\operatorname{span}(e_1).
]

The compressed form on (E) has zero finite Riesz operator, while (Ae_1=e_2\notin E). Thus a finite Riesz lift cannot define the ambient source multiplier or associated operator. D0.3 records this same nonconflation rule.  `[FINITE_CELL][PAPER]`

## 4. Candidate comparison

| Candidate                          | Kill power |                             Cost | Actual wall reduction                                                      | Ruling                                    |
| ---------------------------------- | ---------: | -------------------------------: | -------------------------------------------------------------------------- | ----------------------------------------- |
| **A — shifted symbol alias**       |        1/5 |                              Low | Adds continuity/measurability packaging, but no new mathematical carrier   | **Kill as standalone public scaffolding** |
| **B — shifted square-root weight** |    **5/5** | Low; exact compile cost unproved | Fixes the canonical form weight and tests totalized-square-root truncation | **Selected**                              |
| **C — form-domain submodule**      |        5/5 |        Medium; API cost unproved | First domain object, but logically consumes B                              | Retain as B3.0P                           |
| **D — finite mode span in domain** |        4/5 |      Medium; proof cost unproved | Supplies source core membership after C                                    | Retain after C                            |
| **E — ambient W02 extension**      |        3/5 |             Medium–high, unknown | Closes one bounded perturbation                                            | Not selected                              |
| **F — ambient Prime extension**    |        4/5 |                    High, unknown | Closes the arithmetic bounded perturbation                                 | Not selected                              |
| **G — closed shifted form bundle** |        5/5 |                    High, unknown | Would combine several independent walls                                    | Kill as current overbundle                |

`[ABSTRACT][CONDITIONAL]`

## 5. Exact scratch candidate

Exact lock:

```text
SHA-256:
  b1641e36554b66131bb04b14b606b94557a8f004a686fad73b51378e72360bba

bytes:
  2116

wc-lines:
  59

final LF:
  true
```

[Byte-exact B3.0O scratch candidate](sandbox:/mnt/data/GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_CANDIDATE_2026-08-09.lean)

```lean
import Q3.Proofs.RouteB.D0PstarExactArchSymbolLowerBound
import Q3.Proofs.A_Star_Properties

noncomputable section

open scoped Real

namespace Q3.RouteB.D0Pstar

private theorem sourceArchimedeanMultiplier_continuous_for_shiftedSqrt :
    Continuous sourceArchimedeanMultiplier := by
  have hrepr :
      sourceArchimedeanMultiplier =
        fun t : ℝ => -Q3.a_star t / (2 * Real.pi) := by
    funext t
    exact sourceArchimedeanMultiplier_eq_neg_aStar_scaled t
  rw [hrepr]
  exact Q3.a_star_continuous_thm.neg.div_const (2 * Real.pi)

/-- The nonnegative square-root weight attached to the exact finite shift of
B3.0N.  This is form-domain data only; it is not an ambient source form or an
associated operator. -/
noncomputable def sourceArchimedeanShiftedSqrtWeight (t : ℝ) : ℝ :=
  Real.sqrt
    (sourceArchimedeanMultiplier t +
      (|Real.log Real.pi| + Real.log 4 + 6))

theorem sourceArchimedeanShiftedSqrtWeight_continuous :
    Continuous sourceArchimedeanShiftedSqrtWeight := by
  simpa [sourceArchimedeanShiftedSqrtWeight] using
    Real.continuous_sqrt.comp
      (sourceArchimedeanMultiplier_continuous_for_shiftedSqrt.add
        continuous_const)

theorem sourceArchimedeanShiftedSqrtWeight_measurable :
    Measurable sourceArchimedeanShiftedSqrtWeight :=
  sourceArchimedeanShiftedSqrtWeight_continuous.measurable

theorem sourceArchimedeanShiftedSqrtWeight_nonneg
    (t : ℝ) :
    0 ≤ sourceArchimedeanShiftedSqrtWeight t := by
  exact Real.sqrt_nonneg _

theorem sourceArchimedeanShiftedSqrtWeight_sq
    (t : ℝ) :
    sourceArchimedeanShiftedSqrtWeight t ^ 2 =
      sourceArchimedeanMultiplier t +
        (|Real.log Real.pi| + Real.log 4 + 6) := by
  unfold sourceArchimedeanShiftedSqrtWeight
  exact Real.sq_sqrt
    (sourceArchimedeanMultiplier_add_explicitShift_nonneg t)

#print axioms sourceArchimedeanShiftedSqrtWeight
#print axioms sourceArchimedeanShiftedSqrtWeight_continuous
#print axioms sourceArchimedeanShiftedSqrtWeight_measurable
#print axioms sourceArchimedeanShiftedSqrtWeight_nonneg
#print axioms sourceArchimedeanShiftedSqrtWeight_sq

end Q3.RouteB.D0Pstar
```

The candidate reuses the exact continuity route already employed in B3.0B3 and the exact B3.0N lower-bound theorem.   `[ABSTRACT][LEAN]`

I did not run the pinned Lean toolchain in this environment. The bytes are source- and API-audited, but they are preflight input rather than proof evidence.

## 6. Mandatory judges

| ID                                     | Mutation or attack                                                                                           | Required stop                                  |
| -------------------------------------- | ------------------------------------------------------------------------------------------------------------ | ---------------------------------------------- |
| `P057_B3_0O_1_EXACT_SHIFT`             | Change `6`, remove `log 4`, or alter `abs(log π)`                                                            | `B3_0O_EXACT_SHIFT_MISMATCH`                   |
| `P057_B3_0O_2_TOTALIZED_SQRT`          | Replace `Real.sq_sqrt hnonneg` by the unconditional `sq_sqrt'`, thereby proving equality to `max radicand 0` | `B3_0O_TOTALIZED_SQRT_TRUNCATION`              |
| `P057_B3_0O_3_ASTAR_SIGN`              | Change `-a_star/(2π)` to `+a_star/(2π)` in the continuity crosswalk                                          | `B3_0O_ASTAR_SIGN_ORIENTATION_MISMATCH`        |
| `P057_B3_0O_4_FORM_VS_OPERATOR_WEIGHT` | Replace the square-root weight by the full shifted symbol                                                    | `B3_0O_FORM_OPERATOR_WEIGHT_COLLAPSE`          |
| `P057_B3_0O_5_ABS_SURROGATE`           | Replace the radicand by `abs sourceArchimedeanMultiplier` or another always-positive surrogate               | `B3_0O_ABS_OR_MAX_SURROGATE`                   |
| `P057_B3_0O_6_GLOBAL_QUANTIFIER`       | Restrict the object to sampled frequencies, modes, or one finite block                                       | `B3_0O_GLOBAL_QUANTIFIER_LOST`                 |
| `P057_B3_0O_7_PREMISE_SURROGATE`       | Assume the desired radicand nonnegativity instead of consuming B3.0N                                         | `SURROGATE_BY_PREMISE_NOT_SOURCE_CONSTRUCTION` |
| `P057_B3_0O_8_DEPENDENCY`              | Add generated PSD, Step33, hbox, payload, PrimeCert, or Aristotle-output support                             | `ROUTEB_GENERATED_PSD_DEPENDENCY_LEAK`         |
| `P057_B3_0O_9_SCOPE`                   | Add a domain, form, graph, operator, compression, numerator, or checkpoint claim                             | `B3_0O_SCOPE_SMUGGLE`                          |

The cheap independent control for P2 is the negative scalar input (x=-1):

[
\operatorname{sqrt}(-1)^2=0\ne-1.
]

Thus a totalized square root cannot establish the exact square identity without the B3.0N nonnegativity theorem. `[ABSTRACT][LEAN]`

## 7. Exact preflight validation

Required source gate:

```bash
test "$(git rev-parse HEAD)" = \
  "745c00672781a01ce0d0878f95ebe91ca1bbc7e3"

test "$(git rev-parse origin/rh_clean)" = \
  "745c00672781a01ce0d0878f95ebe91ca1bbc7e3"

test "$(git diff --cached | sha256sum | cut -d' ' -f1)" = \
  "291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b"
```

Create only the untracked scratch file:

```text
q3.lean.aristotle/Goal057B3_0O_ShiftedSqrtMultiplier_Scratch.lean
```

Require:

```bash
sha256sum \
  q3.lean.aristotle/Goal057B3_0O_ShiftedSqrtMultiplier_Scratch.lean

wc -c -l \
  q3.lean.aristotle/Goal057B3_0O_ShiftedSqrtMultiplier_Scratch.lean

rg -n \
  'sorry|exact\?|admit|unsafe|native_decide|opaque|axiom |Float' \
  q3.lean.aristotle/Goal057B3_0O_ShiftedSqrtMultiplier_Scratch.lean

cd q3.lean.aristotle

lake env lean \
  Goal057B3_0O_ShiftedSqrtMultiplier_Scratch.lean
```

Required result:

```yaml
candidate_sha256:
  b1641e36554b66131bb04b14b606b94557a8f004a686fad73b51378e72360bba
bytes: 2116
wc_lines: 59
final_LF: true

direct_Lean_exit: 0

imports:
  exact_count: 2

public_surface:
  definitions: 1
  theorems: 4

private_surface:
  definitions: 0
  theorems: 1

forbidden_tokens: 0

axiom_gate:
  sourceArchimedeanShiftedSqrtWeight_sq:
    exactly:
      - propext
      - Classical.choice
      - Quot.sound
  every_other_public_declaration:
    no_axiom_outside_standard_triple: true
```

Run all nine judges in temporary copies, delete every mutant, then require:

```text
routeb_status.py --check: PASS
git diff --check: PASS
tracked repository mutation: NONE
route state mutation: NONE
unrelated staged patch SHA: UNCHANGED
exact git status: REPORTED
```

### Binary preflight outcomes

```text
PASS:
  GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_PROVED
```

Return the exact scratch bytes, direct Lean output, axiom report, dependency fingerprint, and all nine plant fates to this same chat for a separate production-release adjudication.

```text
FAIL:
  GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_FAILED
```

Return the first exact Lean/API defect. Do not weaken the square identity to `max radicand 0`, introduce an assumed sign premise, or jump directly to a domain declaration.

## 8. Exact semantic boundary after preflight success

A successful B3.0O preflight proves only:

[
\boxed{
w_{\mathrm{arch}}(t)
====================

\sqrt{
m_{\mathrm{arch}}(t)
+
\bigl(|\log\pi|+\log4+6\bigr)
}
}
]

is continuous, measurable, nonnegative, and satisfies

[
\boxed{
w_{\mathrm{arch}}(t)^2
======================

m_{\mathrm{arch}}(t)
+
\bigl(|\log\pi|+\log4+6\bigr)
}
]

for every real (t). `[ABSTRACT][LEAN]`

It does not prove:

* a weighted-(L^2) form domain;
* linear closure of that domain;
* density;
* a closed or lower-semicontinuous form;
* equality with D0.2;
* bounded W02 or Prime extensions;
* an associated graph or operator;
* operator-domain membership;
* compression;
* the continuum numerator;
* H4a1b;
* a coarse checkpoint.

The exact next gap is:

```text
GOAL057_B3_0P_SHIFTED_ARCH_MULTIPLIER_FORM_DOMAIN_PRIMITIVE
```

It is named but not authorized.

## 9. Strongest attack

> B3.0O still does not create a form domain. Why is it not another decorative wrapper?

The objection is correct about scope: B3.0O does not create the domain.

It survives because it introduces the exact nonlinear coefficient that distinguishes the form domain from the operator domain. Its square theorem is not definitional under Lean’s totalized square root; it depends on the global B3.0N sign theorem. A wrong sign, absolute-value surrogate, sampled-domain theorem, or full-symbol substitution is independently detectable.

Candidate A lacks that property. Candidate C would be the first domain object, but exposing it before the square-root weight’s exact global square contract has compiled would bundle two category decisions into one transaction.

## 10. Meta closeout

**What became smaller?**

The ambient-form wall is reduced from “construct a shifted domain” to one first representation object: the exact globally measurable square-root weight.

**What was killed?**

* a standalone shifted-symbol alias;
* direct form-domain mint before the square-root contract;
* full shifted multiplier as the form-domain weight;
* totalized `sqrt` truncation hidden behind `max`;
* a bundled closed-form transaction.

**What must not be tried again?**

Do not use the full shifted symbol for the form domain. Do not infer all-(H_m) membership from modewise membership. Do not call the future weighted submodule D0.2 before an equality theorem.

**Current smallest named gap**

```text
GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_FAILED
```

until the exact candidate compiles; after a green preflight:

```text
GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PRODUCTION_MISSING
```

until a separate production release.

**Next cheapest decisive test**

Compile the exact 2,116-byte candidate and run the totalized-square-root, sign, shift, and category plants.

**Prediction ledger**

```text
Prior provisional prediction:
  the immediate post-B3.0N node would be the shifted form-domain primitive.

Fate:
  REFINED_BEFORE_TEST.
  No form-domain child had been selected or executed.
  The exact audit found a strictly smaller load-bearing square-root-weight
  primitive.

Registered prediction:
  the exact 2,116-byte B3.0O candidate compiles under the pinned toolchain,
  and its square theorem has exactly the standard axiom triple.

Status:
  REGISTERED_NOT_YET_TESTED.
```

```yaml
iteration:
  target: GOAL057_B3_0_POST_N_NEXT_NODE_ADJUDICATION
  status: PROGRESS
  failed_strategy: mint_the_weighted_domain_before_locking_the_totalized_sqrt_contract
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_FAILED
  invariant_learned: form_domain_uses_sqrt_shift_operator_domain_uses_full_shift_and_the_exact_square_requires_global_nonnegativity
  forbidden_future_move: identify_form_and_operator_domains_or_replace_the_shifted_symbol_by_abs_or_max
  next_decisive_test: exact_B3_0O_untracked_Lean_preflight
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
OPERATIVE_CLASS:
  TRY_GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT

MODE:
  UNTRACKED_EXACT_LEAN_PREFLIGHT
  PRODUCTION_AUTHORIZED: false
  TRACKED_REPOSITORY_MUTATION: false
  NO_PRODUCTION_AUTHORIZATION_IN_THIS_VERDICT: true

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 745c00672781a01ce0d0878f95ebe91ca1bbc7e3
  require_origin_equal: true

  controlling_request_sha256:
    6166f58c224bcfd7e3e311918b503276816ed235e4c6aab9900ff7fb603d31ef
  controlling_request_bytes: 9598
  controlling_request_wc_lines: 273
  controlling_request_final_LF: true

  preserve_staged_patch_sha256:
    291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

CREATE_UNTRACKED_ONLY:
  - q3.lean.aristotle/Goal057B3_0O_ShiftedSqrtMultiplier_Scratch.lean

DO_NOT_CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarShiftedArchSqrtWeight.lean

EXACT_CANDIDATE:
  source_artifact:
    GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_CANDIDATE_2026-08-09.lean
  method: BYTE_FOR_BYTE_COPY
  sha256: b1641e36554b66131bb04b14b606b94557a8f004a686fad73b51378e72360bba
  bytes: 2116
  wc_lines: 59
  final_LF: true
  any_byte_change: STOP_AND_RETURN_CORRECTED_CANDIDATE

EXACT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarExactArchSymbolLowerBound
  - Q3.Proofs.A_Star_Properties

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE_EXACT:
  definitions:
    - sourceArchimedeanShiftedSqrtWeight
  theorems:
    - sourceArchimedeanShiftedSqrtWeight_continuous
    - sourceArchimedeanShiftedSqrtWeight_measurable
    - sourceArchimedeanShiftedSqrtWeight_nonneg
    - sourceArchimedeanShiftedSqrtWeight_sq
  total: 5

PRIVATE_SURFACE_EXACT:
  definitions: []
  theorems:
    - sourceArchimedeanMultiplier_continuous_for_shiftedSqrt
  total: 1

MANDATORY_SEMANTICS:
  - exact_sourceArchimedeanMultiplier
  - exact_B3_0N_shift_abs_log_pi_plus_log_4_plus_6
  - exact_Real_sqrt_weight
  - exact_global_forall_real_t_quantifier
  - exact_continuity
  - exact_measurability
  - exact_nonnegativity
  - exact_square_identity
  - direct_B3_0N_nonnegativity_consumption
  - exact_minus_aStar_div_two_pi_continuity_crosswalk
  - no_form_domain
  - no_operator_domain
  - no_D0_2_equality
  - no_ambient_form_graph_operator_compression_or_numerator_claim

MANDATORY_JUDGES:
  - P057_B3_0O_1_EXACT_SHIFT
  - P057_B3_0O_2_TOTALIZED_SQRT
  - P057_B3_0O_3_ASTAR_SIGN
  - P057_B3_0O_4_FORM_VS_OPERATOR_WEIGHT
  - P057_B3_0O_5_ABS_SURROGATE
  - P057_B3_0O_6_GLOBAL_QUANTIFIER
  - P057_B3_0O_7_PREMISE_SURROGATE
  - P057_B3_0O_8_DEPENDENCY
  - P057_B3_0O_9_SCOPE

INDEPENDENT_CONTROLS:
  - negative_radicand_totalized_sqrt_control
  - exact_B3_0N_theorem_dependency_fingerprint
  - exact_aStar_sign_orientation_fingerprint
  - constant_shift_contains_no_t_i_m_or_N
  - exact_square_theorem_type_fingerprint

VALIDATION:
  - verify_HEAD_equals_origin_rh_clean
  - verify_staged_patch_SHA256_unchanged
  - verify_exact_scratch_SHA256_bytes_wc_lines_and_final_LF
  - forbidden_token_scan
  - direct_lake_env_lean_on_scratch
  - exact_two_import_audit
  - exact_public_surface_1_definition_4_theorems
  - exact_private_surface_0_definitions_1_theorem
  - print_axioms_for_all_public_declarations
  - require_sourceArchimedeanShiftedSqrtWeight_sq_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - require_no_other_public_axiom_outside_standard_triple
  - run_all_nine_judges_in_temporary_copies
  - remove_all_mutation_artifacts
  - routeb_status_check
  - git_diff_check
  - exact_git_status_report
  - prove_no_tracked_repository_mutation
  - preserve_same_living_chat

PREFLIGHT_STOP:
  GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_FAILED

PREFLIGHT_SUCCESS:
  GOAL057_B3_0O_SHIFTED_ARCH_SQRT_WEIGHT_PREFLIGHT_PROVED

NEXT_GAP_NOT_AUTHORIZED:
  GOAL057_B3_0P_SHIFTED_ARCH_MULTIPLIER_FORM_DOMAIN_PRIMITIVE

NOT_AUTHORIZED:
  - create_the_B3_0O_production_file
  - select_or_authorize_B3_0P
  - define_the_shifted_form_domain
  - define_sourceWeilSesquilinearForm
  - define_SourceWeilFormDomain
  - define_SourceWeilAssociatedGraph
  - define_SourceWeilOperatorDomain
  - define_sourceWeilAssociatedOperator
  - use_the_full_shift_as_the_form_domain_weight
  - infer_all_H_m_weighted_membership_from_modewise_results
  - call_any_convenient_domain_D0_2
  - construct_whole_space_W02_or_Prime_extensions
  - substitute_sourceCCMFiniteRieszOperator_for_an_ambient_operator
  - assert_selected_kTrial_operator_domain_membership
  - assert_compression_or_invariance
  - claim_continuum_numerator
  - invoke_or_close_H4A1B
  - decrement_the_ten_checkpoint_ledger
  - touch_frozen_parent_extract_schedules
  - create_Bus_010
  - release_Goal_055
  - unfreeze_G2_CCM
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_fresh_chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  active_bus_goal: 057
  bus_010: VOID
  goal_055: HOLD
  g2_ccm: FROZEN
  current_checkpoint: ACTUAL_TRIAL_NUMERATOR_SOURCE_TARGET_BRIDGE
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10
  H4a1b: OPEN
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```

