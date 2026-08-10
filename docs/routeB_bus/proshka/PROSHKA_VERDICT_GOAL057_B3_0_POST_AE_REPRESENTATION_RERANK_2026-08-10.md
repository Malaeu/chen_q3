# STATUS: OPEN — FORM-LEVEL ODD SOURCE-WEIL PULLBACK SELECTED; ASSOCIATED OPERATOR DEFERRED

```yaml
STATUS: OPEN

PRIMARY: TRY_GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PREFLIGHT
PRIMARY_COUNT: 1
OPERATIVE_CLASS: TRY_GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PREFLIGHT
OPERATIVE_CLASS_COUNT: 1

B3_0AE_CLASSIFICATION:
  LEAN_PROVED_EXPLICIT_LOWER_SEMICONTINUOUS_NONNEGATIVE_SHIFTED_EXTENDED_ENERGY_PLUS_EXACT_HERMITIAN_FORM_AND_FINITE_CCM_RESTRICTION_NOT_KATO_STRUCTURE_NOT_ASSOCIATED_OPERATOR

FORM_LOCK_FOR_GLOWER:
  status: SUFFICIENT_FOR_FORM_LEVEL_PULLBACK_AND_LOWER_BOUND_PROGRAM
  associated_operator_required: false
  separate_form_core_or_direct_tail_domain_supplier_required: true

ODD_COMPRESSION_NEEDS_ASSOCIATED_OPERATOR: false
ODD_COMPRESSION_MEANING: FORM_PULLBACK_NOT_OPERATOR_COMPRESSION
ODD_INF_SPEC_WORDING_NEEDS_ASSOCIATED_OPERATOR: true

SMALLEST_NEXT_LEAN_CHILD: sourceWeilOddFormPullback13
EXECUTION_AUTHORIZED_INSIDE_THIS_REVIEW: false
LEAN_EDIT_AUTHORIZED_INSIDE_THIS_REVIEW: false
REPO_WRITE_AUTHORIZED_INSIDE_THIS_REVIEW: false
ARISTOTLE_SUBMISSION: NONE

SOURCE_LOCK:
  controlling_attachment:
    sha256: 22fe052a67c3d93630e9e5423f6f843c327dc3d8337b0e826d2a7f72184fa753
    bytes: 73949
    wc_lines: 2349
    final_LF: true
    utf8: PASS
    read_in_full: true
  local_HEAD_from_attachment:
    574c58a6eb47d9b8b847b72ce0d33c2e93150356
  local_HEAD_remote_visibility: UNPUSHED_LOCAL_AHEAD_STATE
  authority_for_B3_0AD_AE: ATTACHED_BYTES

SELECTED_ROUTE:
  candidate: A_FORM_LEVEL_ODD_RESTRICTION_FIRST
  result: SELECTED
  reason:
    GLOWER_consumes_a_quadratic_form_lower_bound_not_an_H_m_valued_operator_residual

REJECTED_AS_CURRENT_NEXT_ACTION:
  B_EXPLICIT_FOURIER_MULTIPLIER_GRAPH:
    status: DEFERRED_TO_H4A1B_OPERATOR_BRANCH
  C_GENERIC_CLOSED_FORM_REPRESENTATION_INFRASTRUCTURE:
    status: KILLED_AS_CURRENT_OVERBUNDLE
  D_SOURCE_ACQUISITION_STOP:
    status: KILLED_BY_EXISTING_FORM_AND_FINITE_RESTRICTION_DATA

GLOWER_CHAIN_AFTER_RERANK:
  - OddSourceWeilCompression13_FORM_PULLBACK
  - OddModeSpanFormCore13_OR_DirectOddTailDomainClosure
  - YoshidaTailCoercivity13Explicit
  - OddFormResidualFeshbachLower13
  - CompressionTransferToAllFiniteN

DECISIVE_MISSING_SUPPLIERS:
  - exact_complex_normalized_odd_coefficient_isometry
  - exact_form_norm_core_for_literal_odd_modes_OR_direct_tail_coercivity_on_full_odd_form_domain
  - same_object_Yoshida_Suzuki_tail_crosswalk_with_explicit_constants
  - full_tail_residual_bound_for_form_level_Feshbach_certificate

STOP:
  GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PREFLIGHT_FAILED

SUCCESS:
  GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PROVED

SUCCESS_EFFECT:
  GLOWER_Lock_A: CLOSED
  B3_0: OPEN
  GLOWER_CONSTANT_FLOOR: OPEN
  associated_operator: OPEN
  selected_kTrial_operator_domain: OPEN
  H4A1B: OPEN
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

ARSENAL:
  STANDING_MANDATE_ACCEPTED: true
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: FINITE_CELL_TO_COFINAL_FAMILY_INTERFACE
VERIFIER: LEAN_THEN_PAPER_PLUS_ARB_INTERVAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
H4A1B: OPEN
N480: HOLD
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Source-lock ruling

The controlling attachment passes the requested byte lock:

```text
SHA-256:
  22fe052a67c3d93630e9e5423f6f843c327dc3d8337b0e826d2a7f72184fa753

bytes:
  73,949

wc-lines:
  2,349

final LF:
  true

UTF-8:
  PASS
```

The attachment states that the validated worktree is three commits ahead of the remote branch and makes its embedded B3.0AD/B3.0AE bytes authoritative. The local commit `574c58a6…0356` is therefore treated as an attachment-locked local state, not falsely reported as a remotely verified GitHub pin.  `[ABSTRACT][PAPER]`

## 2. Direct ruling

**Candidate A is the correct next action.**

B3.0AD and B3.0AE now supply enough exact form data to run the G-LOWER argument at form level:

1. an exact Hermitian source-Weil sesquilinear form on the shifted Arch domain;
2. exact `W02 + Arch − Prime` finite restrictions;
3. an explicit lower-bound shift;
4. a nonnegative extended energy on all `H_m`;
5. lower semicontinuity;
6. an exact finite-locus theorem;
7. an exact diagonal identity on the form domain.

B3.0AE does **not** supply an associated operator, but G-LOWER’s immediate target is a lower bound for a quadratic form. It is not an (H_m)-valued residual theorem.  `[ABSTRACT][LEAN]`

Thus:

[
\boxed{
\texttt{OddSourceWeilCompression13}
}
]

must now mean the normalized odd **pullback of the source form**, not an operator expression such as

[
P^-A_{13}P^-.
]

This category lock is mandatory under C04.

The older operator-first verdict remains valid for its original consumer. H4a1b requires an actual vector

[
(A_m-a)x\in H_m
]

and its (H_m)-norm. A form-domain theorem cannot supply that vector. The old graph/domain route is therefore deferred, not refuted.   `[ABSTRACT][PAPER]`

## 3. What B3.0AE now permits

Write

[
B_i(x,y)
========

\operatorname{sourceWeilSesquilinearForm}(i,x,y),
]

and

[
q_i(x)=\Re B_i(x,x).
]

B3.0AE gives a shifted extended energy (\widehat q_i) such that, on the exact form domain,

[
\boxed{
\widehat q_i(x)
===============

q_i(x)+C_i|x|^2,
}
]

where

[
C_i=\operatorname{sourceWeilLowerBoundConstant}(i).
]

It also proves that (\widehat q_i) is lower semicontinuous and that its finite locus is exactly the existing shifted Arch form domain.  `[ABSTRACT][LEAN]`

Therefore the raw G-LOWER target

[
q_{13}^{-}(x)\ge c_0|x|^2
]

is equivalent, on the odd form domain, to

[
\boxed{
\widehat q_{13}^{-}(x)
\ge
(C_{13}+c_0)|x|^2.
}
]

No associated operator occurs in this equivalence.

This is enough to:

* define the odd form restriction;
* identify every finite odd matrix as its normalized finite pullback;
* formulate high-mode form coercivity;
* formulate a form-level completion-of-squares or Feshbach inequality;
* transfer the resulting form floor to every exact finite odd CCM matrix.

`[ABSTRACT][LEAN]`

It is **not** enough to write:

[
\inf\operatorname{Spec}(A_{13}^{-})\ge c_0,
]

because `A₁₃⁻` has not been constructed. Until the representation theorem is formalized, the lawful conclusions are:

[
q_{13}^{-}\ge c_0
\quad\text{on its domain},
]

[
K_{13,N}^{-}\succeq c_0I
\quad\forall N,
]

and hence the corresponding finite lower-envelope statement.

## 4. The remaining form-side defect

B3.0AE does **not** by itself prove that the literal odd mode span is a **form core**.

Hilbert-space density is insufficient. A sequence can converge in `H_m` while its form energy fails to converge. Lower semicontinuity also has the wrong one-sided direction for deriving a lower bound on the limit merely from lower bounds on arbitrary Hilbert-norm approximants.

The missing supplier must therefore be one of the following exact statements.

### Supplier A — explicit odd form core

For the shifted nonnegative energy (\widehat q_{13}^{-}):

[
\boxed{
\forall x\in\mathcal D(\widehat q_{13}^{-}),
\ \exists x_n\in
\operatorname{span}{V_r-V_{-r}:r\ge1},
}
]

such that

[
|x_n-x|^2+
\widehat q_{13}^{-}(x_n-x)\longrightarrow0.
]

Suggested name:

```text
OddModeSpanFormCore13
```

### Supplier B — direct tail theorem on the full form domain

Alternatively, `YoshidaTailCoercivity13Explicit` may be stated directly on a closed tail subspace of the full odd form domain, with no density passage left to prove.

Only one of these two suppliers is necessary. Hilbert-norm density alone is not accepted.

`[COFINAL_FAMILY][CONDITIONAL]`

## 5. Exact smallest Lean child

### Owned path

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  D0PstarSourceWeilOddFormPullback13.lean
```

### Namespace

```lean
Q3.RouteB.D0Pstar
```

### Direct imports

```lean
import Q3.Proofs.RouteB.D0PstarSourceWeilClosedForm
import Q3.Proofs.RouteB.D0PstarShiftedArchFiniteModeDomain
import Q3.Proofs.RouteB.D0PstarCCMFiniteRieszOperator
```

The first import supplies B3.0AD/B3.0AE form data. The second supplies exact finite-mode form-domain inclusion. The third supplies the exact isometric finite CCM synthesis carrier.

The existing finite source ledger already preserves the ordered complex coefficient form, including the `W02 + Arch − Prime` signs.   `[FINITE_CELL][LEAN]`

The finite source matrix already owns the literal mode order and reflection map.  `[FINITE_CELL][LEAN]`

The D0.4 source lock fixes the normalized odd basis as

[
\frac{V_r-V_{-r}}{\sqrt2},
\qquad
1\le r\le N.
]

Its ambient Lean interface remains unpinned, so the normalized complex odd isometry is a genuine missing object rather than a duplicate wrapper.  `[ABSTRACT][PAPER]`

### Maximum public surface

```yaml
public_definitions:
  - ccmOddCoefficientIsometry
  - sourceWeilOddSynthesis13

public_theorems:
  - sourceWeilOddFormPullback13

total_public_declarations: 3
```

No public `OddWeilMatrix` alias is permitted. The literal matrix stays `ccmWeilMatFinite 13 N`; the compression is represented by the pullback through the isometry. This avoids a redundant matrix interface under C10.

### Exact coefficient isometry contract

```lean
noncomputable def ccmOddCoefficientIsometry
    (N : ℕ) :
    EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (CCMModeFinite N)
```

For `r : Fin N`, let (n=r+1). The exact coordinate law is:

```text
mode +n:
  a r / sqrt 2

mode -n:
  -a r / sqrt 2

mode 0:
  0
```

It must satisfy:

[
J_Na(\operatorname{ccmNegFinite}j)=-J_Na(j),
]

and

[
|J_Na|=|a|.
]

### Exact odd synthesis contract

```lean
noncomputable def sourceWeilOddSynthesis13
    (N : ℕ) :
    EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ]
      sourceArchimedeanShiftedFormDomain
        ⟨13, N, by norm_num⟩
```

It is the composition:

```text
normalized odd coefficient isometry
→ exact CCM finite synthesis equivalence
→ exact E_m_N inclusion into the shifted form domain.
```

It must not pass through `sourceCCMFiniteRieszOperator`. The finite Riesz operator is irrelevant to a form pullback.

### Exact public theorem

```lean
theorem sourceWeilOddFormPullback13
    (N : ℕ)
    (a b : EuclideanSpace ℂ (Fin N)) :
    sourceWeilSesquilinearForm
        ⟨13, N, by norm_num⟩
        (sourceWeilOddSynthesis13 N a)
        (sourceWeilOddSynthesis13 N b) =
      ∑ j, ∑ k,
        star ((ccmOddCoefficientIsometry N a) j) *
          (Q3.RouteB.ccmWeilMatFinite 13 N j k : ℂ) *
          (ccmOddCoefficientIsometry N b) k
```

This is the exact Lean realization of `OddSourceWeilCompression13`.

It is sesquilinear, not merely diagonal. The diagonal and shifted-energy laws then follow without another public wrapper:

[
q_{13}^{-}(a)
=============

\Re\left(
(J_Na)^*K_{13,N}(J_Na)
\right),
]

and

[
\widehat q_{13}^{-}(a)
======================

q_{13}^{-}(a)+C_{13}|a|^2.
]

`[FINITE_CELL][LEAN]`

## 6. Proof route

1. Define the exact normalized antisymmetric coefficient map on the literal `-N,…,N` carrier.
2. Prove its center is zero and reflection acts by `-1`.
3. Prove norm preservation from paired positive/negative entries and the exact `1/√2` factor.
4. Compose it with the existing finite synthesis isometry into `E_m_N`.
5. Use B3.0R to land in the exact form domain.
6. Apply B3.0AD’s finite-restriction theorem without changing coefficient order.
7. Retain `star` on the first coefficient slot.
8. Derive the shifted diagonal identity only by B3.0AE’s exact shift theorem.

No operator graph, operator domain, orthogonal projection, finite Riesz action, residual, eigenvalue, or numerical certificate enters.

## 7. Positive judge and semantic falsifiers

The auxiliary object and all mutations are precommitted before implementation, satisfying C09.

### Positive judge — `N = 1`

For (a=1), the mode order is `(-1,0,+1)` and the exact vector must be:

[
\boxed{
\left(-\frac1{\sqrt2},,0,,\frac1{\sqrt2}\right).
}
]

The judge must prove:

[
|J_1(1)|=1,
]

reflection acts by `-1`, and the pulled-back diagonal matrix value is

[
K_{+1,+1}-K_{+1,-1}.
]

Required code:

```text
P057_GLOWER_ODD_PULLBACK_POSITIVE_CONTROL_PASS
```

### Falsifier 1 — parity-sign mutation

Mutation:

[
(V_r-V_{-r})/\sqrt2
\quad\mapsto\quad
(V_r+V_{-r})/\sqrt2.
]

This enters the even sector.

Required stop:

```text
GLOWER_ODD_PULLBACK_PARITY_SIGN_MISMATCH
```

### Falsifier 2 — normalization mutation

Mutation: delete the `1/√2` factor.

Then:

[
|J_Na|^2=2|a|^2,
]

so both the claimed isometry and the lower-bound shift are off by a factor of two.

Required stop:

```text
GLOWER_ODD_PULLBACK_NORMALIZATION_MISMATCH
```

### Falsifier 3 — raw/shifted-form conflation

Mutation: identify

```text
sourceWeilShiftedExtendedQuadraticForm
```

with the raw CCM quadratic value while omitting

```text
sourceWeilLowerBoundConstant * ‖a‖².
```

Required stop:

```text
GLOWER_SHIFTED_ENERGY_RAW_FORM_CONFLATION
```

This is a direct C04 plant: the raw form and shifted nonnegative energy have the same domain but different numerical laws.

## 8. Candidate re-ranking

| Rank | Candidate                                    | Ruling                       | Cheap exclusion test                                                                                                     |
| ---: | -------------------------------------------- | ---------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
|    1 | **A — form-level odd restriction first**     | **Selected**                 | Exact three-declaration preflight above                                                                                  |
|    2 | B — explicit multiplier graph first          | Deferred to H4a1b            | Compile the exact form-pullback child with zero operator/graph/domain symbols                                            |
|    3 | C — generic closed-form representation layer | Killed as current overbundle | Compile A using only source-specific form imports; any generic representation structure then has zero immediate consumer |
|    4 | D — source-acquisition stop                  | Killed                       | `N=1` source-form pullback control constructed entirely from current local form and matrix data                          |

### Candidate B

The cheap test is:

```text
forbid:
  SourceWeilAssociatedGraph
  SourceWeilOperatorDomain
  sourceWeilAssociatedOperator
  LinearPMap

then compile:
  sourceWeilOddFormPullback13
```

A pass proves that the operator graph is not load-bearing for Lock A.

Required exclusion code:

```text
GLOWER_OPERATOR_GRAPH_NOT_LOAD_BEARING_FOR_FORM_PULLBACK
```

This does not kill the operator route globally. It removes it only from the current G-LOWER priority.

### Candidate C

A generic representation framework would be justified only if the selected form theorem could not be stated or proved without it. The exact source-specific child has no such dependency.

Required exclusion code after the A preflight passes:

```text
GLOWER_GENERIC_REPRESENTATION_LAYER_OVERBUNDLE
```

### Candidate D

The source object, exact form, exact finite restriction, mode order, reflection, and normalized finite synthesis are already present. A successful `N=1` control refutes the claim that new source acquisition is required before the first odd pullback theorem.

Required exclusion code:

```text
GLOWER_SOURCE_ACQUISITION_STOP_REFUTED_BY_EXISTING_FORM_DATA
```

## 9. Downstream obligations remain separate

| Obligation                                   | Status                | Associated operator required? | Exact next dependency                                                    |
| -------------------------------------------- | --------------------- | ----------------------------: | ------------------------------------------------------------------------ |
| Odd form restriction/pullback                | **Selected**          |                        **No** | normalized complex odd isometry                                          |
| Odd form-core or direct domain closure       | Open                  |                            No | form-norm approximation or direct full-domain tail theorem               |
| Yoshida high-mode coercivity                 | Open                  |                            No | same-object parity/Fourier crosswalk and explicit constants              |
| Residual Feshbach finite-head certificate    | Open                  |   No, if stated in form scale | full tail residual bound and finite lower envelope                       |
| Associated operator existence                | Open, separate branch |             Yes by definition | closed-form representation theorem or source-specific graph construction |
| Selected `kTrial` operator-domain membership | Open                  |                           Yes | associated graph plus explicit multiplier-domain proof                   |
| H4a1b (H_m)-valued residual                  | Open                  |                           Yes | selected-trial operator-domain and projected-action crosswalk            |
| `inf Spec(A_{13}^{-})` wording               | Open                  |                           Yes | associated self-adjoint operator                                         |
| All finite odd CCM floors                    | Open after Lock A     |                            No | G-LOWER form floor                                                       |

`[ABSTRACT][CONDITIONAL]`

The exact associated-operator theorem still required by the separate H4a1b branch is:

[
\operatorname{Dom}(A_i)
=======================

\left{
x\in\mathcal D(B_i):
\exists y\in H_m(i);
\forall g\in\mathcal D(B_i),;
B_i(x,g)=\langle y,g\rangle
\right},
]

with uniqueness of (y), definition (A_ix=y), and eventually self-adjointness. This theorem is not needed for the selected odd form pullback.

## 10. Repaired G-LOWER chain

The prior G-LOWER route remains viable, but its language must be repaired.

### Lock A — selected now

```text
OddSourceWeilCompression13
=
exact normalized odd form pullback.
```

`[FINITE_CELL][LEAN]`

### Lock B — still open

```text
OddModeSpanFormCore13
OR
YoshidaTailCoercivity13Explicit directly on the full odd form domain.
```

The Yoshida/Suzuki theorem must use the same centered interval, odd sector, normalization, and source-Weil convention. A neighboring tail theorem is forbidden. The previous wrong-object kill remains active.  `[COFINAL_FAMILY][PAPER_THEN_LEAN]`

### Lock C — form-level Feshbach

The abstract theorem should be stated for a Hermitian form decomposition, not for an already-existing unbounded operator.

One lawful form is:

```text
tail form ≥ d ‖z‖²
full cross residual bounded by ‖R h‖ ‖z‖
finite corrected head B - d⁻¹ R*R ≥ 0
------------------------------------------------
full form ≥ c0 ‖·‖²
```

The residual must include the complete infinite tail. A finite truncated residual cannot certify the conclusion.

`[ABSTRACT][LEAN_PLUS_ARB_INTERVAL]`

### Final lawful conclusion before operator representation

[
\boxed{
q_{13}^{-}(f)\ge c_0|f|^2
\quad
\forall f\in\mathcal D(q_{13}^{-})
}
]

and consequently

[
\boxed{
K_{13,N}^{-}\succeq c_0I
\quad
\forall N.
}
]

The phrase

```text
inf_spec_K_odd_infinity >= c0
```

must remain a paper shorthand until an associated self-adjoint operator is constructed.

## 11. Strongest attack

The strongest objection is:

> B3.0AE proves only lower semicontinuity of an extended diagonal function. It does not produce a Kato form structure. How can it support a Feshbach argument?

The objection kills three possible overclaims:

* automatic operator existence;
* self-adjointness;
* form-core convergence.

It does **not** kill Candidate A.

Candidate A consumes the already-proved Hermitian sesquilinear form from B3.0AD for cross terms and finite restrictions. It consumes B3.0AE only for the exact shifted diagonal, finite domain, and lower-semicontinuity lock. It makes no operator claim.

Before the infinite-tail theorem closes, one further supplier remains mandatory:

```text
OddModeSpanFormCore13
```

or a direct tail theorem already quantified over the entire odd form domain.

If neither supplier exists, the route stops at:

```text
GLOWER_ODD_FORM_CORE_OR_DIRECT_TAIL_DOMAIN_MISSING
```

It may not silently replace form-norm density by Hilbert-norm density.

A second fatal check is the shift ledger. If the implementation cannot preserve

[
\widehat q=q+C|\cdot|^2
]

exactly, it stops at:

```text
GLOWER_SHIFTED_ENERGY_RAW_FORM_CONFLATION
```

## 12. Final proposal

The next machine-sized object is the exact normalized odd form pullback at `m = 13`.

Registered prediction:

```text
sourceWeilOddFormPullback13:
  PASS.

likely first implementation defect:
  Fin/CCMModeFinite positive-negative index orientation
  or the 1/sqrt(2) normalization.

associated operator requirement:
  ABSENT from this child.

GLOWER tail prediction:
  UNCHANGED_UNTESTED.

corrected-head c0=1e-58 prediction:
  UNCHANGED_UNTESTED.
```

The pass condition for this transaction is exact equality. It is not a positivity verdict.

The later G-LOWER pass remains:

```text
lower endpoint of the corrected finite lower envelope >= 0.
```

The later target kill remains:

```text
rigorous Ritz upper envelope < c0.
```

Failure of tail extraction or failure of a sufficient Feshbach certificate does not kill the true lower bound.

## META CLOSEOUT

**What became smaller?**

The operator-versus-form fork is resolved for G-LOWER. The immediate wall is no longer “construct an associated operator.” It is the exact normalized odd pullback of an already-constructed form.

**What was killed?**

* operator-first as the current G-LOWER action;
* a generic Kato infrastructure project before a source-specific consumer;
* source-acquisition stop before the finite odd pullback;
* treating shifted energy as the raw CCM form.

**What must not be tried again?**

Do not use `P^-A P^-` notation before `A` exists. Do not infer a form core from Hilbert density. Do not run `N=480` as a lower-bound proof. Do not omit the explicit lower-bound shift.

**Current smallest named gap**

```text
GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PREFLIGHT_FAILED
```

After its success:

```text
GLOWER_ODD_FORM_CORE_OR_DIRECT_TAIL_DOMAIN_MISSING
```

then:

```text
YoshidaTailCoercivity13Explicit
```

and:

```text
OddFormResidualFeshbachLower13
```

**Fate of prior predictions**

```text
"tail supplier passes after explicit constants":
  RETAINED_UNTESTED.

"corrected head at c0=1e-58 is positive":
  RETAINED_UNTESTED.

"first failure is normalization or full residual budget":
  RETAINED;
  normalization is now tested first by the odd-isometry control.

"operator graph is the next mandatory B3 action":
  NOT_REFUTED_GLOBALLY;
  RE-SCOPED_TO_H4A1B_AND_OPERATOR_DOMAIN_BRANCH;
  NO_LONGER_NEXT_FOR_GLOWER.
```

```yaml
iteration:
  target: post_B3_0AE_representation_rerank
  status: PROGRESS
  failed_strategy: require_associated_operator_before_any_GLOWER_form_restriction
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PREFLIGHT_FAILED
  invariant_learned: raw_form_shifted_energy_and_associated_operator_are_three_distinct_categories
  forbidden_future_move: use_operator_compression_notation_or_Hilbert_density_as_form_core
  next_decisive_test: exact_N1_normalized_odd_form_pullback_preflight
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```

## CODEX DIRECTIVE

```yaml
TARGET:
  GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PREFLIGHT

MODE:
  PRECOMMITTED_NEXT_TRANSACTION_ONLY
  EXECUTE_NOW: false
  NO_REPO_WRITE: true
  NO_LEAN_EDIT: true
  NO_UNTRACKED_HARNESS_IN_THIS_REVIEW: true
  SEPARATE_OPERATIONAL_RELEASE_REQUIRED: true

SOURCE_LOCK_FOR_LATER_RELEASE:
  controlling_attachment_sha256:
    22fe052a67c3d93630e9e5423f6f843c327dc3d8337b0e826d2a7f72184fa753
  B3_0AE_source_sha256:
    dcd9fa0eac5791610ce1ebd4ea0a7bbfbff5d9d6ec8707133d1146f657fdd769
  preserve_foreign_staged_patch_sha256:
    291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b

OWNED_PATH_FOR_LATER_RELEASE:
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilOddFormPullback13.lean

EXACT_DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarSourceWeilClosedForm
  - Q3.Proofs.RouteB.D0PstarShiftedArchFiniteModeDomain
  - Q3.Proofs.RouteB.D0PstarCCMFiniteRieszOperator

PUBLIC_SURFACE_MAXIMUM:
  definitions:
    - ccmOddCoefficientIsometry
    - sourceWeilOddSynthesis13
  theorems:
    - sourceWeilOddFormPullback13
  total: 3

MANDATORY_OBJECT_LOCK:
  odd_basis:
    positive_mode: a_r_div_sqrt2
    negative_mode: neg_a_r_div_sqrt2
    center_mode: zero
  mode_order: literal_CCMModeFinite_minus_N_through_N
  source_form: sourceWeilSesquilinearForm
  finite_matrix: ccmWeilMatFinite_13_N
  first_slot: conjugate_linear
  second_slot: linear
  shifted_energy_relation:
    q_shifted_equals_q_raw_plus_sourceWeilLowerBoundConstant_times_norm_sq

MANDATORY_JUDGES:
  - P057_GLOWER_ODD_PULLBACK_POSITIVE_CONTROL_N1
  - GLOWER_ODD_PULLBACK_PARITY_SIGN_MISMATCH
  - GLOWER_ODD_PULLBACK_NORMALIZATION_MISMATCH
  - GLOWER_SHIFTED_ENERGY_RAW_FORM_CONFLATION

FORBIDDEN_DEPENDENCIES_AND_CLAIMS:
  - SourceWeilAssociatedGraph
  - SourceWeilOperatorDomain
  - sourceWeilAssociatedOperator
  - sourceCCMFiniteRieszOperator_as_form_supplier
  - operator_compression
  - selected_kTrial_operator_domain
  - projection_leakage
  - continuum_numerator
  - N480
  - Aitken
  - checkpoint_decrement
  - route_promotion
  - PX_RH_claim

LATER_VALIDATION_REQUIRED:
  - verify_exact_local_source_hashes
  - verify_candidate_SHA256_bytes_lines_final_LF
  - direct_lake_env_lean
  - target_build
  - full_build
  - q3_check
  - exact_three_declaration_public_surface
  - forbidden_token_and_dependency_scan
  - require_axioms_exactly_[propext_Classical.choice_Quot.sound]
  - run_positive_control_and_all_three_falsifiers
  - verify_no_operator_or_graph_symbol_in_dependency_closure
  - strict_Spine
  - proof_database_import_and_idempotence
  - routeb_status_check
  - exact_git_status_report

STOP:
  GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PREFLIGHT_FAILED

SUCCESS:
  GOAL057_GLOWER_ODD_SOURCE_WEIL_FORM_PULLBACK13_PROVED

AFTER_SUCCESS:
  closed:
    - OddSourceWeilCompression13_FORM_PULLBACK
  still_open:
    - OddModeSpanFormCore13_OR_DirectOddTailDomainClosure
    - YoshidaTailCoercivity13Explicit
    - OddFormResidualFeshbachLower13
    - associated_operator
    - selected_kTrial_operator_domain
    - H4A1B
  coarse_checkpoints_closed: 0
  coarse_checkpoints_remaining: 10

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  h4a1b: OPEN
  n480: HOLD
  Aristotle_submission: NONE
  route_promotion: false
  px_rh_claim: NOT_MADE
```
