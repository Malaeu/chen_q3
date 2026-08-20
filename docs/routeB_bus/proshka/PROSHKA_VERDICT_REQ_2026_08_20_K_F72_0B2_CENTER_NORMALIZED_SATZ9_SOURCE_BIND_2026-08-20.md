# STATUS: CONDITIONAL — S2 PRIVATE SOURCE WITNESS SELECTED; S1 IS ONLY THE GENERIC KERNEL RECEIVER
```yaml
PRIMARY: SELECT_S2_PRIVATE_SOURCE_WITNESS_PLUS_S1_GENERIC_RECEIVER
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-20-K

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: 4c65398c894fcca8cc6ad9fa73b810097e14d1c8
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_BLOB: 6ec0d72aafb1377f4913870fc10e0c158c48017e
  SOLVER_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersPhysicalFourierScalarProportionality.lean
  SOLVER_BLOB: 56d69d9fd935e6f15e35785e2fc7f31a5c68958b
  CENTER_LOCK_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CenterAnchorScalarLock.lean
  CENTER_LOCK_BLOB: a4195440b1ad3edfca785a3568fa9c8605fd3ff1
  PARAMETER_DICTIONARY_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean
  PARAMETER_DICTIONARY_BLOB: 10e9e9729dd320dc5793aa013fabc0a73eba7c61
  MS_USAGE_CARD_PATH: docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md
  MS_USAGE_CARD_BLOB: 593cc68522c20648fe6b30254da8bdc2ce6309b6

DECISION:
  S1_CHARACTERIZATION_ONLY:
    status: INSUFFICIENT_FOR_SOURCE_PROVENANCE
    retained_role: GENERIC_KERNEL_RECEIVER
  S2_INDEPENDENT_EXISTENCE:
    status: SELECTED_LOAD_BEARING_SUPPLY
    implementation_role: PRIVATE_SOURCE_WITNESS
  public_route_object_graph:
    export_literal_ps_object: false
    export_center_normalized_equality: true
  raw_paper_ps_normalization:
    law: L2_NORMALIZATION_PLUS_CENTER_SIGN
    raw_value_at_zero_equals_one: false
  center_normalized_source_view:
    formula: "pbar_n,k(x) = Ps_n^0(x/lambda_k; gamma_k^2) / Ps_n^0(0; gamma_k^2)"
    value_at_zero: 1

PROJECT_SUPPLY:
  selected_center_nonzero: PROVED_LEAN
  selected_center_real: PROVED_LEAN
  selected_evenness: PROVED_LEAN
  selected_interior_derivative: PROVED_LEAN
  selected_derivative_at_zero: DERIVABLE_FROM_EVENNESS_NOT_YET_EXPORTED_AS_PUBLIC_WRAPPER
  selected_physical_ode: PROVED_LEAN
  center_anchor_scalars: PROVED_LEAN

SOURCE_SUPPLY:
  literal_Ps_definition_and_normalization: PAPER_PROVED_NOT_LEAN_MATERIALIZED
  source_center_nonzero_for_n_0_4: PAPER_PROVED
  source_evenness_for_n_0_4: PAPER_PROVED
  source_derivative_at_zero: PAPER_DERIVABLE_FROM_EVENNESS_AND_REGULARITY
  source_physical_ode_lift: OPEN_PROJECT_PORT
  source_to_project_separation_eigenvalue: OPEN_EXPLICIT_CROSSWALK

PARAMETER_LOCK:
  lambda_k: sqrt(k+2)
  gamma_k: 2*pi*lambda_k^2
  G_k: gamma_k^2
  paper_parameter: gamma_k^2
  sqrt_G_eq_gamma: DERIVABLE_USING_GAMMA_POSITIVITY
  theta_project: mode4ClassicalEvenEigenvalue(G_k,j) + G_k
  theta_source: paper_lambda_(2j)^0(G_k) + G_k
  theta_equality_is_automatic_from_G: false

F72_0B2:
  generic_receiver: LEAN_READY
  source_inhabitant: OPEN_LOAD_BEARING
  endpoint_extension: LEAN_READY
  CLOSES_NOW: false
  NEXT_AFTER_FULL_CLOSE: F72_0B3

EXACT_MISSING_IDENTITY:
  name: SATZ9_FIXED_MODE_SOURCE_DATA_INHABITANT
  statement: >-
    For n in {0,4} and every precommitted k, materialize the independently
    normalized paper first-kind spheroidal mode at gamma_k^2, prove its
    source separation value equals the selected project separation value,
    and supply the physical-window ODE/evenness/center data consumed by the
    generic center-normalized uniqueness receiver.

DISCRIMINATOR:
  name: INDEPENDENT_SOURCE_AND_SEPARATION_LOCK
  pass: >-
    The raw source object and its paper eigenvalue are defined before and
    without the selected project mode; the final equality is derived by the
    ODE receiver.
  kill: >-
    The source object is defined from the selected project target, or the
    desired equality/eigenvalue identity is inserted as a hypothesis.
  zero_consistent: INCONCLUSIVE

FAILURE_CODES:
  - F72_0B2_SOURCE_REPRESENTATIVE_DEFINED_BY_PROJECT_TARGET
  - F72_0B2_SOURCE_WITNESS_UNMATERIALIZED
  - F72_0B2_SEPARATION_EIGENVALUE_CROSSWALK_GAP
  - F72_0B2_SOURCE_PHYSICAL_ODE_LIFT_GAP
  - F72_0B2_CENTER_DERIVATIVE_INTERFACE_GAP
  - F72_0B2_OPEN_TO_CLOSED_WINDOW_GAP
  - F72_0B2_PARAMETER_SQUARE_ROOT_UNIT_MISMATCH
  - F72_0B2_CENTER_NORMALIZED_SATZ9_SOURCE_BIND_CLOSED

CANDIDATE_REPRESENTATIONS:
  R1_S2_PRIVATE_WITNESS_PLUS_S1_RECEIVER:
    rank: PRIMARY
    kill_power: 10/10
    cost: 3/10_after_source_interface
  R2_UNIVERSAL_CENTER_NORMALIZED_SATZ9_THEOREM:
    rank: RUNNER_UP
    kill_power: 8/10
    cost: 4/10
    warning: SOURCE_EXISTENCE_MUST_NOT_BE_HIDDEN_IN_THE_THEOREM_INTERFACE
  R3_DIRECT_PROJECT_ODE_VOLERRA_RATE:
    rank: RESERVE_NOT_AUTHORIZED
    kill_power: 8/10
    cost: 8/10

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: false
ARISTOTLE_AUTHORIZED: false
QUEUE_STATUS_MUTATED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
```

## ROUTE MAP

### 1. Решение развилки

Выбор — не чистый `S1` и не публичный `S2`-объект.

```text
S2 supplies provenance privately.
S1 exposes the generic Lean receiver publicly.
```

`S1` сам по себе не закрывает source bind. Квантор

```text
for every even regular solution of the same ODE ...
```

доказывает только одномерность уже выбранного eigenspace. Он не доказывает,
что этот eigenspace является именно paper degree `n=0` или `n=4`, и не даёт
права применить Satz 9. При фиксированном `G` существуют разные regular even
modes с разными separation values. `[COFINAL_FAMILY][PAPER]` **[C04]**

`S2` нужен как private source witness: literal first-kind spheroidal function
из Meixner--Schäfke/DLMF normalization, вместе с paper eigenvalue and source
properties. Но этот witness не надо тащить в public Route-B object graph.
Публичным результатом должен быть только center-normalized equality on the
physical window. `[COFINAL_FAMILY][CONDITIONAL]`

Определить paper witness как selected project mode запрещено. Такая
конструкция делает equality tautological and transports no Satz-9 provenance.
`[COFINAL_FAMILY][PAPER]` **[C10]**

### 2. Важная поправка к нормировке

Литеральный `Ps_n^m` не нормирован условием `Ps(0)=1`. Стандартная
Meixner--Schäfke/DLMF first-kind normalization fixes its `L2(-1,1)` mass and
then fixes the sign at the center for even parity. Для `m=0`, `n=0,4` center
sign is positive, so the center is nonzero. `[ABSTRACT][PAPER]`

Поэтому правильный source object для receiver — derived center-normalized
view

\[
\bar p_{n,k}(x)
=
\frac{\operatorname{Ps}_{n}^{0}(x/\lambda_k;\gamma_k^2)}
     {\operatorname{Ps}_{n}^{0}(0;\gamma_k^2)}.
\]

Он source-derived, has value `1` at the center, and does not use the project
mode. The raw paper normalization remains available inside F72.1A to recover
the Satz-9 denominator lower bound. `[COFINAL_FAMILY][PAPER]`

A theorem field named

```lean
rawPs_valueAtZero_eq_one
```

would be false for the literal source convention. The legal field is

```lean
centerNormalizedPs_valueAtZero_eq_one
```

derived from `rawPs_center_ne`. `[ABSTRACT][PAPER]`

### 3. Center nonzero and first derivative

The project center denominator is already closed directly:

```lean
selectedFerrersCenterZero_ne
selectedFerrersCenterFour_ne
```

in `G6N1CenterAnchorScalarLock.lean`. These use the exact selected modes and
are stronger and cheaper than reconstructing nonvanishing through an
existential Fourier scalar. `[COFINAL_FAMILY][LEAN]`

The physical scalar-sign theorem gives a redundant second route:

```text
chi != 0
0 < chi * center
----------------
center != 0
```

but no downstream theorem should identify an existential `chi` with the stored
`P.chi2` merely by notation. The direct center theorem avoids that extra
identity. `[FINITE_CELL][LEAN]` **[C04]**

The derivative-at-center input is not a new analytic hypothesis. The selected
modes are even and have an interior derivative; the source modes with
`n-m` even are even and regular. In both cases the first derivative at zero is
therefore zero. The current helper `derivative_value_zero_of_even` is private,
so a public generic wrapper must be added or the three-line argument repeated.
`[ABSTRACT][LEAN_READY]`

### 4. The spectral parameter is a separate obligation

The project dictionary already proves

\[
\lambda_k=\sqrt{k+2},\qquad
\gamma_k=2\pi\lambda_k^2,\qquad
G_k=\gamma_k^2=\operatorname{mode4JacobiG}(k+2).
\]

`[COFINAL_FAMILY][LEAN]`

This does **not** prove equality of the separation eigenvalues. The solver
uses

\[
\theta^{proj}_{j,k}
=
\operatorname{mode4ClassicalEvenEigenvalue}(G_k,j)+G_k,
\]

whereas the source mode uses

\[
\theta^{src}_{j,k}
=
\lambda_{2j}^{0}(G_k)+G_k.
\]

The field

\[
\boxed{
\lambda_{2j}^{0}(G_k)
=
\operatorname{mode4ClassicalEvenEigenvalue}(G_k,j)
}
\]

is therefore load-bearing. It belongs to F72.0B2, not to the already-closed
`gamma/G` arithmetic. Omitting it lets one bind the same differential
expression to the wrong even mode. `[COFINAL_FAMILY][CONDITIONAL]` **[C04]**

The notation `c = sqrt G` is legal only after recording `c=gamma_k>0` and
`G=gamma_k^2`. It must not be confused with Fuchs's independently scaled
parameter. `[COFINAL_FAMILY][LEAN_READY]`

### 5. Exact kernel decomposition

#### F72.0B2A — generic closed-window uniqueness receiver

Prove one source-free theorem:

```lean
theorem complex_prolate_even_center_one_unique_on_closed_window
    (lambda theta : ℝ) (hlambda : 0 < lambda)
    (f df g dg : ℝ → ℂ)
    (hf_cont : ContinuousOn f (Icc (-lambda) lambda))
    (hg_cont : ContinuousOn g (Icc (-lambda) lambda))
    (hf_even : Function.Even f)
    (hg_even : Function.Even g)
    (hf : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt f (df x) x)
    (hg : ∀ x ∈ Ioo (-lambda) lambda, HasDerivAt g (dg x) x)
    (hfluxf : /* exact current solver flux ODE at theta */)
    (hfluxg : /* exact current solver flux ODE at theta */)
    (hf0 : f 0 = 1)
    (hg0 : g 0 = 1) :
    Set.EqOn f g (Icc (-lambda) lambda)
```

Proof route:

1. derive `df 0 = 0` and `dg 0 = 0` from evenness and the derivative facts;
2. apply `complex_prolate_divergence_solution_unique_of_center` on `Ioo`;
3. extend to `Icc` by continuity and `closure (Ioo (-lambda) lambda)=Icc`.

This floor closes the receiver only. It does not close F72.0B2 and must not be
counted as source provenance. `[ABSTRACT][LEAN_READY]`

#### F72.0B2B — independent Satz-9 source package

For each `k` and `j in {0,2}`, materialize a private source package whose raw
function is the literal first-kind spheroidal representative of full degree
`2*j` and order zero. Required fields:

```text
raw source definition independent of project target;
raw source normalization and center sign;
raw center nonzero;
raw parity/evenness;
regularity and physical-coordinate differentiability;
paper parameter gamma_k^2 = G_k;
paper separation eigenvalue = project selected separation eigenvalue;
physical divergence-form ODE with the exact solver theta.
```

The source record or proof file must name Meixner--Schäfke/DLMF provenance.
An abstract structure inhabited only by assuming all fields is not a proof of
this floor. `[COFINAL_FAMILY][CONDITIONAL]`

#### F72.0B2C — center-normalized source/project wrappers

Define only private normalized views:

\[
\bar f_{j,k}(x)=\frac{f_{j,k}(x)}{f_{j,k}(0)},
\qquad
\bar p_{j,k}(x)=\frac{p_{j,k}(x)}{p_{j,k}(0)}.
\]

Prove that scalar division preserves the exact homogeneous ODE, continuity,
evenness and derivative data. `[COFINAL_FAMILY][LEAN_READY]`

#### F72.0B2D — source bind

Apply F72.0B2A to obtain

\[
\boxed{
\forall x\in[-\lambda_k,\lambda_k],
\quad
\frac{f_{j,k}(x)}{f_{j,k}(0)}
=
\frac{p_{j,k}(x)}{p_{j,k}(0)}
}
\]

for `j=0,2`. `[COFINAL_FAMILY][CONDITIONAL]`

The directly consumed anchored form is

\[
 a_{0,k}f_{0,k}(x)=\bar p_{0,k}(x),
\qquad
 a_{4,k}f_{4,k}(x)=3\bar p_{4,k}(x),
\]

because `a0=1/f0(0)` and `a4=3/f4(0)` are already kernel-proved.
`[COFINAL_FAMILY][CONDITIONAL]`

#### F72.0B2E — handoff

After both modes are proved, F72.0B2 closes. The next load-bearing floor is
`F72.0B3`, which may invoke the center-normalized Satz-9 rate without exposing
the raw paper functions publicly. `[COFINAL_FAMILY][CONDITIONAL]`

## W13 SEMANTIC CHECKS

| Check | Result | Tags |
|---|---|---|
| W13.1 raw source object independent of project mode | **OPEN** | `[COFINAL_FAMILY][CONDITIONAL]` |
| W13.2 literal source normalization is recorded correctly | **PASS**: L2 plus sign, not center-one | `[ABSTRACT][PAPER]` |
| W13.3 source center nonzero for degrees 0 and 4 | **PASS on paper; Lean port open** | `[COFINAL_FAMILY][PAPER]` |
| W13.4 source parity and derivative zero | **PASS on paper; Lean port open** | `[COFINAL_FAMILY][PAPER]` |
| W13.5 gamma/G/unit dictionary | **PASS** | `[COFINAL_FAMILY][LEAN]` |
| W13.6 carrier `j=0,2` to full degree `n=0,4` | **PASS** | `[COFINAL_FAMILY][LEAN]` |
| W13.7 source separation value equals project separation value | **OPEN** | `[COFINAL_FAMILY][CONDITIONAL]` |
| W13.8 dimensionless-to-physical coordinate lift | **paper formula locked; Lean wrapper open** | `[COFINAL_FAMILY][CONDITIONAL]` |
| W13.9 exact ODE sign and theta | **CONDITIONAL on W13.7/8** | `[COFINAL_FAMILY][CONDITIONAL]` |
| W13.10 project center denominator | **PASS** | `[COFINAL_FAMILY][LEAN]` |
| W13.11 project derivative at zero | **DERIVABLE; public wrapper open** | `[COFINAL_FAMILY][LEAN_READY]` |
| W13.12 open-window uniqueness receiver | **PASS** | `[ABSTRACT][LEAN]` |
| W13.13 closed-window equality and downstream handoff | **LEAN-ready after source package** | `[COFINAL_FAMILY][CONDITIONAL]` |

## FINAL PROPOSAL

Use the combined architecture:

```text
private S2 source witness
  -> public S1 center-normalized source data
  -> generic closed-window uniqueness receiver
  -> selected Ferrers center-normalized equality
  -> F72.0B3 Satz-9 rate port.
```

Registered prediction before implementation:

```text
P_K_IMPL_1:
  the generic closed-window receiver compiles with no new analytic lemma;
  most likely friction is Lean normal-form plumbing around derivative-zero
  and closure Ioo=Icc.

P_K_IMPL_2:
  the first genuine source blocker is the exact paper/project separation
  eigenvalue equality, not the center or gamma arithmetic.
```

Cheapest decisive test: write the source package signature first and try to
fill every field without mentioning the selected project function in the raw
source definition. If the separation field cannot be supplied, stop before
writing the generic receiver. `[COFINAL_FAMILY][CONDITIONAL]`

### Candidate representations

1. **R1 — S2 private witness plus S1 receiver.** Source-faithful and keeps the
   public graph small. **Kill power 10/10; cost 3/10 after the source
   interface.** `[COFINAL_FAMILY][CONDITIONAL]`
2. **R2 — universal center-normalized Satz-9 theorem.** This can remove the
   literal object from Lean, but only if the paper theorem is genuinely ported
   for the full characterized eigenspace. Merely declaring the universal
   theorem would hide S2 existence and is not accepted. **Kill power 8/10;
   cost 4/10.** `[COFINAL_FAMILY][CONDITIONAL]`
3. **R3 — direct normalized ODE/Volterra rate.** Avoids the source
   representative but reopens the analytic rate proof. **Kill power 8/10;
   cost 8/10. Not authorized.** `[COFINAL_FAMILY][CONDITIONAL]`

## STRONGEST ATTACK

The strongest reviewer objection is:

> “Same ODE” is underspecified. At fixed `G`, degree zero and degree four are
> both even, regular and nonzero at the center. Why does the quantified source
> candidate belong to the degree-four Satz-9 mode rather than another even
> eigenspace?

This objection is fatal to pure S1. The repair is the explicit separation
identity

\[
\lambda_{4}^{0}(G_k)
=
\operatorname{mode4ClassicalEvenEigenvalue}(G_k,2),
\]

and its degree-zero companion. `G` equality alone cannot replace it.
`[COFINAL_FAMILY][CONDITIONAL]` **[C04]**

A second fatal substitution is to define

```text
paperPs := selectedProjectMode
```

or to add

```text
hbind : paperPs = selectedProjectMode / center
```

as a premise. Both make the theorem tautological and import no Satz-9
information. The weakest repaired statement is the generic receiver plus an
independently inhabited source package. `[COFINAL_FAMILY][PAPER]` **[C10]**

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION IS AUTHORIZED BY THIS ADJUDICATION.

Next admissible Lean transaction after the source-package contour is accepted:

  F72_0B2A_COMPLEX_PROLATE_EVEN_CENTER_ONE_CLOSED_WINDOW_UNIQUENESS

Target file:
  Q3/Proofs/RouteB/G6N1CenterNormalizedProlateODEReceiver.lean

Inputs:
  existing complex_prolate_divergence_solution_unique_of_center;
  continuity on Icc;
  evenness;
  exact derivative and flux data;
  center value one.

Output:
  EqOn on Icc, deriving both center derivatives internally.

Forbidden:
  defining any Satz-9 source function;
  assuming the target equality;
  adding a new axiom/constant/sorry/admit;
  weakening Icc to Ioo in the exported theorem;
  claiming F72.0B2 closed.

Validation:
  lake env lean Q3/Proofs/RouteB/G6N1CenterNormalizedProlateODEReceiver.lean
  lake build Q3.Proofs.RouteB.G6N1CenterNormalizedProlateODEReceiver
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1CenterNormalizedProlateODEReceiver.lean

Expected axioms:
  [propext, Classical.choice, Quot.sound]

Success code:
  F72_0B2A_CENTER_NORMALIZED_ODE_RECEIVER_LEAN

Failure code:
  F72_0B2A_CENTER_DERIVATIVE_OR_ENDPOINT_NORMAL_FORM_GAP
```

## META CLOSEOUT

**Что стало меньше?**

F72.0B2 reduced from “define a paper special function and identify it” to two
orthogonal obligations:

```text
A. generic center-normalized ODE receiver;
B. independent source inhabitant with exact separation-value crosswalk.
```

`[COFINAL_FAMILY][CONDITIONAL]`

**Что убито?**

- pure S1 as a complete source bind;
- raw paper `ps(0)=1`;
- automatic theta equality from `G` equality;
- use of the existential Fourier scalar to reprove a center denominator;
- open-window equality masquerading as the closed-window theorem.

**Что нельзя пробовать снова?**

Do not define the source representative from the project target. Do not hide
source existence in a universal theorem declaration. Do not omit the paper-to-
project separation eigenvalue equality.

**Current smallest named gap:**

```text
SATZ9_FIXED_MODE_SOURCE_DATA_INHABITANT
```

**Next cheapest decisive test:**

Write the exact source-package signature and verify that the raw source
definition and paper eigenvalue are independent of the selected project mode.

**Fate of registered predictions:**

```text
P_K1: existing uniqueness receiver is sufficient after exact data
  CONFIRMED.

P_K2: derivative equality at zero is a hidden new analytic input
  REFUTED; it follows from evenness plus the existing derivative facts.

P_K3: theta equality follows automatically from gamma/G equality
  REFUTED; the separation eigenvalue crosswalk is independent.

P_K4: pure S1 closes source provenance
  REFUTED.

P_K5: the literal paper Ps is center-normalized to one
  REFUTED; center-one is a derived private view.
```

**Memory entry:**

```yaml
iteration: REQ-2026-08-20-K
target: F72_0B2_CENTER_NORMALIZED_SATZ9_SOURCE_BIND
status: OPEN
failed_strategy: PURE_CHARACTERIZATION_WITHOUT_SOURCE_PROVENANCE
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: SATZ9_FIXED_MODE_SOURCE_DATA_INHABITANT
invariant_learned: same_G_does_not_imply_same_separation_eigenvalue
forbidden_future_move: define_paper_source_from_project_target
next_decisive_test: independent_source_and_separation_lock
```
