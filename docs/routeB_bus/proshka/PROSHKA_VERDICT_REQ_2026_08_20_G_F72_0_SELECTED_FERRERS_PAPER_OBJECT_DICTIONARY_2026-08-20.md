# STATUS: CONDITIONAL — PACKAGE D RATIFIED; F72.0 PARAMETER/INDEX DICTIONARY CLOSED, LITERAL PAPER-FUNCTION BIND REMAINS OPEN
```yaml
PRIMARY: RATIFY_D_AND_REPAIR_F72_0_AS_TWO_LAYER_OBJECT_DICTIONARY
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-20-G

PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  QUEUE_HEAD_AT_START: 1706fe0355ccd5b5eda966b0d72166f7e8880712
  PACKAGE_D_COMMIT: c10c9b580bbf0349c6ea0311c889f2c0f2596655
  PACKAGE_D_PARENT: 52dddd66b397cc7185033499524a2aff54896cc4

PACKAGE_D:
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPreAnchorDataInhabitant.lean
  BLOB: 8d420f8a6e2926f9c10d65480dca41e13ffe97ce
  SOURCE_SHAPE_AUDIT: PASS
  PROVENANCE_AUDIT: PASS
  INDEX_FORMULA_AUDIT: PASS
  PAIR_SPEC_AUDIT: PASS
  GATE_RECEIPT_AUDIT: PASS
  JUDGE_RERAN_LEAN: false
  STATUS: RATIFIED

F72_0:
  ORIGINAL_NAME: SelectedFerrersPaperObjectDictionary
  ORIGINAL_COST: 2/10
  PROJECT_PARAMETER_INDEX_DICTIONARY: PROVED_ON_SHELF
  PAPER_SATZ9_NORMALIZATION_DICTIONARY: RATIFIED_PAPER
  LITERAL_PROJECT_MODE_EQ_SCALAR_MUL_PS_N: OPEN_SOURCE_BIND
  FIRST_LEAN_NODE_CLAIM: REPAIRED_TO_F72_0A_PROJECT_PARAMETER_LOCK
  OVERALL_STATUS: CONDITIONAL

EXACT_INDEX_LOCK:
  schedule: "m_k = N_k = k+2; K_k = 5*(k+2)"
  project_even_carrier_j: [0, 2]
  paper_full_degree_n: [0, 4]
  law: "n = 2*j"
  warning: "production field chi2 belongs to full degree n=4, not degree n=2"

EXACT_PARAMETER_LOCK:
  window_lambda: "lambda_k = sqrt(k+2)"
  dimensionless_coordinate: "z = u/lambda_k"
  paper_gamma: "gamma_k = 2*pi*lambda_k^2 = 2*pi*(k+2)"
  project_G: "mode4JacobiG(k+2) = gamma_k^2"
  spheroidal_order: 0
  project_DLMF_eigenvalue: "Lambda_{j,k} = mode4ClassicalEvenEigenvalue(gamma_k^2,j)"
  physical_PW_eigenvalue: "Lambda_{j,k} + gamma_k^2"

SATZ9_FIXED_MODE_NORMALIZATION:
  paper_mode: "h_{n,lambda}(u) = s_n*lambda^(-1/2)*ps_n^0(u/lambda;gamma^2)"
  s_0: "1/sqrt(2)"
  s_4: "3/sqrt(2)"
  derivation: "CCM equations (7.10)-(7.11), gamma=2*pi*lambda^2"

SCALAR_LOCK:
  exact_missing_scalar: "a_{j,k} = h_{2j,lambda_k}(0) / f^{proj}_{j,k}(0), after the paper representative is source-bound"
  orientation: SOURCE_DERIVED_SIGNED_RATIO_AT_ZERO
  factor_four_occurrences_in_individual_mode_dictionary: 0
  factor_four_occurrences_in_port_combination_layer: 1
  port_law: "portSourceScale_k = 4*lemma72Scale_k"

FUCHS_BOUNDARY:
  DOI: 10.1016/0022-247X(64)90017-4
  PDF_STATUS: NEEDS_OWNER
  BLOCKS_F72_0: false
  BLOCKS_F72_3_SCOPE_LOCK: true
  alias_only_now:
    - "project P.chi0 <-> paper physical finite-Fourier scalar of full degree 0"
    - "project P.chi2 <-> paper physical finite-Fourier scalar of full degree 4"

W9_LEDGER:
  CLOSES:
    - PACKAGE_D_SOURCE_PROVENANCE_AND_INDEX_AUDIT
    - SELECTED_FERRERS_PROJECT_PARAMETER_INDEX_DICTIONARY
    - SATZ9_FIXED_MODE_NORMALIZATION_CONVENTION_LOCK
    - FACTOR_FOUR_SINGLE_OCCURRENCE_FIREWALL
  OPENS:
    - SELECTED_FERRERS_LITERAL_MEIXNER_SCHAEFKE_REPRESENTATIVE_BIND
  NEW_INPUT_COUNT: 1
  OLD_BLOCKER_COUNT_REMOVED: 4
  NEW_INPUT_IS_SMALLER_THAN_REMOVED_BLOCKERS: true

NEXT_MINIMAL_GAP: SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE
DISCRIMINATOR: NO_TAUTOLOGICAL_PS_DEFINITION

CANDIDATE_REPRESENTATIONS:
  R1_LITERAL_FIXED_MODE_SOURCE_BIND:
    kill_power: 10/10
    proof_cost: 5/10
    role: PRIMARY
  R2_DIRECT_PROJECT_MODE_RATE_WITH_EXISTENTIAL_SCALAR:
    kill_power: 9/10
    proof_cost: 7/10
    role: RUNNER_UP

REGISTERED_PREDICTIONS:
  P_G_D1: "Package D has no index/provenance discrepancy"
  P_G_D2: "The only F72.0 load-bearing remainder is literal paper-function normalization, not gamma/index algebra"
  P_G_D3: "The factor 4 belongs only to the zero-mass/port layer"
  P_G_D4: "Fuchs access remains irrelevant to F72.0 and relevant only to F72.3"

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Independent audit of package D

The package is ratified as the exact **selected pre-anchor inhabitant**. The schedule is fixed before the proof:

\[
m_k=N_k=k+2,\qquad K_k=5(k+2).
\]

The public pair is chosen only from
`exists_modeZero_modeFour_selectedFerrersProductionProlatePair`; the exported
`pair_spec` keeps the selected `S0`, selected `S4`, exact physical window,
mode identities, positive integrals, nonzero Fourier scalars, restricted
Fourier relations, and strict differential-eigenvalue order visible. No
unrelated `ProlatePair` is introduced. `[COFINAL_FAMILY][LEAN]`

The source record reports direct Lean, named build, `q3_check`, and the
standard axiom triple for the printed declarations. I audited the source and
the receipt but did not rerun the Lean toolchain. `[COFINAL_FAMILY][LEAN]`

There is no package discrepancy. There is one naming hazard that the paper
dictionary must expose:

```text
project zero-based even carrier j = 2
<-> full spheroidal/Hermite degree n = 4
<-> production function P.h4
<-> production Fourier field P.chi2.
```

`P.chi2` must never be read as the paper degree-two scalar. `[ABSTRACT][LEAN]`

### 2. Exact project-to-paper parameter dictionary

For each cofinal index `k`, define

\[
m_k:=k+2,\qquad \lambda_k:=\sqrt{m_k},\qquad
\gamma_k:=2\pi\lambda_k^2=2\pi m_k.
\]

The exact dictionary is:

| Layer | Project object | Paper object | Exact law | Tags |
|---|---|---|---|---|
| carrier | zero-based even index `j` | full degree `n` | `n=2*j`; `j=0,2` gives `n=0,4` | `[ABSTRACT][LEAN]` |
| coordinate | physical `u` | spheroidal `z` | `z=u/lambda_k` | `[ABSTRACT][LEAN]` |
| window | `P.pw.lambda` | paper `lambda` | `lambda_k=sqrt(k+2)` | `[COFINAL_FAMILY][LEAN]` |
| bandwidth | `mode4SlepianC m_k` | `gamma_k` | `gamma_k=2*pi*lambda_k^2` | `[COFINAL_FAMILY][LEAN]` |
| ODE square | `mode4JacobiG m_k` | `gamma_k^2` | literal equality | `[COFINAL_FAMILY][LEAN]` |
| spheroidal order | even Legendre recurrence | `m_sph` | `m_sph=0` | `[ABSTRACT][PAPER]` |
| differential value | `mode4ClassicalEvenEigenvalue G j` | `lambda_n^0(gamma^2)` | same separation value | `[COFINAL_FAMILY][PAPER]` |
| physical PW value | RHS of physical ODE | eigenvalue of `PW_lambda` | `Lambda_{j,k}+gamma_k^2` | `[COFINAL_FAMILY][LEAN]` |

The project dimensionless equation is exactly

\[
\frac{d}{dz}\left((1-z^2)Y'(z)\right)
 +\left(\Lambda_{j,k}+\gamma_k^2(1-z^2)\right)Y(z)=0.
\]

Thus the project parameter `Lambda` is the source spheroidal separation value,
while `Lambda + gamma^2` is the eigenvalue of the physical prolate-wave
operator. These two values must not be merged. `[ABSTRACT][LEAN]`

### 3. Function and normalization dictionary

Let

\[
Y_{j,k}(z):=
\operatorname{mode4FerrersSeries}(S_{j,k}.\mathrm{coefficients})(z).
\]

The project physical unit-`L2` mode is

\[
f^{\mathrm{proj}}_{j,k}(u)
=
\frac{\mathbf 1_{[-\lambda_k,\lambda_k]}(u)
      Y_{j,k}(u/\lambda_k)}
     {\mathrm{physicalL2Normalization}(S_{j,k})}.
\]

This is exactly the function stored in `P.h0` for `j=0` and in `P.h4` for
`j=2`. `[COFINAL_FAMILY][LEAN]`

CCM uses the Meixner--Schäfke representatives

\[
h^{\mathrm{paper}}_{n,\lambda}(u)
=
s_n\lambda^{-1/2}
  \operatorname{ps}^{0}_{n}(u/\lambda;\gamma^2),
\qquad n\in\{0,4\}.
\]

From CCM equations (7.10)--(7.11), with
`gamma=2*pi*lambda^2`, the fixed constants are

\[
s_0=\frac1{\sqrt2},\qquad
s_4=\frac3{\sqrt2}.
\]

These constants are the **individual fixed-mode Satz-9 normalization**. They
do not contain the later factor `4`. `[ABSTRACT][PAPER]`

The exact load-bearing identity still missing from the current Lean corpus is:

\[
\boxed{
\exists a_{j,k}\in\mathbb R^{\times}\;\forall |u|\le\lambda_k,
\quad
a_{j,k}f^{\mathrm{proj}}_{j,k}(u)
=
h^{\mathrm{paper}}_{2j,\lambda_k}(u)
}
\]

for `j=0,2`, with the scalar orientation fixed by the source representative,
not fitted after numerical inspection. Once the literal paper representative
is available, the canonical signed scalar is

\[
a_{j,k}
:=
\frac{h^{\mathrm{paper}}_{2j,\lambda_k}(0)}
     {f^{\mathrm{proj}}_{j,k}(0)},
\]

because the project center value is already nonzero. `[COFINAL_FAMILY][CONDITIONAL]`

The repository proves uniqueness only among two already-packaged project
Ferrers solutions at the same parameters and normalization. It explicitly
does not identify that package with an external DLMF/Meixner--Schäfke
function. Therefore the displayed identity cannot be manufactured by naming
the project mode `ps_n`. `[ABSTRACT][LEAN]` **[C04] [C10]**

### 4. Fourier and Fuchs notation firewall

The project plus kernel is `exp(+2*pi*I*x*y)`. Under
`u=lambda*t`, `v=lambda*s`, it becomes

\[
e^{2\pi iuv}=e^{i\gamma ts},
\qquad \gamma=2\pi\lambda^2.
\]

A dimensionless scalar `mu_n` becomes the physical scalar `lambda*mu_n`.
For full degrees `n=0,4`, the paper finite-Fourier scalars correspond to

```text
paper chi_0(lambda) <-> project P.chi0,
paper chi_4(lambda) <-> project P.chi2.
```

This is an alias dictionary only. It does not import Fuchs's asymptotic
estimate. `[COFINAL_FAMILY][PAPER]`

The inaccessible Fuchs PDF therefore does not block F72.0. It blocks only the
exact theorem-scope audit for F72.3. The DOI and bibliographic identity are
confirmed, but the theorem body is not treated as available evidence.
`[ABSTRACT][PAPER]`

### 5. Scalar firewall: the factor `4`

The factor `4` occurs zero times in the individual mode dictionary and exactly
once after the zero-mass combination is transferred to the port convention:

\[
\operatorname{portSourceScale}_k
=4\,\operatorname{lemma72Scale}_k.
\]

It must not be inserted into `s_0`, `s_4`, either individual `a_{j,k}`, the
coordinate map, or the finite-Fourier scalar. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

Repair F72.0 into two layers.

### F72.0A — project parameter/index lock

This is the actual first Lean node. It proves only the exact project-side
formulas:

```text
m_k=N_k=k+2;
K_k=5*(k+2);
lambda_k=sqrt(k+2);
gamma_k=2*pi*lambda_k^2=2*pi*(k+2);
gamma_k^2=mode4JacobiG(k+2);
j=0,2 <-> n=0,4;
P.h0/P.h4 and P.chi0/P.chi2 use those same selected witnesses.
```

It closes a real object/parameter edge and opens no analytic supplier.
`[COFINAL_FAMILY][LEAN]`

### F72.0B — literal fixed-mode representative bind

This is the remaining source theorem:

```text
SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE
```

It must bind the same selected functions to the literal
`ps_0^0`/`ps_4^0` convention up to a source-derived nonzero scalar. It is not a
definitional alias and not an assumption carrying the desired equality.
`[COFINAL_FAMILY][CONDITIONAL]`

After F72.0B, F72.1 may consume Satz 9 directly. F72.2 then assembles the
zero-mass combination, and only F72.5 inserts the single factor `4` for the
port convention. `[COFINAL_FAMILY][CONDITIONAL]`

### Candidate re-representations

1. **R1 — literal fixed-mode source bind.** Define or import the exact paper
   representatives, then use a specialized regular-eigenspace uniqueness
   theorem to obtain the scalar. **Kill power 10/10; cost 5/10.**
   `[COFINAL_FAMILY][CONDITIONAL]`

2. **R2 — direct project-mode rate with an existential scalar.** Avoid a
   persistent `ps_n` object and prove the transferred Satz-9 estimate directly
   for the selected project modes:
   \[
   \exists a_{n,k}\ne0,\quad
   \|a_{n,k}f^{\mathrm{proj}}_{n,k}-h_n\|_\infty
   \le C\lambda_k^{-2}.
   \]
   This merges the representative bind into F72.1 while keeping the scalar
   source-derived and precommitted. **Kill power 9/10; cost 7/10.**
   `[COFINAL_FAMILY][CONDITIONAL]`

**Discriminator:** a valid implementation must prove a non-tautological
source identity or the direct rate without defining the paper representative
to be the project function and without adding an equality hypothesis whose
conclusion is the target. A zero-information alias is a C10 kill.

Registered prediction: R1 is cheaper if a fixed-mode source representative is
materialized; otherwise R2 will be the first executable analytic theorem.

## STRONGEST ATTACK

The strongest reviewer objection is:

> The project function and `ps_n^0` satisfy the same-looking ODE and carry the
> same label. Why is the dictionary not already proved?

Because equality of notation is not equality of objects. Every nonzero scalar
multiple has the same ODE, zero set, parity, and spectral value. The current
project uniqueness theorem compares only two instances of the project
structure with the project's own coefficient normalization. It does not place
an external Meixner--Schäfke representative inside that structure. `[C04]`

The fatal shortcut would be:

```text
def paperPS := selectedProjectMode
```

followed by an assertion that Satz 9 applies. This replaces the source object
with a surrogate selected for convenience and makes the dictionary
circular. `[C10]`

The weakest valid repair is either R1 or R2 above. Failure to obtain the
literal bind does not negate the fixed-mode rate; it only blocks this
particular representation of the rate theorem.

## CODEX DIRECTIVE

```text
TASK: F72_0A_SELECTED_FERRERS_PROJECT_PARAMETER_DICTIONARY

Create exactly one new file:
  Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean

Direct imports only:
  G6N1SelectedFerrersPreAnchorDataInhabitant
  D0Mode4FerrersDimensionlessFourierScaling

Prove and export the project-side dictionary only:

1. selectedFerrersPaperDegree j := 2*j.
2. selectedFerrersPaperLambda k := sqrt(k+2).
3. selectedFerrersPaperGamma k := 2*pi*(selectedFerrersPaperLambda k)^2.
4. gamma = 2*pi*(k+2).
5. gamma^2 = mode4JacobiG(k+2).
6. degree(0)=0 and degree(2)=4.
7. selectedFerrersPreAnchorPair k has the same lambda and the exact
   S0/S4 identities already exported by pair_spec/data_pair_spec.

Mandatory W9 ledger in the source header:
  CLOSES:
    - SELECTED_FERRERS_PROJECT_PARAMETER_INDEX_DICTIONARY
  OPENS: []

Forbidden:
  - do not define ps_n or paper h_n,lambda;
  - do not state project mode = scalar * ps_n;
  - do not add Satz-9 or Fuchs assumptions;
  - do not introduce factor 4;
  - do not touch CCMLemma73PreAnchorPort;
  - do not touch F72.1 or F72.3;
  - no sorry/admit/custom axiom/native_decide.

Validation:
  lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean
  lake build Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersPaperParameterDictionary.lean

Success:
  F72_0A_SELECTED_FERRERS_PROJECT_PARAMETER_DICTIONARY_LEAN
  with exactly [propext, Classical.choice, Quot.sound].

Failure:
  F72_0A_PROJECT_PARAMETER_DICTIONARY_KERNEL_MISMATCH
```

No second execution target is authorized in this verdict.

## META CLOSEOUT

**What became smaller?**

F72.0 is no longer a vague paper-to-project bridge. All carrier, degree,
coordinate, bandwidth, ODE, physical scaling, and factor-placement rows are
fixed. One source identity remains.

**What was killed?**

- reading `P.chi2` as the degree-two paper scalar;
- using `gamma=2*pi*lambda` or `gamma=G`;
- identifying the physical PW eigenvalue with project `Lambda` instead of
  `Lambda+G`;
- inserting the factor `4` into individual modes;
- defining the paper function as a project surrogate;
- treating the Fuchs paywall as a blocker for F72.0.

**What must not be tried again?**

Do not infer the external normalization from the shared ODE, from the names
`h0/h4`, or from project unit-`L2` normalization alone.

**Current smallest named gap:**

```text
SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE
```

**Next cheapest decisive test:**

Compile F72.0A, then ask whether the literal source representative can be
materialized without an assumption carrying the target equality. If not,
select R2 and move the scalar bind into the direct rate theorem.

**Fate of registered predictions:**

```text
P_G_D1: CONFIRMED.
  Package D has no source/index/provenance discrepancy.

P_G_D2: CONFIRMED.
  The remaining load-bearing row is the literal paper-function bind.

P_G_D3: CONFIRMED.
  The factor 4 belongs only to the later port-combination layer.

P_G_D4: CONFIRMED.
  Fuchs access affects F72.3 scope, not F72.0.

Prior FIRST_BY_COST_AFTER_D_PUSH:
  PARTIALLY_CONFIRMED_WITH_REPAIR.
  F72.0A is the first cheap Lean node; the full literal F72.0 is not yet a
  Lean-closed theorem.
```

```yaml
iteration:
  target: F72.0 selected Ferrers paper object dictionary
  status: PROGRESS
  failed_strategy: infer_external_ps_identity_from_same_ODE_and_names
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: SELECTED_FERRERS_TO_SATZ9_REPRESENTATIVE
  invariant_learned: "same selected witness, n=2*j, gamma=2*pi*lambda^2, source-derived scalar, factor 4 exactly once later"
  forbidden_future_move: tautological_ps_alias_or_factor_four_in_individual_mode
  next_decisive_test: compile_project_parameter_dictionary_then_test_non_tautological_source_bind
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
