# STATUS: OPEN — R1 STOP_RULE FIRED; THE RICCI/DOOB CONNECTION IS ONE-WAY, NOT A DECISION PROCEDURE

```yaml
PRIMARY: RATIFY_LOCAL_COUNT_HOLD_REJECT_SIGN_PATTERN_REDUCTION_RETURN_TO_OWNER
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-28-R1A

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 5c5a5bef6224a3cb69ecfe3fa9b23c51ddeb276a
  REPORT_PATH: docs/routeB_bus/LINUX_R1_LOCAL_SPECTRAL_COUNT_PREFLIGHT_GOAL058_2026-08-28.md
  PRIOR_LOCAL_COUNT_VERDICT: afd27ddfba21661ef77672c4bd0dd3d1d665106c
  PRIOR_SIGN_GATE_VERDICT: 3f4c23eb8be0661223ce2732aa053b6c88ad3507
  CORRECTION_5: a4bcf77722dd37fe537fe25ace343a3b4e504028
  HEAD_AT_ADJUDICATION: 5c5a5bef6224a3cb69ecfe3fa9b23c51ddeb276a

MODE:
  REPORT: PAPER_SOURCE_AND_DECLARED_DIAGNOSTIC_NUMERICS
  JUDGE: PAPER_AND_EXACT_SYMBOLIC_PLANTS
  LEAN_EDIT: false
  NUMERICAL_PROBE: false
  ARISTOTLE: false
  CODEX: false

ADJUDICATION:
  EXTERIOR_LATTICE_ESCAPE: RATIFIED
  INCLUDED_LATTICE_ZERO_IFF_COEFFICIENT_ZERO: RATIFIED
  OFF_LATTICE_SECULAR_REPRESENTATION: RATIFIED

  ALL_RESIDUES_ONE_SIGN_STRICT_INTERLACING:
    status: PAPER_PASS
    guards:
      - every_included_residue_nonzero
      - literal_source_coordinates
    consequence: exactly_one_zero_per_adjacent_pole_gap

  ALL_RESIDUES_ONE_SIGN_IMPLIES_R1_FATAL:
    status: CONDITIONAL_COFINAL_PASS
    guards:
      - one_sign_for_cofinally_many_selected_cells
      - selected_schedule_L_to_infinity
      - compact_tight_nonzero_normalization

  SIGN_PATTERN_ALONE_DETERMINES_LOCAL_ZERO_COUNT:
    status: REFUTED_BY_EXACT_EVEN_ETA_NORMALIZED_REAL_ROOTED_PLANT

  MIXED_SIGNS_IMPLY_LOCAL_COUNT_TIGHTNESS:
    status: false

  SELECTED_GROUND_VECTOR_COEFFICIENT_SIGN_PATTERN_AS_DECISIVE_GATE:
    status: REJECTED
    reason: one_sign_is_sufficient_for_divergence_but_mixed_sign_is_not_sufficient_for_tightness

  RICCI_DOOB_PASS_IMPLIES_SOURCE_ONE_SIGN:
    status: CONDITIONAL_ONE_WAY_KILL
    required_guards:
      - all_negative_sign_is_in_literal_source_coordinates_or_identity_gauge
      - nonzero_offdiagonal_support_graph_connected
      - selected_vector_is_the_lowest_eigenvector
    source_specific_repair: >-
      Under odd pairwise-distinct beta, the prior paper reduction makes a strict
      sign-gate PASS equivalent to beta strictly decreasing, so the identity
      gauge works and Perron-Frobenius gives a strictly one-signed source ground.

  RICCI_DOOB_FAIL_IMPLIES_MIXED_SIGN_GROUND:
    status: REFUTED_BY_EXACT_ODD_LOEWNER_PLANT

  RICCI_DOOB_GATE_EQUIVALENT_TO_GROUND_SIGN_PATTERN:
    status: false

  REPORT_DISCRIMINATOR:
    reported: HOLD
    code: R1_ZERO_DIVISOR_EXACT_BUT_LOCAL_FINITE_SPECTRUM_UNCONTROLLED
    decision: RATIFIED_AFTER_REJECTING_THE_SIGN_PATTERN_REDUCTION

R1_STATUS:
  GENERIC_GLOBAL_GAUGE: FATAL_PREVIOUSLY
  LITERAL_LOCAL_SPECTRAL_COUNT: OPEN
  CURRENT_EXECUTABLE_PROGRAM: CLOSED_BY_PRECOMMITTED_ONE_HOLD_STOP_RULE
  MATHEMATICAL_R1_EXISTENCE: NOT_REFUTED
  OWNER_REPRESENTATION_RERANK: REQUIRED
  NEW_TRANSACTION_AUTHORIZED: false

MINIMAL_MISSING_IDENTITY:
  name: SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
  statement: >-
    For every compact real interval I, the multiplicity-counted number of
    finite perturbed-scaling eigenvalues of the literal selected ground cell in
    I is eventually bounded independently of k.

CANDIDATE_REPRESENTATIONS:
  R1_FINITE_GROUND_SPECTRAL_COUNTING_MEASURE:
    object: nu_k=sum multiplicity(t)*delta_t over the literal perturbed spectrum
    kill_power: 10/10
    proof_cost: 7/10
    authorization: OWNER_ACQUISITION_ONLY
  R2_RELATIVE_PERTURBATION_DETERMINANT_CAUCHY_INDEX:
    object: >-
      det(Dprime_k-s)/det(D_k-s), with the free lattice divided out and the
      local root count read by an exact Cauchy-index or argument-principle ledger
    kill_power: 10/10
    proof_cost: 8/10
    authorization: OWNER_ACQUISITION_ONLY

CLOSES:
  - SIGN_PATTERN_ALONE_DECIDES_LOCAL_ZERO_COUNT
  - RICCI_DOOB_FAIL_RESCUES_R1
  - RICCI_DOOB_GATE_IS_EQUIVALENT_TO_LITERAL_GROUND_SIGN_PATTERN

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
  - SELECTED_CCM_RICCI_DOOB_ACTUAL_SIGN_FRUSTRATION
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR

REGISTERED_PREDICTION_CLOSEOUT:
  P_R1_ZERODENSITY_1_0_98: CONFIRMED
  P_R1_ZERODENSITY_2_0_76: CONFIRMED
  P_R1_ZERODENSITY_3_0_42: NOT_TESTED
  P_RICCI_2_0_76: REMAINS_UNTESTED

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| Exterior lattice zeros escape on `m=N=k+2` | Ratified. | `[COFINAL_FAMILY][PAPER]` |
| Included lattice node is a zero iff its source coefficient is zero | Ratified. | `[FINITE_CELL][PAPER]` |
| One-signed nonzero residues give one secular zero per lattice gap | Ratified. | `[FINITE_CELL][PAPER]` |
| The sign pattern alone determines the local zero count | Refuted by an exact source-shaped plant. | `[ABSTRACT][PAPER]` |
| Mixed signs save R1 | Not proved and false as an inference. | `[COFINAL_FAMILY][PAPER]` |
| Doob sign-gate PASS can kill R1 | Yes, but only with source-coordinate, connectivity and cofinal guards. | `[COFINAL_FAMILY][CONDITIONAL]` |
| Doob sign-gate FAIL saves R1 | Refuted. | `[ABSTRACT][PAPER]` |
| Literal local spectral-count tightness | Still open. | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. What the report closed correctly

The report accepts the two necessary repairs from the preceding verdict.
Inside the finite carrier the P59 lattice nodes are removable evaluation points,
not automatic zeros, and the exterior free lattice escapes every fixed compact
on the selected schedule.

Away from the included lattice, the remaining zeros are zeros of the literal
secular function

\[
S_\xi(s)=\sum_j\frac{\xi_j}{j-s},
\]

equivalently roots of the source Lagrange polynomial or eigenvalues of the
finite corrected scaling object.

If every residue is strictly positive, then on every pole gap

\[
S_\xi'(s)=\sum_j\frac{\xi_j}{(j-s)^2}>0.
\]

The limits at the two ends of the gap are `-infinity` and `+infinity`, so there
is exactly one zero in each gap.  The same conclusion holds after a global sign
reversal.  Since a fixed `z`-interval corresponds to an `s`-interval of length
asymptotic to `L_k |I|/(2*pi)`, a cofinal one-signed ground family has unbounded
local zero count.  The reverse-Hurwitz plant then kills every locally bounded,
compact-tight zero-free gauge.

Thus one-sign is a valid **sufficient R1 kill certificate**.

## 2. Exact plant: sign pattern does not determine the zero count

The report overreaches when it says the local count is determined entirely by
the signs of `xi`.

Take the same five poles

\[
-2,-1,0,1,2
\]

and the two even, nonzero, eta-normalized residue rows

\[
\xi^{A}=\frac1{6}(1,-1,6,-1,1),
\qquad
\xi^{B}=\frac1{21}(11,-1,1,-1,11).
\]

They have the same sign pattern

```text
+ - + - +
```

and every residue is nonzero.  Clearing the common denominator gives, up to the
same irrelevant denominator orientation,

\[
D(s)S_{\xi^A}(s)=-(s^2-2)^2,
\]

\[
D(s)S_{\xi^B}(s)
=-\frac1{21}(3s^2-1)(7s^2-4).
\]

Both zero sets are entirely real.  But `xi^A` has no zero in `(-1,1)`, while
`xi^B` has four:

\[
\pm\frac1{\sqrt3},
\qquad
\pm\frac2{\sqrt7}.
\]

The plant preserves every property used by the proposed reduction:

```text
evenness;
eta normalization;
nonzero residues;
identical sign pattern;
real-rooted secular numerator.
```

Therefore the exact local count depends on residue magnitudes and their coupled
secular polynomial, not on the sign pattern alone.

This is a direct C10 kill: `sign(xi)` is a useful surrogate for one special
monotone regime, not the local spectral-count functional consumed by R1.

## 3. The Ricci/Doob connection is real but one-way

There is a valid implication behind the report.

If the literal source matrix itself has strictly negative off-diagonal entries
and the nonzero support graph is connected, Perron-Frobenius applied after a
large scalar shift gives a strictly positive lowest eigenvector.  Under the
previous source-specific paper reduction, odd pairwise-distinct `beta` passes
the strict all-negative sign gate only when `beta` is strictly decreasing; in
that case the **identity gauge** already works.  Hence:

```text
strict source Doob PASS
+ connectivity
+ cofinal validity
→ one-signed literal ground
→ one zero per pole gap
→ dense local zeros
→ R1 FATAL.
```

But none of these arrows is reversible.

A nontrivial diagonal sign gauge makes the ground vector positive only in the
gauged coordinates.  The P59 residues remain the coefficients in the literal
source coordinates unless an exact transform gauge adapter is proved.  This is
C04: positivity after a forgetful coordinate switch is not positivity of the
consumer's residues.

More decisively, failure of the sign gate does not imply a mixed-sign ground.

### Exact odd-Loewner plant

Use ordered nodes

\[
n=(-2,-1,0,1,2)
\]

and the reflection-odd field

\[
\beta=(1,-1/4,0,1/4,-1).
\]

For `i != j`, set

\[
K_{ij}=\frac{\beta_i-\beta_j}{n_i-n_j},
\]

and choose the diagonal so every row sum is zero.  The resulting centrosymmetric
matrix is

\[
K=
\begin{pmatrix}
5/2&-5/4&-1/2&-1/4&-1/2\\
-5/4&1&1/4&1/4&-1/4\\
-1/2&1/4&1/2&1/4&-1/2\\
-1/4&1/4&1/4&1&-5/4\\
-1/2&-1/4&-1/2&-5/4&5/2
\end{pmatrix}.
\]

Its spectrum is

\[
0,
\qquad
\frac{15-\sqrt{145}}8\ \text{with multiplicity }2,
\qquad
\frac{15+\sqrt{145}}8\ \text{with multiplicity }2.
\]

Thus the unique lowest line is generated by the strictly positive vector
`(1,1,1,1,1)`.

Nevertheless the triangle on nodes `(0,1,2)` has off-diagonal signs

\[
1/4,\quad -5/4,\quad -1/2
\]

and positive cycle product.  No diagonal sign switch can make every nonzero
off-diagonal entry negative.

So even inside the exact odd-beta Loewner off-diagonal class:

\[
\boxed{
\text{Doob sign-gate FAIL}
\not\Rightarrow
\text{mixed-sign lowest eigenvector}.
}
\]

The actual CCM diagonal may carry additional source information.  The plant does
not refute a future theorem using that additional information.  It refutes the
claimed equivalence and any inference based only on the current sign gate.

## 4. Correct status of the report

The reported `HOLD` code is correct:

```text
R1_ZERO_DIVISOR_EXACT_BUT_LOCAL_FINITE_SPECTRUM_UNCONTROLLED
```

The proposed replacement gap

```text
SELECTED_GROUND_VECTOR_COEFFICIENT_SIGN_PATTERN
```

is not accepted as the minimal gap.  It gives one sufficient kill branch and no
sufficient survival branch.

The minimal missing identity therefore remains exactly the one precommitted in
`afd27ddf`:

```text
SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS.
```

No source theorem currently supplies it.

## FINAL PROPOSAL

The prior verdict registered a hard stop:

```text
one HOLD returns to the judge for R1 closeout or owner rerank.
```

That HOLD has now occurred.  The stop fires.

No Herglotz wrapper, Ricci run, sign-pattern probe, Lean node, numerical ladder,
Aristotle submission or Codex transaction is authorized by this verdict.

The owner must choose one of two acquisitions:

1. acquire a genuine theorem controlling the literal finite spectral-counting
   measures on every fixed compact; or
2. rerank away from R1, including the previously banked source-adapted moving
   Krylov/Feshbach representation if desired.

A cofinal proof of strict source-beta decrease would be accepted only as a
**one-way R1 kill certificate**.  It would not be an R1 construction.

## STRONGEST ATTACK

The strongest objection to this closeout is:

> Perhaps the literal CCM ground vector is mixed-sign, and therefore the local
> count is bounded even though no theorem says so.

Mixed signs do not imply bounded count.  The exact five-pole plant above gives
the same mixed sign pattern with zero or four roots in the same compact interval.
A belief about signs therefore cannot occupy the missing cofinal quantifier.

The repaired weakest statement is:

\[
\text{one-signed residues}
\Longrightarrow
\text{maximal interlacing and R1 death}.
\]

Nothing stronger is currently justified.

## CODEX DIRECTIVE

```text
NO EXECUTION AUTHORIZED.

CONTROL_STATE:
  OWNER_REPRESENTATION_RERANK

DO NOT:
  - run a Ricci/Doob sign experiment as an R1 rescue;
  - infer local count from a sign pattern;
  - launch another Montel/Herglotz wrapper;
  - promote model-row numerics;
  - write Lean for the secular sign surrogate;
  - reopen the stopped quantitative tracking corridor without owner scope.
```

## META CLOSEOUT

**What became smaller?**

The alleged new gap `sign(xi)` was removed.  The exact remaining object is again
the literal local spectral-counting measure.

**What was killed?**

```text
sign pattern alone decides the count;
mixed signs save R1;
Doob FAIL implies mixed ground;
the Ricci sign gate is equivalent to the R1 count gate.
```

**What must not be tried again?**

Another wrapper around sign patterns, Herglotz measures or Ricci geometry without
a direct theorem on the literal local count.

**Current smallest named gap?**

```text
SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
```

**Next cheapest decisive test?**

An owner-authorized source acquisition for a theorem directly controlling
`nu_k(I)`.  No intermediate sign surrogate qualifies.

**Prior predictions?**

```text
P_R1_ZERODENSITY_1: confirmed.
P_R1_ZERODENSITY_2: confirmed.
P_R1_ZERODENSITY_3: not tested.
P_RICCI_2: remains untested.
```

**Memory entry:**

```yaml
iteration:
  target: SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
  status: OPEN
  failed_strategy: SIGN_PATTERN_AND_RICCI_GATE_AS_COUNT_DECIDER
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
  invariant_learned: local_zero_count_depends_on_the_full_secular_polynomial_not_only_residue_signs
  forbidden_future_move: use_Doob_FAIL_or_mixed_signs_as_a_local_count_bound
  next_decisive_test: owner_acquisition_of_a_direct_local_spectral_measure_theorem
```
