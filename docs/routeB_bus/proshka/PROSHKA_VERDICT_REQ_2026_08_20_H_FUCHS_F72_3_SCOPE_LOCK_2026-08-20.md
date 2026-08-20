# STATUS: CONDITIONAL — REQ-H SCOPE-LOCKS F72.3 EXACTLY; THE PROJECT LEAN PORT REMAINS OPEN

```yaml
PRIMARY: F72_3_FUCHS_PROJECT_CROSSWALK_SCOPE_LOCKED
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-20-H

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: 829a34a59897769d38f3f8ef47df69a16f083055
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  FUCHS_PDF_PATH: docs/routeB_bus/litreview/pdfs/fuchs_1964_bandlimited_eigenvalues.pdf
  FUCHS_PDF_LFS_OID_SHA256: f86d5759248729fa56a30d2c9231c8acb9dd5c9cdea6a320acd7adf821c29cb3
  FUCHS_USAGE_CARD: docs/routeB_bus/litreview/FUCHS_1964_USAGE_CARDS.md
  CCM_PAPER: arXiv:2511.22755
  CCM_USAGE_CARD: docs/routeB_bus/litreview/CCM_ZST_USAGE_CARDS.md
  PROJECT_KERNEL: q3.lean.aristotle/Q3/Proofs/RouteB/ProlateSourceRegularity.lean
  PROJECT_SCALING: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersDimensionlessFourierScaling.lean
  PROJECT_PAIR: q3.lean.aristotle/Q3/Proofs/RouteB/D0ModeZeroFourFerrersProductionProlatePair.lean

SOURCE_VERIFICATION:
  fuchs_lfs_pointer_hash_matches_queue: true
  fuchs_primary_text_consumed_via_owner_verified_usage_card: true
  fuchs_pdf_bytes_independently_rendered_by_judge: false
  ccm_page_30_formula_independently_screenshot_checked: true

DELIVERY:
  DOC_ONLY: true
  LEAN_WRITTEN: false
  CODEX_REDIRECTED: false
  ARISTOTLE_CALLED: false

CLOSES:
  - F72_3_FUCHS_SCOPE_LOCK_FOR_N0_AND_N4
  - F72_3_WINDOW_PARAMETER_CONVERSION
  - F72_3_EIGENVALUE_CATEGORY_CONVERSION
  - F72_3_PROJECT_ASYMPTOTIC_CONSTANTS
  - FALSE_DIRECT_IDENTIFICATION_FUCHS_LAMBDA_EQ_PROJECT_CHI
  - FALSE_PARAMETER_IDENTIFICATION_FUCHS_A_EQ_PROJECT_LAMBDA
OPENS: []

CROSSWALK:
  scale_r: sqrt(2*pi)
  project_window: [-lambda, lambda]
  fuchs_window: [-a, a]
  a: sqrt(2*pi) * lambda
  fuchs_c: a^2
  project_gamma: 2*pi*lambda^2
  parameter_identity: fuchs_c = project_gamma
  unitary_rescale: U_lambda(h)(s) = (2*pi)^(-1/4) * h(s/sqrt(2*pi))
  operator_intertwining: F_a(U_lambda h) = sqrt(2*pi) * U_lambda(T_lambda h)
  project_operator: T_lambda h(x) = integral_[-lambda,lambda] exp(i*2*pi*x*y) h(y) dy
  fuchs_operator: F_a f(t) = integral_[-a,a] exp(i*s*t) f(s) ds

EIGENVALUE_MAP:
  fuchs_relation: F_a f_n = i^n * mu_n * f_n
  fuchs_concentration: Lambda_n = abs(mu_n)^2 / (2*pi)
  degree_zero: sqrt(2*pi) * chi0_Q3 = mu_0
  degree_four: sqrt(2*pi) * chi2_Q3 = mu_4
  slot_warning: project_chi2_corresponds_to_Fuchs_degree_4
  squared_map_zero: Lambda_0 = chi0_Q3^2
  squared_map_four: Lambda_4 = chi2_Q3^2
  positive_branch_required: true
  positive_branch_source: n_in_{0,4}_and_Fuchs_mu_n_positive_convention

FUCHS_THEOREM_1:
  formula: 1-Lambda_n ~ 4*sqrt(pi)*8^n/n!*a^(2*n+1)*exp(-2*a^2)
  fixed_mode_scope: all_n
  selected_modes_covered: [0, 4]
  ordering_repair_needed: false

PROJECT_ASYMPTOTICS:
  chi0: 1-chi0_Q3 ~ 2*sqrt(2)*pi*lambda*exp(-4*pi*lambda^2)
  chi2: 1-chi2_Q3 ~ (2^14/3)*sqrt(2)*pi^5*lambda^9*exp(-4*pi*lambda^2)
  common_weak_output: abs(1-chi0_Q3), abs(1-chi2_Q3) <= C_chi*lambda^(-2) eventually

CCM_FORMULA_CORRECTION:
  old_misread: (2^14/3)*sqrt(2*pi)*lambda^5*exp(-4*pi*lambda^2+9*log(lambda))
  correct_visual_read: (2^14/3)*sqrt(2)*pi^5*exp(-4*pi*lambda^2+9*log(lambda))
  equivalent_correct_form: (2^14/3)*sqrt(2)*pi^5*lambda^9*exp(-4*pi*lambda^2)
  action: supersede_formula_only_do_not_edit_closed_verdict

F72_3_STATUS:
  paper_scope: PROVED_FROM_SOURCE_CARD
  exact_crosswalk: PROVED_ON_PAPER_FROM_PROJECT_DEFINITIONS
  project_lean_theorem: OPEN
  independent_new_asymptotic_research: NOT_REQUIRED
  dependency_order_changed: false
  execution_priority_changed: true
  after_F72_0: run_in_parallel_with_F72_1

COST_REPAIR:
  prior_single_cost: 7/10
  paper_scope_uncertainty_now: 1/10
  exact_lean_scaling_crosswalk: 3/10
  weak_corollary_given_formal_Fuchs_input: 2/10
  full_Lean_reproof_of_Fuchs_if_required: 8/10
  dominant_L73_2_wall_remains: F72_1_MEIXNER_SCHAEFKE_FIXED_MODE_UNIFORM_RATE

DISCRIMINATOR:
  name: N4_CCM_CONSTANT_MATCH
  correct: (2^14/3)*sqrt(2)*pi^5*lambda^9*exp(-4*pi*lambda^2)
  wrong_a_eq_lambda: exponent_exp(-2*lambda^2)
  wrong_Lambda_eq_chi: leading_constant_is_twice_correct_value
  zero_consistent_result: INCONCLUSIVE

CANDIDATE_REPRESENTATIONS:
  R1_PHYSICAL_UNITARY_RESCALE:
    rank: PRIMARY
    kill_power: 10/10
    cost: 2/10
  R2_DIMENSIONLESS_MODE4SLEPIANC_THEN_FUCHS:
    rank: CROSS_CHECK
    kill_power: 9/10
    cost: 2/10

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT

NEXT_LOAD_BEARING_GAP: F72_1_MEIXNER_SCHAEFKE_FIXED_MODE_UNIFORM_RATE
NEXT_LOCAL_F72_3_GAP: F72_3A_FUCHS_PROJECT_OPERATOR_INTERTWINING

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_RELAY_PLUS_LEAN_SOURCE_AUDIT
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5
```

## ROUTE MAP

REQ-H is answered by an exact two-stage conversion. Fuchs's theorem is not
about the production finite-Fourier scalar directly. It is about the
energy-concentration eigenvalue of the sinc-kernel operator. The production
operator and Fuchs's finite Fourier operator are conjugate only after a fixed
change of units, and the concentration eigenvalue is the square of the
production transform eigenvalue.

The exact route is

```text
Q3 physical operator T_lambda, kernel exp(i*2*pi*x*y)
  -> unitary coordinate rescaling by sqrt(2*pi)
  -> Fuchs finite Fourier operator F_a, kernel exp(i*s*t)
  -> Fuchs concentration eigenvalue Lambda_n
  -> positive square root for degrees n=0,4
  -> project chi0 / chi2 asymptotics
  -> weak O(lambda^-2) output consumed by F72.4
```

`[COFINAL_FAMILY][PAPER]`

The dependency DAG does not change:

```text
F72.0 exact object dictionary
        |\
        | \----> F72.3 Fuchs defect port
        v
F72.1 Satz-9 mode rate
        |
        v
F72.2 physical/Hermite transport
        |\
        | \----> F72.4 integral rate <---- F72.3
        v
      F72.5 -> F72.6 -> L73.2
```

What changes is the work priority. F72.3 is no longer an independent analytic
research wall. After F72.0 it is a bounded units/eigenvalue port and may be
closed in parallel with F72.1. F72.1 remains the dominant external analytic
floor.

## EXACT WINDOW CROSSWALK

Write

\[
 r:=\sqrt{2\pi},\qquad a:=r\lambda.
\]

The production finite Fourier operator is

\[
 (T_\lambda h)(x)
 :=\int_{-\lambda}^{\lambda}e^{i2\pi xy}h(y)\,dy.
\]

Fuchs's finite Fourier operator is

\[
 (\mathcal F_a f)(t)
 :=\int_{-a}^{a}e^{ist}f(s)\,ds.
\]

Define the unitary scaling

\[
 (U_\lambda h)(s)
 :=r^{-1/2}h(s/r)
 =(2\pi)^{-1/4}h\!\left(\frac{s}{\sqrt{2\pi}}\right).
\]

A direct substitution `s = r*y` proves, with no asymptotic input,

\[
\boxed{
 \mathcal F_a U_\lambda
 =r\,U_\lambda T_\lambda.
}
\]

The window parameters therefore satisfy

\[
\boxed{
 a^2=2\pi\lambda^2.
}
\]

This is exactly the project quantity

\[
 \operatorname{mode4SlepianC}(mProject)
 =2\pi mProject
 =2\pi\lambda^2
\]

because the selected physical window has `lambda = sqrt(mProject)`.

Thus Fuchs's `c=a^2` is the project dimensionless bandwidth `gamma`; Fuchs's
`a` is not the project physical window radius `lambda`. `[ABSTRACT][LEAN_READY]`

## EXACT EIGENVALUE CROSSWALK

Suppose

\[
 T_\lambda h=\chi h.
\]

The intertwining identity gives

\[
 \mathcal F_a(U_\lambda h)=r\chi\,U_\lambda h.
\]

Fuchs writes the degree-`n` eigenrelation as

\[
 \mathcal F_a f_n=i^n\mu_n f_n
\]

and his concentration eigenvalue as

\[
 \Lambda_n=\frac{|\mu_n|^2}{2\pi}.
\]

For the selected degrees `n=0` and `n=4`, one has `i^n=1`. Under the exact
mode dictionary and Fuchs's positive `mu_n` convention,

\[
 \sqrt{2\pi}\,\chi_0^{Q3}=\mu_0,
 \qquad
 \sqrt{2\pi}\,\chi_2^{Q3}=\mu_4.
\]

The second project slot is named `chi2`, but its function is the physical
degree-four mode. Therefore

\[
\boxed{
 \Lambda_0=(\chi_0^{Q3})^2,
 \qquad
 \Lambda_4=(\chi_2^{Q3})^2.
}
\]

This is the category boundary that must remain visible. Directly writing
`Lambda_n = chi_n` is false. It would also produce a leading defect constant
twice the CCM value. **[C04]**

The positive branch is load-bearing. The squared identity alone does not imply
`chi -> +1`: the negative branch would converge to `-1`. The project-facing
crosswalk must therefore derive, not assume,

```text
0 < chi0_Q3 < 1;
0 < chi2_Q3 < 1.
```

For the exact degrees `0,4`, this follows from the Fuchs eigenvalue convention
and the factor `i^n=1`. It belongs inside the same crosswalk, not as a fitted
phase selected after observing convergence. **[C09]**

## PROJECT ASYMPTOTICS

Fuchs Theorem 1 gives, for every fixed nonnegative integer `n`,

\[
 1-\Lambda_n(a)
 \sim
 \frac{4\sqrt\pi\,8^n}{n!}
 a^{2n+1}e^{-2a^2}.
\]

Since `chi = sqrt(Lambda)` on the positive branch,

\[
 1-\chi
 =\frac{1-\Lambda}{1+\chi}
 \sim \frac12(1-\Lambda).
\]

Substituting `a=sqrt(2*pi)*lambda` gives the general fixed-mode formula

\[
 1-\chi_n^{Q3}(\lambda)
 \sim
 \frac{2^{4n+3/2}\pi^{n+1}}{n!}
 \lambda^{2n+1}e^{-4\pi\lambda^2}.
\]

For the two production slots this is

\[
\boxed{
 1-\chi_0^{Q3}(\lambda)
 \sim 2\sqrt2\,\pi\lambda e^{-4\pi\lambda^2},
}
\]

and

\[
\boxed{
 1-\chi_2^{Q3}(\lambda)
 \sim
 \frac{2^{14}}3\sqrt2\,\pi^5\lambda^9e^{-4\pi\lambda^2}.
}
\]

The second formula agrees exactly with the visually rendered CCM formula

\[
 \frac{2^{14}}3\sqrt2\,\pi^5
 e^{-4\pi\lambda^2+9\log\lambda}.
\]

It does not agree with the OCR-derived expression previously written in the
REQ-F verdict. The glyph after `sqrt(2)` is `pi^5`, not `sqrt(pi)*lambda^5`.
The old verdict is immutable; this verdict supersedes that formula only.

## WEAK PROJECT THEOREM

F72.4 does not need the sharp constants. The project-facing theorem should be
exactly:

```text
There exist C_chi >= 0 and k0 such that for every k >= k0,

  abs(1 - (D.pair k).chi0)
    <= C_chi * (D.pair k).pw.lambda^(-2),

  abs(1 - (D.pair k).chi2)
    <= C_chi * (D.pair k).pw.lambda^(-2).
```

For the precommitted schedule `lambda_k = sqrt(k+2)`, the right-hand side is
`C_chi/(k+2)`. The exponential estimates imply this with enormous margin.
No eigenvalue-ordering fallback is needed because Fuchs Theorem 1 covers both
fixed degrees directly.

A clean implementation may split F72.3 into:

```text
F72.3A  exact project/Fuchs operator intertwining and positive branch;
F72.3B  fixed-mode Fuchs asymptotic -> common eventual lambda^-2 bound.
```

This split is bookkeeping inside F72.3, not a new route input.

## COST AND ORDER

The exponential strength changes the cost classification, not the dependency
order.

- The paper-scope uncertainty is gone.
- The selected degrees `0,4` are covered directly.
- No ordering theorem is required.
- The exact constants are determined by two algebraic conversions.
- The weak `lambda^-2` consequence is trivial once the formal Fuchs input is
  available.

The former single estimate `7/10` mixed three different costs. The repaired
ledger is:

```text
paper acquisition/scope:              1/10, closed;
Lean units/operator crosswalk:         3/10;
weak corollary from a formal input:     2/10;
full Lean reproving of Fuchs Theorem 1: 8/10, only if demanded.
```

Therefore F72.3 may be executed immediately after F72.0 and in parallel with
F72.1. It does not move before F72.0 because mode identity and positive phase
must be source-locked first. F72.1 remains the main analytic wall.

## STRONGEST ATTACK

The strongest reviewer objection is:

> Fuchs controls the sinc-kernel energy eigenvalue. The project consumes a
> finite-Fourier transform scalar. Why does an estimate for one imply an
> estimate for the other with the claimed constant and sign?

The answer is not narrative similarity. It is the exact pair

\[
 \mathcal F_aU_\lambda=\sqrt{2\pi}\,U_\lambda T_\lambda,
 \qquad
 \Lambda_n=(\chi_n^{Q3})^2.
\]

Two planted failures certify the crosswalk:

1. Setting `a=lambda` changes the exponential from `exp(-4*pi*lambda^2)` to
   `exp(-2*lambda^2)`.
2. Setting `Lambda=chi` doubles the leading constant of `1-chi`; the degree-four
   result then fails the CCM formula.

A third guard checks the slot map:

```text
Fuchs degree 4 -> project chi2,
not a nonexistent project chi4 field.
```

## FINAL PROPOSAL

Ratify the physical unitary-rescaling representation R1.

1. Keep F72.0 as the exact selected-mode dictionary.
2. Prove the operator intertwining with the literal production kernel.
3. Derive the positive degree-`0/4` eigenvalue map.
4. Port only the fixed-mode consequence of Fuchs Theorem 1.
5. Export the common eventual `lambda^-2` bound consumed by F72.4.
6. Continue the main analytic effort on F72.1 / Meixner--Schaefke Satz 9.

The dimensionless route through `mode4SlepianC` is retained as an independent
cross-check. It must produce the same `a^2=gamma=2*pi*lambda^2` identity and the
same project constants before the port is accepted.

## CODEX DIRECTIVE

```text
NO LARGE LEAN EXECUTION FROM REQ-2026-08-20-H.

After F72.0 is materialized, the single next local target is:

  F72_3A_FUCHS_PROJECT_OPERATOR_INTERTWINING

Prove, for r = sqrt(2*pi), a = r*lambda and
U(h)(s) = r^(-1/2) * h(s/r):

  F_a (U h) = r * U (T_lambda h)

with:
  T_lambda kernel = exp(i*2*pi*x*y),
  F_a kernel      = exp(i*s*t).

Required outputs:
  a^2 = 2*pi*lambda^2;
  exact eigenvalue transport r*chi = i^n*mu;
  for n=0,4, Lambda_n = chi^2;
  explicit positive-branch obligation.

Forbidden:
  a := lambda;
  Lambda_n := chi;
  chi2 := Fuchs degree 2;
  fitted constants;
  importing the old misread CCM constant.

Validation when execution is authorized:
  direct Lean;
  target build;
  q3_check;
  public axiom profile = [propext, Classical.choice, Quot.sound].

Success code:
  F72_3A_FUCHS_PROJECT_OPERATOR_INTERTWINING_LEAN

Failure code:
  F72_3_PROJECT_FUCHS_UNIT_OR_PHASE_MISMATCH
```

## META CLOSEOUT

**What became smaller?**

F72.3 changed from an uncertain second asymptotic theory into one exact operator
intertwining, one square-root eigenvalue conversion, and a trivial weak
corollary of a source theorem.

**What was killed?**

```text
Fuchs a = project lambda;
Fuchs concentration eigenvalue = project chi;
Fuchs degree 4 = project chi4;
the OCR-derived CCM constant from the REQ-F verdict;
the n=0 ordering fallback.
```

**What must not be tried again?**

Do not move between the sinc-kernel energy eigenvalue and the finite-Fourier
scalar without the square. Do not fit the `sqrt(2*pi)` scale from numerical
data. Do not read the compact CCM formula from parsed PDF text when the rendered
page is available.

**Current smallest named gap:**

```text
F72_3A_FUCHS_PROJECT_OPERATOR_INTERTWINING
```

The route-wide load-bearing gap remains:

```text
F72_1_MEIXNER_SCHAEFKE_FIXED_MODE_UNIFORM_RATE.
```

**Next cheapest decisive test:**

Prove the intertwining twice: directly in physical coordinates and through
`mode4SlepianC`. The two routes must yield the same `sqrt(2*pi)` eigenvalue
factor and the same degree-four constant.

**Fate of prior registered predictions:**

```text
Fuchs covers both n=0 and n=4 directly:
  CONFIRMED.

An ordering repair might be required for n=0:
  REFUTED; no repair is needed.

F72.1 will dominate the Lean proof cost:
  CONFIRMED.

After the two rate suppliers, the zero-mass combination is finite-dimensional
stability:
  STILL PENDING; REQ-H introduces no contrary evidence.
```

**Memory entry:**

```text
iteration: REQ-2026-08-20-H
target: F72.3 finite-Fourier eigenvalue defect rate
status: PROGRESS
failed_strategy: direct identification across conventions
cognitive_operator_used: UNIT_AUDIT
new_gap_name: F72_3A_FUCHS_PROJECT_OPERATOR_INTERTWINING
invariant_learned: concentration eigenvalue = transform scalar squared
forbidden_future_move: guess 2*pi or square-root factors
next_decisive_test: two-route exact intertwining cross-check
```
