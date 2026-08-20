# STATUS: OPEN — L73.2 HAS TWO ANALYTIC CORES, NOT ONE: SATZ 9 PLUS A FOURIER-EIGENVALUE DEFECT RATE

```yaml
PRIMARY: DECOMPOSE_L73_2_SELECTED_FERRERS_LEMMA72_RATE
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-20-F

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: a43b9529b83e300fa73a5060c762e3dc7b478b9f
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  PREVIOUS_FLOORS_VERDICT: docs/routeB_bus/proshka/PROSHKA_VERDICT_CCM_LEMMA_7_3_PREANCHOR_PORT_FLOORS_2026-08-20.md
  REQ_E_VERDICT: docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_E_EXPLICIT_CCM_MELLIN_NORMALIZATION_2026-08-20.md
  PAPER_KEY: CCM-ZST-2025
  PAPER_ID: arXiv:2511.22755
  LOCAL_PDF: docs/routeB_bus/litreview/pdfs/2511.22755.pdf
  USAGE_CARD: docs/routeB_bus/litreview/CCM_ZST_USAGE_CARDS.md
  MEIXNER_SCHAEFKE_INPUT: Satz_9_page_243_section_3_2_as_quoted_in_CCM
  FUCHS_INPUT: Theorem_1_JMAA_9_1964_317_330

REQUEST_CONTEXT:
  SELECTED_PREANCHOR_INHABITANT:
    owner_relay_status: LOCAL_KERNEL_GREEN_AWAITING_PUSH
    present_at_input_head: false
    consumed_fact: pair_spec_exposes_exact_selected_Ferrers_modes
  SCHEDULE:
    m_k: k_plus_2
    N_k: k_plus_2
    K_k: five_mul_k_plus_2
    lambda_k: sqrt_k_plus_2
  SOURCE_MODES:
    mode_zero: selected_normalizedPhysicalMode
    mode_four: selected_normalizedPhysicalMode
  LIMIT_PACKET: Q3.RouteB.D0Pstar.explicitCCMLimitH

DELIVERY:
  DOC_ONLY: true
  LEAN_WRITTEN: false
  CODEX_REDIRECTED: false
  ARISTOTLE_CALLED: false

CLOSES:
  - L73_2_SELECTED_FERRERS_LEMMA72_RATE_FLOOR_DECOMPOSITION
  - FALSE_SATZ9_ALONE_CLOSES_SELECTED_ZERO_MASS_COMBINATION_RATE
OPENS: []
FLOOR_IDS_ARE_DECOMPOSITION_LABELS_NOT_NEW_INPUTS: true

TOP_LEVEL_ADJUDICATION:
  L73_2_STATUS: OPEN_MAIN_WALL
  FLOOR_COUNT: 7
  SATZ9_IS_ANALYTIC_CORE_OF_PART_I: true
  SATZ9_IS_ALL_OF_L73_2: false
  SECOND_ANALYTIC_CORE: FIXED_MODE_FINITE_FOURIER_EIGENVALUE_DEFECT_RATE
  REMAINING_FLOORS_AFTER_TWO_RATES: FINITE_DIMENSIONAL_ASSEMBLY
  OVERALL_COST: 9/10
  FIRST_BY_COST_AFTER_D_PUSH: F72_0_SELECTED_FERRERS_PAPER_OBJECT_DICTIONARY
  FIRST_NEW_ANALYTIC_FLOOR: F72_1_MEIXNER_SCHAEFKE_FIXED_MODE_UNIFORM_RATE
  SECOND_LOAD_BEARING_ANALYTIC_FLOOR: F72_3_FINITE_FOURIER_EIGENVALUE_DEFECT_RATE

SCALAR_LOCK_AFTER_REQ_E:
  INTERNAL_LEMMA72_SCALE:
    role: align_project_zero_mass_line_with_literal_equation_7_1_packet
    target: explicitCCMLimitH
  PORT_SOURCE_SCALE:
    formula: portSourceScale_k = 4 * lemma72Scale_k
    role: make_the_downstream_Mellin_limit_equal_project_centeredXi
  PORT_FACING_RATE: >-
    sup_{|x| <= lambda_k}
      |portSourceScale_k * q_k(x) - 4 * explicitCCMLimitH(x)|
      <= C * lambda_k^(-2)
  FACTOR_FOUR_OCCURS_EXACTLY_ONCE: true
  FITTED_SCALAR_FORBIDDEN: true

MINIMAL_MISSING_IDENTITY:
  name: SELECTED_FERRERS_FIXED_MODE_AND_FOURIER_DEFECT_RATE_PACKAGE
  formula: >-
    There exist source-derived nonzero real scalars a_{n,k} and C >= 0 such that,
    eventually in k, for n in {0,4},
      (forall x in [-lambda_k,lambda_k],
        |a_{n,k} f_{n,k}(x) - h_n(x)| <= C lambda_k^(-2))
    and
      |1 - chi_{n,k}| <= C lambda_k^(-2).
  why_minimal: >-
    The first row supplies the individual spheroidal-to-Hermite rate.
    The second preserves the same rate when the zero-mass coefficients are
    defined through whole-window integrals. Once both rows exist, the remaining
    passage to the selected two-mode combination is finite-dimensional algebra.

DISCRIMINATOR:
  name: STRICT_SELECTED_FERRERS_LEMMA72_RATE
  pass: >-
    lambda_k^2 times the uniform norm of the source-normalized selected
    combination minus its repaired limit packet is eventually bounded.
  pointwise_only: INCONCLUSIVE
  L2_only: INCONCLUSIVE
  O_lambda_inverse_only: INCONCLUSIVE
  fitted_sourceScale: REJECT_CIRCULAR
  factor_four_duplicated: REJECT_UNIT_MISMATCH

CANDIDATE_REPRESENTATIONS:
  R1_PAPER_SPLIT_FIXED_MODES_PLUS_FOURIER_DEFECT:
    rank: PRIMARY
    kill_power: 10/10
    cost: 9/10
    route: >-
      Port Satz 9 only for n=0,4; separately port the weak consequence
      |1-chi_n|=O(lambda^-2); then assemble the zero-mass line.
  R2_DIRECT_SCALED_ODE_RESOLVENT_TO_HERMITE:
    rank: RUNNER_UP
    kill_power: 8/10
    cost: 9/10
    route: >-
      Treat the scaled prolate operator as a singular perturbation of the
      harmonic oscillator, prove a fixed-mode graph/resolvent estimate and
      derive both the mode and integral rates without materializing general
      spheroidal or parabolic-cylinder libraries.
  R3_DIRECT_FERRERS_COEFFICIENT_TO_HERMITE:
    rank: QUARANTINED
    kill_power: 7/10
    cost: 10/10
    route: >-
      Rescale the exact Ferrers coefficient recurrence and prove convergence
      to the fixed Hermite coefficient rows with a uniform evaluation bound.

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

NEXT_LOAD_BEARING_GAP: F72_1_MEIXNER_SCHAEFKE_FIXED_MODE_UNIFORM_RATE
NEXT_CHEAPEST_DECISIVE_TEST: F72_3_FUCHS_SCOPE_LOCK_FOR_N0_AND_N4

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## ROUTE MAP

The wall called `L73.2_SELECTED_FERRERS_LEMMA72_RATE` is not one theorem hidden
behind one citation. CCM Lemma 7.2 contains two logically different estimates:

1. the fixed-mode estimates for `n = 0,4`;
2. the estimate for the zero-integral linear combination.

The first is obtained from Meixner--Schäfke Satz 9 after a parameter and
normalization conversion. The second also uses the finite-Fourier eigenvalues
`chi_n(lambda)` to control the whole-window integrals that define the
zero-mass line. The paper explicitly invokes Fuchs Theorem 1 at this point.
`[COFINAL_FAMILY][PAPER]`

Therefore the honest route is

```text
exact selected Ferrers pair and schedule
  -> project/paper spheroidal dictionary
  -> Satz 9 fixed-mode rate
  -> exact Hermite and physical normalization transport
  -> finite-Fourier eigenvalue defect rate
  -> whole-window integral rate
  -> zero-mass coefficient stability
  -> repaired factor-4 port sourceScale
  -> L73.2
```

The two analytic rate suppliers can be developed in parallel after the object
dictionary. The last three steps are assembly, not new asymptotic analysis.

## REPAIRED TARGET AFTER REQ-E

Let

```text
lambda_k := lambda_m (D.index k),
f0_k      := selected mode-zero normalizedPhysicalMode,
f4_k      := selected mode-four normalizedPhysicalMode,
I0_k      := integral f0_k,
I4_k      := integral f4_k,
q_k       := (I4_k f0_k - I0_k f4_k) / sqrt(I0_k^2 + I4_k^2),
h          := explicitCCMLimitH.
```

The paper-level Lemma-7.2 normalization first supplies a source-derived scalar
`lemma72Scale_k` with

\[
 \sup_{|x|\le\lambda_k}
 |\operatorname{lemma72Scale}_k q_k(x)-h(x)|
 \le C\lambda_k^{-2}.
\]

REQ-E proved that the production Mellin transform of `E_star h` is one quarter
of `centeredXi`, not `centeredXi`. The public port field must therefore be

\[
 \operatorname{portSourceScale}_k
 =4\operatorname{lemma72Scale}_k,
\]

and the port-facing rate is

\[
\boxed{
 \sup_{|x|\le\lambda_k}
 |\operatorname{portSourceScale}_k q_k(x)-4h(x)|
 \le 4C\lambda_k^{-2}.
}
\]

This places the scalar `4` exactly once. It is not duplicated in the
quarter-Xi Mellin theorem and is not selected from observed convergence.
`[COFINAL_FAMILY][CONDITIONAL]` **[C09]**

## FLOOR LEDGER

### F72.0 — `SelectedFerrersPaperObjectDictionary`

```yaml
CHARACTER: SOURCE_OBJECT_AND_PARAMETER_PORT
CLOSES:
  - SELECTED_FERRERS_MODE_TO_FIXED_SPHEROIDAL_MODE_DICTIONARY
OPENS: []
DEPENDS_ON_D_INHABITANT: HARD
STATUS: READY_AFTER_OWNER_RELAY_PUSH
COST: 2/10
```

Required output, for `n = 0,4`:

```text
lambda_k = sqrt(k+2);
gamma_k = 2*pi*lambda_k^2;
z = x/lambda_k;
selected project mode = nonzero source-derived scalar
                        * ps_n^0(z; gamma_k^2);
the scalar orientation is fixed before the asymptotic estimate is consumed.
```

The current Q3 shelf already supplies the selected regular Ferrers solutions,
physical scaling, exact prolate ODE, ordered mode labels, zero-count transport,
nontriviality, and uniqueness up to scalar. The production pair theorem exposes

```text
P.h0 = S0.normalizedPhysicalMode,
P.h4 = S4.normalizedPhysicalMode,
P.pw.lambda = sqrt(mProject).
```

What is still needed at this floor is an exact bridge to the normalization used
in the quoted spheroidal asymptotic. Merely satisfying the same ODE and carrying
the same integer label does not identify the scalar. `[COFINAL_FAMILY][PAPER]`
**[C04]**

The preferred implementation does not require a general `ps_n^m` library. It
may expose two fixed project-facing source theorems, one for `n=0` and one for
`n=4`, provided their proof is source-locked to the exact Satz-9 normalization.

### F72.1 — `MeixnerSchaefkeFixedModeUniformRate`

```yaml
CHARACTER: MAIN_EXTERNAL_ASYMPTOTIC_PORT
CLOSES:
  - SELECTED_FERRERS_MODE_ZERO_UNIFORM_HERMITE_RATE
  - SELECTED_FERRERS_MODE_FOUR_UNIFORM_HERMITE_RATE
OPENS: []
DEPENDS_ON: F72_0
STATUS: OPEN_ANALYTIC_CORE_ONE
COST: 8/10
COST_IF_REPROVED_FROM_ODE: 10/10
```

For angular order `m=0`, fixed degrees `n=0,4`, and
`gamma_k = 2*pi*lambda_k^2`, Satz 9 gives uniformly for `z in [-1,1]`

\[
 \operatorname{ps}_n^0(z;\gamma^2)
 =\left(\frac{4\gamma}{\pi}\right)^{1/4}
   \frac{D_n(\sqrt{2\gamma}\,z)}{\sqrt{(2n+1)n!}}
   +O(\gamma^{-3/4}).
\]

After multiplication by `(4*gamma/pi)^(-1/4)` and substitution
`z=x/lambda`, the remainder is `O(gamma^(-1))`. Since
`gamma=2*pi*lambda^2`, this is exactly `O(lambda^(-2))` uniformly on the
expanding physical window `[-lambda,lambda]`.

The project-facing output must have eventual quantifiers and source-derived
scalars:

\[
 \exists C_n\ge0,\ \forall^\infty k,\ \forall |x|\le\lambda_k,\qquad
 |a_{n,k}f_{n,k}(x)-h_n(x)|\le C_n\lambda_k^{-2},
 \quad n\in\{0,4\}.
\]

This is the principal analytic content of Lemma 7.2(i). It is not present in
the current Q3 shelf and no source-locked Mathlib theorem for spheroidal
functions or this asymptotic was found. `[COFINAL_FAMILY][PAPER]`

### F72.2 — `ParabolicCylinderHermiteAndProjectNormalizationTransport`

```yaml
CHARACTER: UNITS_NORMALIZATION_AND_FIXED_MODE_ASSEMBLY
CLOSES:
  - SATZ9_RATE_IN_PROJECT_PHYSICAL_COORDINATES
OPENS: []
DEPENDS_ON:
  - F72_0
  - F72_1
STATUS: OPEN_ASSEMBLY
COST: 3/10
```

The exact fixed-mode identities used by CCM are

\[
 D_0(\sqrt{4\pi}\,x)=2^{-1/4}h_0(x),
\]

\[
 D_4(\sqrt{4\pi}\,x)=2^{5/4}\sqrt3\,h_4(x).
\]

At this floor one should hard-code the two polynomial-Gaussian formulas rather
than formalize a general parabolic-cylinder function library. Mathlib contains
Hermite polynomial algebra, while the Q3 shelf already contains the explicit
Gaussian/Hermite packet needed downstream. The missing work is exact constants,
coercions, and transfer from the paper-normalized representative to a scalar
multiple of the selected project mode.

The scalar need not converge to `1`: the final zero-mass line is invariant
under independent nonzero rescalings of its two basis modes. What must be exact
is the scalar relation itself and its orientation. `[ABSTRACT][CONDITIONAL]`

### F72.3 — `FiniteFourierEigenvalueDefectRate`

```yaml
CHARACTER: SECOND_EXTERNAL_ASYMPTOTIC_PORT
CLOSES:
  - SELECTED_MODE_ZERO_FOURIER_EIGENVALUE_DEFECT_RATE
  - SELECTED_MODE_FOUR_FOURIER_EIGENVALUE_DEFECT_RATE
OPENS: []
DEPENDS_ON:
  - F72_0
  - exact_selected_finite_Fourier_eigenrelations
STATUS: OPEN_ANALYTIC_CORE_TWO
COST: 7/10
COST_IF_FUCHS_SCOPE_REPAIR_IS_NEEDED: 9/10
```

The weak theorem actually needed is only

\[
 |1-\chi_{n,k}|\le C_\chi\lambda_k^{-2},
 \qquad n\in\{0,4\},
\]

eventually in `k`. The exponentially sharp Fuchs asymptotic is stronger than
necessary.

CCM cites Fuchs Theorem 1 and writes explicitly, for `n=4`,

\[
 1-\chi_4(\lambda)
 \sim \frac{2^{14}}{3}\sqrt{2\pi}\,\lambda^5
       e^{-4\pi\lambda^2+9\log\lambda}.
\]

The paper says that the same extreme concentration holds for small fixed modes
such as `n=0,4`, but the exact scope of Fuchs Theorem 1 for the `n=0` branch has
not been source-locked in the present repository. Therefore the cheapest
belief-changing test is a primary-source scope audit before any Lean design.

If Fuchs supplies only the `n=4` line in the required convention, the first
repair candidate is to prove the fixed-mode ordering

```text
0 < chi_4(lambda) <= chi_0(lambda) <= 1
```

for the exact selected Fourier eigenvalues, which would imply
`1-chi_0 <= 1-chi_4`. This repair is not currently claimed as a shelf theorem.

The Q3 shelf already proves finite-Fourier eigenrelations, nonvanishing, and
sign/center relations. It does not prove `chi_n(lambda) -> 1` or any uniform
rate. `[COFINAL_FAMILY][PAPER]`

### F72.4 — `SelectedModeWholeWindowIntegralRate`

```yaml
CHARACTER: ANALYTIC_ASSEMBLY
CLOSES:
  - SELECTED_MODE_ZERO_INTEGRAL_RATE
  - SELECTED_MODE_FOUR_INTEGRAL_RATE
OPENS: []
DEPENDS_ON:
  - F72_2
  - F72_3
STATUS: OPEN_AFTER_TWO_ANALYTIC_CORES
COST: 2/10
```

Use the exact finite-Fourier identity at frequency zero:

\[
 \int_{-\lambda_k}^{\lambda_k} f_{n,k}(x)\,dx
 =\chi_{n,k}f_{n,k}(0).
\]

Together with the center-value consequence of F72.2 and the defect rate from
F72.3, this gives

\[
 \left|
  \int f_{n,k}-\int_{\mathbb R} h_n
 \right|
 \le C_I\lambda_k^{-2}.
\]

No new special-function asymptotic is needed here. The project shelf already
contains the exact frequency-zero/integral crosswalk and positive-integral
orientation for the selected Ferrers witnesses.

### F72.5 — `SelectedZeroMassLineCoefficientStability`

```yaml
CHARACTER: FINITE_DIMENSIONAL_COEFFICIENT_ASSEMBLY
CLOSES:
  - SELECTED_FERRERS_INTERNAL_LEMMA72_SCALE
  - SELECTED_FERRERS_ZERO_MASS_COMBINATION_RATE
OPENS: []
DEPENDS_ON:
  - F72_2
  - F72_4
STATUS: OPEN_ASSEMBLY
COST: 4/10
```

Write the paper-normalized modes as `u0_k,u4_k` and their integrals as
`J0_k,J4_k`. The zero-mass line is generated by

\[
 r_k=J_{4,k}u_{0,k}-J_{0,k}u_{4,k}.
\]

Independent rescaling of the two project basis modes does not change this
one-dimensional line: if `f0=s0*u0` and `f4=s4*u4`, then

\[
 I_4f_0-I_0f_4=s_0s_4\,(J_4u_0-J_0u_4).
\]

Thus the exact production `prolateCombination` is a nonzero scalar multiple of
`r_k`. F72.2 and F72.4 give `O(lambda^-2)` convergence of both the functions
and their two coefficients. An eventual lower bound for the limiting
coefficient norm then gives a source-derived nonzero `lemma72Scale_k` and

\[
 \sup_{|x|\le\lambda_k}
 |\operatorname{lemma72Scale}_k q_k(x)-h(x)|
 \le C\lambda_k^{-2}.
\]

This floor is ordinary two-dimensional norm and division stability. It does
not require another Sturm, spectral, or Mellin theorem.

### F72.6 — `FactorFourPortSourceScaleAndFinalRate`

```yaml
CHARACTER: PORT_NORMALIZATION_AND_FINAL_ASSEMBLY
CLOSES:
  - L73_2_SELECTED_FERRERS_LEMMA72_RATE
OPENS: []
DEPENDS_ON:
  - F72_5
  - REQ_E_QUARTER_CENTERED_XI_NORMALIZATION_AUDIT
STATUS: OPEN_AFTER_F72_5
COST: 1/10
```

Define

```text
portSourceScale_k := 4 * lemma72Scale_k.
```

Prove nonvanishing and multiply the F72.5 estimate by `4`. The final target is
against `4 * explicitCCMLimitH`, not against the unscaled packet. This is the
exact normalization consumed by the repaired L73.5 quarter-Xi identity.

No analytic premise is added here. A second hidden factor `4` anywhere in
L73.3--L73.5 is a unit bug. `[ABSTRACT][CONDITIONAL]` **[C09]**

## DEPENDENCY DAG AND COST

```text
selected D pair_spec (ready locally, not at INPUT_HEAD)
             |
             v
F72.0 object/parameter dictionary                     cost 2
       |                              \
       v                               v
F72.1 Satz-9 fixed-mode rate          F72.3 chi-defect rate
       cost 8                          cost 7
       |
       v
F72.2 physical/Hermite transport       cost 3
       \                              /
        \                            /
         v                          v
          F72.4 integral rate          cost 2
                    |
                    v
          F72.5 zero-mass line          cost 4
                    |
                    v
          F72.6 factor-four port        cost 1
                    |
                    v
                   L73.2
```

The wall retains cost `9/10`: costs are not added linearly, and the two external
asymptotic ports can proceed in parallel. The dominant uncertainty remains the
formal import of fixed-mode uniform large-parameter asymptotics, not the final
locally-uniform topology wrapper.

## WHAT ALREADY EXISTS

### Q3 shelf — usable source infrastructure

The current source tree already contains kernel-checked infrastructure for:

```text
selected mode-zero and mode-four regular Ferrers solutions;
coefficient recurrence and summability;
closed-window continuity and interior C2 regularity;
exact prolate differential equation and endpoint zero flux;
physical scaling x = u/sqrt(mProject);
ordered fixed mode labels and zero-count transport;
finite-Fourier eigenrelations with real nonzero scalars;
center/sign and frequency-zero integral identities;
mode normalization, orthogonality and positive integrals;
the exact production ProlatePair and prolateCombination formula;
the literal equation-(7.1) limit packet;
the repaired quarter-centeredXi normalization audit.
```

These facts make F72.0 and F72.4--F72.6 bounded ports. None of them implies a
uniform large-`lambda` rate.

### Mathlib — generic machinery only

Official Mathlib source contains Hermite polynomial algebra and the generic
analysis machinery needed for filters, eventual bounds, norms, integrals,
finite-dimensional continuity, algebraic division estimates, and ODE
uniqueness. The available Hermite object is a polynomial object, not the
paper's full normalized Hermite function or its spheroidal approximation.

No declaration matching `spheroidal` or `parabolic cylinder` was found in the
official Mathlib source search, and no ready theorem was found for Satz 9 or
Fuchs eigenvalue concentration. This is an availability audit, not a claim
that such a formalization is impossible.

### External sources — exact roles

```text
Meixner--Schaefke Satz 9:
  fixed-mode uniform spheroidal-to-parabolic-cylinder asymptotic.

CCM Lemma 7.2 proof:
  exact parameter translation gamma = 2*pi*lambda^2;
  conversion to normalized h0,h4;
  assembly logic for the zero-mass combination.

Fuchs Theorem 1:
  extreme concentration of the finite-Fourier eigenvalue;
  only the weaker O(lambda^-2) consequence is required here.

DLMF 30.9:
  corroborating spheroidal large-parameter reference and notation;
  not a formal project supplier by itself.
```

## STRONGEST ATTACK

### Kill 1 — Satz 9 alone does not preserve the required rate

Suppose F72.2 gives only

\[
 \sup_{|x|\le\lambda}
 |f_{n,\lambda}(x)-h_n(x)|\le C\lambda^{-2}.
\]

A direct integral estimate over an interval of length `2*lambda` yields only

\[
 \left|\int_{-\lambda}^{\lambda}(f_{n,\lambda}-h_n)\right|
 \le 2C\lambda^{-1},
\]

plus the exponentially small Hermite tail outside the interval. This is one
power too weak. The coefficients defining the zero-mass combination would then
be controlled only at `O(lambda^-1)`, and the final combination rate (7.8)
would not follow.

The paper avoids this loss by using the exact Fourier-eigenvalue identity and
`chi_n(lambda) -> 1` extremely fast. Therefore treating Satz 9 as the whole
supplier proves a pointwise majorant while failing to prove the scalar
functional consumed by the zero-mass combination. `[COFINAL_FAMILY][PAPER]`
**[C10]**

### Kill 2 — same ODE and same index do not fix normalization

The selected project mode is exactly `L2` normalized and source-oriented. The
Meixner--Schaefke function has its own convention, while CCM applies a
lambda-dependent prefactor. Equality of ODE, eigenvalue, parity and zero count
proves proportionality, not equality. Importing the rate without the scalar
crosswalk changes the represented object. **[C04]**

### Kill 3 — the repaired scalar cannot be inserted twice

REQ-E fixes the literal Mellin coefficient to `1/4`. The factor `4` must occur
in the port's source normalization exactly once. Multiplying both the limit
packet and the sourceScale, or leaving the old L73.2 target unchanged while
also multiplying L73.5, changes the downstream limit by a factor `4` or `16`.
**[C09]**

## FINAL PROPOSAL

Use the split paper route R1.

1. Materialize the already kernel-green selected preanchor inhabitant and its
   `pair_spec` after the owner's explicit push authorization.
2. Close F72.0 as a source dictionary, not as a new asymptotic theorem.
3. In parallel:
   - formalize the two fixed-mode project-facing consequences of Satz 9;
   - acquire and lock the exact scope of Fuchs Theorem 1 for `n=0,4`.
4. Prove only the weak Fourier-defect bound `O(lambda^-2)`; do not formalize the
   full exponential asymptotic unless it is cheaper in the source theorem.
5. Assemble F72.4--F72.6 using the exact production modes and the factor-four
   normalization from REQ-E.

Registered prediction before these tests:

```text
The fixed-mode Satz-9 port will dominate the Lean proof cost.
The Fuchs scope audit will either cover both n=0,4 directly or force one
small ordering lemma; it will not require a third large asymptotic theory.
After both rate suppliers, the zero-mass combination will be ordinary
finite-dimensional stability with no new analytic hypothesis.
```

Likeliest failure point:

```text
paper/project normalization is not exposed strongly enough to state the
Satz-9 remainder on the exact selected mode without introducing a parallel
special-function object.
```

Response if that happens:

```text
Do not strengthen SelectedProlatePreAnchorData with an asymptotic field.
Use R2: prove a project-native scaled-ODE/resolvent estimate for the two fixed
modes, retaining the exact source object and normalization.
```

## CODEX DIRECTIVE

```text
NO LEAN EXECUTION FROM REQ-2026-08-20-F.

This verdict is a floor decomposition only.
Do not add CCM Lemma 7.2 as a structure field or hypothesis.
Do not create a parallel spheroidal family and transfer its rate by narrative.
Do not write the factor 4 into both the limit packet and sourceScale.

First future read-only acquisition task:
  F72_3_FUCHS_SCOPE_LOCK_FOR_N0_AND_N4

Return:
  - exact statement of Fuchs Theorem 1;
  - its eigenvalue convention;
  - whether it covers fixed n=0 and n=4;
  - the exact conversion to the project chi scalars;
  - the weakest O(lambda^-2) corollary;
  - one repair if n=0 is not directly covered.

First future Lean theorem after source acquisition and D materialization:
  F72_0_SELECTED_FERRERS_PAPER_OBJECT_DICTIONARY

Validation gate when execution is later authorized:
  direct Lean;
  target build;
  q3_check;
  public axiom audit = [propext, Classical.choice, Quot.sound];
  exact sourceScale and factor-four plant.
```

## META CLOSEOUT

**What became smaller?**

The single `9/10` wall is now two explicit analytic rate suppliers plus five
bounded assembly floors. The first analytic supplier is Satz 9 for the fixed
modes. The second is a finite-Fourier eigenvalue defect rate needed to retain
the same order under integration.

**What was killed?**

```text
Satz 9 alone -> selected zero-mass combination at O(lambda^-2).
```

It loses one power under naive whole-window integration.

**What must not be tried again?**

- Do not call ODE/eigenvalue equality an exact normalization crosswalk.
- Do not integrate a uniform `O(lambda^-2)` bound over a length-`2*lambda`
  window and report `O(lambda^-2)`.
- Do not fit `sourceScale` from the desired Mellin limit.
- Do not duplicate the factor `4` repaired by REQ-E.
- Do not hide the analytic rate as a field of the selected-data structure.

**Current smallest named gap:**

```text
F72_1_MEIXNER_SCHAEFKE_FIXED_MODE_UNIFORM_RATE
```

**Next cheapest decisive test:**

```text
F72_3_FUCHS_SCOPE_LOCK_FOR_N0_AND_N4
```

This is cheaper than a formal proof and can change the floor architecture.

**Fate of prior registered predictions from the L73 floors verdict:**

```text
P_L73_1:
  CONFIRMED_BY_OWNER_RELAY_NOT_AT_INPUT_HEAD.
  The local inhabitant reportedly exposes the required pair_spec.

P_L73_2:
  PARTIALLY_CONFIRMED.
  The port has a fixed factor 4, but the full scalar aligning the exact project
  zero-mass representative with the paper representative may remain k-dependent.

P_L73_3:
  CONFIRMED.
  The selected Ferrers Lemma-7.2 rate is the dominant formal cost; topology
  promotion remains assembly.

P_L73_4:
  PENDING_UNCHANGED.
  The target-tail floor lies downstream of L73.2 and was not retested here.
```

**New registered predictions:**

```text
P_REQ_F_1:
  statement: exact Fuchs scope will cover fixed n=4 and either directly cover
             n=0 or admit a short eigenvalue-order repair
  probability: 0.68
  fate: PENDING

P_REQ_F_2:
  statement: the selected project modes can be related to the Satz-9
             normalization through existing uniqueness and source-index facts
             without a new analytic theorem
  probability: 0.81
  fate: PENDING

P_REQ_F_3:
  statement: after the two rate suppliers, F72.4--F72.6 introduce no new
             cofinal analytic hypothesis
  probability: 0.91
  fate: PENDING
```

**Memory entry:**

```yaml
iteration:
  target: L73_2_SELECTED_FERRERS_LEMMA72_RATE
  status: OPEN_DECOMPOSED
  failed_strategy: SATZ9_AS_SINGLE_COMPLETE_SUPPLIER
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_FIXED_MODE_AND_FOURIER_DEFECT_RATE_PACKAGE
  invariant_learned: zero-mass coefficient rates require Fourier-eigenvalue concentration, not only pointwise mode convergence
  forbidden_future_move: integrate O(lambda^-2) over a growing window and preserve the exponent
  next_decisive_test: verify Fuchs Theorem 1 scope for exact n=0,4 project convention
```
