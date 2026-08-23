# H2A.4.1B.3C.1.7 — global/window form and polarized near-radical defect discriminator (READ-ONLY MATH+SOURCE)

```yaml
PRIMARY: H2A_4_1B_3C_1_7_GLOBAL_WINDOW_FORM_AND_POLARIZED_NEAR_RADICAL_DEFECT_DISCRIMINATOR
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict 713d379a — CODEX DIRECTIVE (REQ-2026-08-22-V)
MODE: READ_ONLY_MATH_AND_SOURCE
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: 713d379a1a9068a3e628998e161c266e77471983   # live git rev-parse HEAD

OUTCOME_CODE: GLOBAL_WINDOW_FORM_DOMAIN_CROSSWALK_OPEN

SOURCES_READ:
  - "Connes 2602.04022 pp. 20-21 (section 4.1, prior session), 26-30 (sections 6.1-6.6, this session, rendered pages)"
  - "D0PstarSourceWeilSesquilinearForm.lean (199): form on sourceArchimedeanShiftedFormDomain"
  - "D0PstarSourceWeilClosedForm.lean (124): sourceWeilShiftedExtendedQuadraticForm — lsc extended form on all H_m, finite iff in the shifted domain (:79)"
  - "D0PstarShiftedArchClosedForm.lean (248): closed weighted-Lp map, root energy, extended arch form"
  - "D0PstarArchPrimeSesquilinearForm.lean (151), D0PstarPrimeAmbientSesquilinearForm.lean (310): prime pieces + finite-synthesis identities"
  - "D0PstarSourceModeCosineCCMQKernel.lean (:536 private support cutoff)"
  - "D0KTrialStage2.lean (E_star + midpoint-representative docstring)"
  - "ProlateLayer.lean (prolateCombination, ProlatePair)"
  - "own 3C.1.5 / 3C.1.6 reports"

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## TEST 1 — TYPE AND SIGN TABLE

| object | carrier / type | status of the maps |
|---|---|---|
| global Weil form QW_global | quadratic form on (Schwartz-type) test functions on the multiplicative half-line; paper §4.1; sign convention: positivity of QW is RH-equivalent | PAPER only; no Lean object |
| paper QW_lambda | restriction of QW_global to support in [lambda^-1, lambda]; carries canonical selfadjoint A_lambda with QW_lambda(f,f) = <A_lambda f, f> (paper (16)) | PAPER only |
| project H_m | L2(I_m, d*u) window space | LEAN |
| sourceArchimedeanShiftedFormDomain i | dense subdomain of H_m; the production sesquilinear form `sourceWeilSesquilinearForm i` is DECLARED ONLY HERE (star-linear first slot) — verdict repair honored | LEAN |
| extended closed form | `sourceWeilShiftedExtendedQuadraticForm` (ClosedForm.lean:65): lower-semicontinuous on ALL of H_m with values in [0, infty]; FINITE exactly on the shifted domain (:79); relation toReal = re + shift*normSq (:90) — the SHIFT and its sign are explicit | LEAN |
| finite synthesis span | E_m_N via ccmFiniteShiftedFormDomainSynthesis; lies inside the shifted domain; matrix identity to ccmWeilMatFinite (3C.1.5, admitted) | LEAN |

Maps recorded: finite span ⊂ shifted domain ⊂ H_m (literal inclusions);
`iota` = zero extension H_m → functions on (0,infty) (function-level, no Lean
object for the global pairing); W02 endpoint term sits inside the window form
as the rank-two endpoint functionals (bounded, ambient); the lower-bound
shift enters ONLY the extended/closed objects, with its sign exposed at
ClosedForm.lean:90.

**Equality audit.**  literal: form = matrix form on the finite span
(source-locked).  closed-form: window form ↔ extended lsc form on H_m
(source-locked, with shift).  OPEN: any theorem identifying the RESTRICTION
of the paper's QW_global (or QW_lambda) with `sourceWeilSesquilinearForm i`
on the shifted form domain — nothing on disk states it; the three component
crosswalks (W02/WR/Prime pairings = CCM entries) cover the finite span only.
This is the crosswalk the outcome code names.

## TEST 2 — GENERAL POISSON DEFECT IDENTITY (exact, elementary derivation)

For an even function `f` of bounded variation with compact support, carrying
the MIDPOINT convention at its jumps (exactly the convention the production
`hTrial_m` already carries — D0KTrialStage2 docstring: "the endpoint
half-values are already part of hTrial_m"), the classical Dirichlet–Jordan
form of Poisson summation applies pointwise with symmetric summation.  For
`u > 0`, applying it to `x -> f(x*u)`:

```text
sum_{n in Z} f(n*u) = (1/u) * sum_{k in Z} fhat(k/u),
```

and splitting off the `n = 0` and `k = 0` terms of the even sums:

```text
E(f)(u) = sqrt(u) * sum_{n>=1} f(n*u)
        = E(fhat)(1/u)  +  (1/2) * fhat(0) * u^{-1/2}  -  (1/2) * f(0) * u^{1/2}.
```

**This is the exact general defect identity.**  When `f(0) = fhat(0) = 0` it
degenerates to the paper's (18).  Both point defects are EXPLICIT elementary
functions on the window — no O-terms, nothing differentiated.  Category
(Test 4): pointwise/function level, hence L2(I_m)-level after restriction;
NO endpoint atoms exist or are inserted (P_POLARIZED_DEFECT_4 = 0.90:
CONFIRMED in this ledger).  The one external classical input is
Dirichlet–Jordan/BV Poisson with symmetric summation (the Fourier
coefficients of the truncated prolate decay like 1/|xi| because of the
carrier jump, so the k-series converges conditionally, symmetrically) —
named as the explicit approximation/summation object the directive allows;
no Mathlib instance claimed.

Applied to the selected trial (`f = prolateCombination`, `fhat(0) = 0` by
the vanishing-integral condition):

```text
E_star(hTrial)(u) = E_star(hTrialHat)(1/u) - (1/2) * hTrial(0) * u^{1/2}
                    on the window,
```

with exactly ONE surviving point defect (the center value), of exponentially
small amplitude `|hTrial(0)|` (prolate-to-Hermite convergence), carried as an
explicit function `u^{1/2} * 1_{I_m}` — bounded on the window.

## TEST 3 — POLARIZATION

What the consumer needs:

```text
QW_global( iota(S(D_k v)), E_star(hTrial) )  uniformly over unit v.
```

The Test-2 identity decomposes the second argument EXACTLY into

```text
(reflected E-star image)  +  (explicit center-defect function).
```

Polarizing is linear, so the pairing splits into two exact terms.  The
center-defect term is a pairing against a FIXED explicit bounded window
function — form-domain membership of `u^{1/2}*1_{I_m}` in the shifted domain
is checkable and its pairing is a concrete (not yet estimated) functional.
The reflected term is where the radical mechanism should act: its Mellin
side carries the zeta factor, and vanishing at the zeros is what kills it.
BUT this step needs, simultaneously:

1. the OPEN global-to-window form crosswalk of Test 1 (without it the
   project form cannot be replaced by QW_global in the pairing at all);
2. an inversion-covariance statement for the window form (the reflected
   image lives at `1/u`; the window `[lambda^-1, lambda]` is
   inversion-symmetric, but no source-locked theorem transports the form
   through `u -> 1/u`);
3. a spectral (zero-sum) representation of the polarized pairing valid for
   the BV class with conditionally convergent Fourier tails — the paper
   states the radical fact for `S_0^ev`; extending the polarized version to
   the truncated class is a genuine theorem, not bookkeeping.

So the discriminator's answer: the identity half EXISTS (Test 2, exact,
function-level, both point defects explicit — this is strictly more than a
scalar formula: it is an exact decomposition of the vector `E_star(hTrial)`
itself, hence polarizes against ANY v); the crosswalk half is OPEN, and it
blocks the substitution of QW_global into the consumer.  Per the outcome
list this is:

```text
GLOBAL_WINDOW_FORM_DOMAIN_CROSSWALK_OPEN
```

(the identity finding is recorded inside this report; the code reflects the
blocking wall, *not* the absence of the identity).  No scalar Rayleigh value
is used anywhere as a dual bound (the diag(1,-1) plant is reproduced below);
P_POLARIZED_DEFECT_3 = 0.25 is REFUTED-consistent: scalar estimates alone
do NOT imply the dual rate, and this report never uses them.

## TEST 4 — CATEGORY FIREWALL

Chosen category: **L2/function ledger** for the identity and all defects.

```text
delta-objects in this report:
  center-defect: (1/2)*hTrial(0)*u^{1/2} restricted to I_m — an explicit
    continuous function; L2(I_m) member; NO atom;
  below-window / projection tails (from 3C.1.6): L2 functions;
  endpoint atoms: DO NOT EXIST in this ledger.  They arise only after a
    distributional derivative (the 3C.1.2 D_t analysis) — a DIFFERENT,
    separately typed ledger, connected by the explicit map D_t; no term is
    moved between the categories without that map being named.
```

Every term above is well-typed in L2(I_m).  The verdict's repair (endpoint
atoms need a category change) is honored: the 3C.1.6 "endpoint atoms" line
is hereby restated as belonging to the distributional-derivative ledger
only.

## TEST 5 — RATE ARITHMETIC

Not activated: Test 3 did not produce the full polarized radical formula
(the crosswalk wall blocks it).  For the record, DIAGNOSTIC_ONLY notes:
the center-defect pairing amplitude carries the exponentially small factor
`|hTrial(0)|`, and the paper's Figure-1 scalar similarity remains a
heuristic; neither is used as a dual action bound.

## MANDATORY PLANTS

1. **Scalar vs dual (verdict's plant, reproduced).**  `B = diag(1,-1)`,
   `g = (1,1)/sqrt(2)`, `v = (1,0)`: `B(g,g) = 0` yet `|B(v,g)| = 1/sqrt(2)`.
   Small diagonal value implies nothing about the polarized action of an
   indefinite Hermitian form; a Cauchy–Schwarz repair would need positivity
   — RH-equivalent for the unshifted global form, hence forbidden.
2. **Projection breaks radicality.**  `B = diag(0,1)`, `G = e_0` radical;
   project onto `span(e_0+e_1)`: `B(e_0+e_1, PG) = 1/2 != 0`.
3. **Endpoint values create no L2 atoms; differentiation of a jump does.**
   Changing a function at finitely many points does not change its L2 class
   (atoms cannot be "inserted" at the function level); but
   `D_t 1_{[a,b]} = delta_a - delta_b` — the atom is created BY the
   derivative map, in the distributional category.  Two categories, one
   explicit map.
4. **Prime cutoff exact by support.**  For two log-window functions of
   window length `L`, the shift-correlation at `log k` vanishes identically
   for `log k > L`; disk instance
   `sourceModeCorrelation_add_neg_eq_zero_of_window_lt` (private, :536).
   The `k <= m` sum is a support fact on the finite span, not a truncation.
5. **Component norm sums are not the full signed consumer.**  4.1A
   cancellation plant + the 3C.1.4 corrected-vs-raw falsifier, reused.

## FORBIDDEN CHECK

```yaml
scalar_near_radical_as_dual_bound: not used (plant 1; Test 5 marks scalars DIAGNOSTIC_ONLY)
global_window_equality_on_all_H_m: not stated (Test 1 places the form on the
  shifted domain and the extended lsc form on H_m, with the shift exposed)
endpoint_atoms_in_function_ledger: none (Test 4; plant 3)
positivity_or_CS_for_unshifted_global_form: not used (plant 1 notes why forbidden)
component_opNorm_sum_as_consumer: no (plant 5)
fitted_constants_numerics_new_hypotheses: none
selected_row_schedule_scale_target_rayleigh_altered: no
O_term_differentiated: no (the Poisson identity is exact)
lean_numerics_aristotle: none
receipt: BASE_HEAD from live git rev-parse (713d379a...)
```

## PREDICTION CHECK

```text
P_POLARIZED_DEFECT_1 = 0.80 (crosswalk closes on the shifted form domain,
  not all H_m): CONSISTENT — the disk types confirm the shifted domain is
  the only honest carrier; the crosswalk itself remains open (the outcome).
P_POLARIZED_DEFECT_2 = 0.55 (Poisson yields a useful exact polarized defect
  formula): CONFIRMED AT THE IDENTITY LEVEL — the exact defect identity
  exists with both point corrections explicit and only ONE surviving defect
  for the selected trial (fhat(0) = 0); its RADICAL exploitation is blocked
  by the crosswalk + inversion-covariance + BV spectral extension (three
  named inputs).
P_POLARIZED_DEFECT_3 = 0.25: CONSISTENT WITH REFUTATION — nothing scalar
  implies the dual rate; not used.
P_POLARIZED_DEFECT_4 = 0.90 (atoms vanish in L2, reappear after the
  derivative map): CONFIRMED (Test 4, plant 3).
LIKELIEST_FAILURE (GLOBAL_QW_FORM_DOMAIN_OR_UNBOUNDED_DUAL_ACTION_GAP):
  OBSERVED — the form-domain crosswalk is exactly the blocking wall.
```

## RANKED OPEN SUPPLIERS AFTER THIS DISCRIMINATOR

```text
T1: GLOBAL_WEIL_TO_PROJECT_SOURCE_WEIL_EXACT_RESTRICTION_ON_THE_SHIFTED_FORM_DOMAIN
    (the outcome wall; component identities exist on the finite span; the
    domain-level statement is new mathematics with a clear route:
    W02/WR/Prime piecewise + closed-form continuity).
T2: WINDOW_FORM_INVERSION_COVARIANCE (u -> 1/u transport on the
    inversion-symmetric window; needed to use the reflected term).
T3: POLARIZED_SPECTRAL_REPRESENTATION_FOR_BV_CLASS (zero-sum formula for
    the polarized pairing with conditionally convergent tails; the genuinely
    analytic input — the repaired heir of the old prime-oscillation wall).
T4: SELECTED_RAYLEIGH_SCALAR_BOUND (carried over).
POSITIVE ASSET (new, this report): the exact BV Poisson defect identity
    with midpoint convention — ready to be the spine of T3, and the reason
    the selected trial has ONE defect term, not two (fhat(0) = 0 exactly).
```

SUCCESS_CODE_RETURNED: GLOBAL_WINDOW_FORM_DOMAIN_CROSSWALK_OPEN
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
