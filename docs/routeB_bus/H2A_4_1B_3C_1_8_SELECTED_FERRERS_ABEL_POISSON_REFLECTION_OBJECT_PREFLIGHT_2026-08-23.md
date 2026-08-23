# H2A.4.1B.3C.1.8 — selected Ferrers Abel-Poisson reflection object preflight (READ-ONLY MATH+SOURCE)

```yaml
PRIMARY: H2A_4_1B_3C_1_8_SELECTED_FERRERS_ABEL_POISSON_REFLECTION_OBJECT_PREFLIGHT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict be71af51 — CODEX DIRECTIVE (REQ-2026-08-22-V)
MODE: READ_ONLY_MATH_AND_SOURCE
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: be71af51da5399aa78a15f13095e1158a74f2aca   # copied verbatim from live `git rev-parse HEAD` output (receipt repair honored)

OUTCOME_CODE: ABEL_REFLECTED_L2_FOUND_SHIFTED_FORM_NORM_OPEN

DECK_UPDATE_NOTICE:
  ARSENAL_CARDS_v1: card C13 RESTORE-SYMMETRY-BY-EXPLICIT-SHADOW minted
    2026-08-23 by owner ratification (commit ece40b7a);
    NEW_SHA256: 46795713ed6d48b924db4d3ac942f3fbcc02987c2918494d6d2b64fd2e0ebae4
    (the 2026-08-04 mandate hash refers to the 12-card deck; fail-closed
    checks must use the new hash from this notice onward).
    The C13 slot reserved in the 2026-08-05 contour verdict (source-faithful
    transport) was NOT_MINTED and will take the next free number.

FILES_READ:
  - Q3/Proofs/RouteB/D0KTrialStage2.lean (E_star = tsum over PNat)
  - Q3/Proofs/RouteB/MuntzV3/Core.lean (Estar, Mellin, Gwin machinery)
  - Q3/Proofs/RouteB/ProlateCombinationMuntzRegularity.lean (even, support, integrable, ZERO INTEGRAL :46)
  - Q3/Proofs/RouteB/G6N1SelectedFerrersZeroMassCylinderPacket.lean (Lemma72Scale packet rate :177)
  - Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean (Lemma73SourceScale packet rate :61)
  - Q3/Proofs/RouteB/D0PstarShiftedArchClosedForm.lean (sqrt-weight maximal multiplier; domain = shifted form domain; closedness)
  - Q3/Proofs/RouteB/D0PstarSourceWeilClosedForm.lean
  - docs/routeB_bus/GOAL057_B3_0S_SHIFTED_ARCH_FORM_DOMAIN_DENSITY_CLOSEOUT_2026-08-09.md (NO_FORM_NORM_CORE_DENSITY :116, Hilbert-only :19)
  - docs/routeB_bus/H2A_4_1B_3C_1_7_..._2026-08-23.md (own prior report)

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## FOURIER CONVENTION LOCK (directive item 1)

```text
fhat(xi) = integral_R f(x) * exp(-2*pi*i*x*xi) dx
```

— identical to the judge's fixed convention and to Mathlib's `Real.fourierChar`
normalization used by the production `𝓕` (checked in 3C.1.1's mode-transform
usage: `Real.fourier_eq` with `fourierChar (-(inner v t))`).  No stray `2*pi`
factors: with this convention Poisson reads `sum_Z f(n*u) = (1/u) *
sum_Z fhat(k/u)` exactly, which is the form used in 3C.1.7 and below.

## TEST A — EXACT FINITE ABEL SUM AND NORMALIZATIONS

For the SOURCE-SCALED selected packet (no new normalization introduced):

```text
f_k := selectedFerrersLemma73SourceScale k * prolateCombination(pair k)
       (even; support in [-lambda_k, lambda_k]; midpoint representative;
        integral f_k = 0 by integral_prolateCombination_eq_zero (:46))
```

the finite Abel-reflected sum on the window `u in I_m`:

```text
E_reflect(r, f_k)(u) := u^{-1/2} * sum_{n >= 1} r^n * fhat_k(n/u),
    0 < r < 1.
```

Every factor exposed: the `u^{-1/2}` prefactor is forced by the Poisson
bookkeeping (it is `sqrt(1/u)` of the reflected variable); the `r^n` weights
are the Abel regularizer; `fhat_k` carries the source scale linearly
(`fhat` is linear, so the scale sits outside: `s_k * (prolateCombination)^hat`).

## TEST B — ABSOLUTE CONVERGENCE FOR r < 1

`|fhat_k(xi)| <= ||f_k||_{L1} < infty` (prolateCombination_integrable, :36),
so `sum_n r^n |fhat_k(n/u)| <= ||f_k||_{L1} * r/(1-r)` — absolutely
convergent for every `r < 1` and every `u > 0`, uniformly on the window.
PROVED at the triviality level (geometric domination); the finite Abel sum
is unconditionally summable, hence even production-`tsum`-compatible AT
FIXED r < 1.

## TEST C — THE r -> 1- LIMIT

**Pointwise.**  `f_k` is even, compactly supported, of bounded variation
(finite linear combination of truncated PSWFs: smooth interior, two jump
points at the carrier edges), carrying the midpoint representative.  By
Dirichlet–Jordan Poisson summation the symmetric series
`sum_{n>=1} fhat_k(n/u)` CONVERGES for every `u > 0` (its value is given by
the 3C.1.7 identity).  By Abel's limit theorem, a convergent series is Abel
summable to the same value.  Hence the pointwise limit exists at EVERY
window point and equals the Dirichlet–Jordan value.  [external classical
inputs, named: Dirichlet–Jordan for BV midpoint representatives; Abel's
theorem.  No Mathlib instance claimed for either.]

**L2 on I_m.**  The Abel mean is a convex average of the partial sums:
`sum_n r^n a_n = (1-r) * sum_N S_N r^N`.  The classical Jordan bound gives
uniform boundedness of the Fourier partial sums of a BV function:
`sup_{N, u in I_m} |S_N(u)| <= C(Var(f_k), ||f_k||_infty)` (the window keeps
the effective period `u` in a compact positive range).  Convex averages
inherit the bound, so `|E_reflect(r, f_k)(u)| <= C'` uniformly in `r, u`;
the window has finite measure; dominated convergence upgrades the pointwise
limit to an L2(I_m) limit.  **L2 LIMIT: FOUND** — modulo the two named
classical inputs (Jordan uniform bound; dominated convergence is Mathlib).

## TEST D — COMPARISON WITH SYMMETRIC DIRICHLET–JORDAN SUMMATION

Agreement is automatic from Test C: the symmetric series converges pointwise
and Abel's theorem forces the Abel limit to coincide with it — there is no
gap between the two summation methods ONCE convergence of the symmetric sum
is granted; the Abel object adds absolute convergence at each `r < 1` (which
the symmetric sum lacks) and canonicity of the limit.  The even symmetric
grouping is built into the `n >= 1` form because `fhat_k` is even (`f_k`
real and even; evenness from prolateCombination_even :14).

## TEST E — SHIFTED-FORM-DOMAIN MEMBERSHIP AND FORM-NORM GROWTH

Two separate questions, kept apart:

**L2 membership of the limit: YES** (Test C gives the limit as an L2(I_m)
function; independently, by the 3C.1.7 identity the limit equals
`E(f_k)|window - centerDefect`, and `E(f_k)` restricted to the window is the
production `gTrial`-class object whose MemLp certificate is a standing
supplier — consistency check passed).

**Shifted-form-domain membership: OPEN.**  The domain is the graph domain of
the closed maximal sqrt-weight multiplier
(`sourceArchimedeanShiftedWeightedLpPMap`: domain literally equals the
shifted form domain; closedness proved on disk).  Membership therefore
means: the log-weighted (root-energy) norm of the reflected object is
finite.  Structural expectation: a BV window function has log-Fourier
coefficients of order `1/n`, so the arch weight (log-growth envelope)
gives `sum (1 + log(2+n)) / n^2 < infty` — a polynomial-log bound is
PLAUSIBLE (this is the judge's P_ABEL_OBJECT_3 = 0.58 line).  But no disk
theorem supplies the root-energy bound for E-star-class objects, and the
density closeout explicitly warns the form domain has NO form-norm core
from the Hilbert side (NO_FORM_NORM_CORE_DENSITY, closeout :116) — so
membership must be proved directly, not inferred from density.  Form-norm
growth in `k`: unquantified; needs the actual root-energy computation.
THIS is the outcome wall.

## TEST F — SOURCE-SCALED CENTER DEFECT FROM EXISTING F72 SUPPLIERS

Exact disk citation (no exponential claim anywhere):
`selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates`
(G6N1SelectedFerrersFactorFourPortRate.lean:61): under the existing
verbatim `hmode`/`hchi` hypotheses, eventually, for ALL `x` in the window:

```text
|| selectedFerrersLemma73SourceScale k * prolateCombination(pair k)(x)
   - 4 * explicitCCMLimitH(x) ||  <=  C / lambda_k^2.
```

Evaluate at `x = 0`: `explicitCCMLimitH(0) = 0` (the `u^2` factor), so

```text
|| f_k(0) || = || sourceScale_k * prolateCombination(0) || <= C / lambda_k^2
```

eventually — the source-scaled Poisson center defect is a correctly typed
`O(lambda^-2)` object from an EXISTING kernel-checked supplier (the
zero-mass variant :177 gives the same at scale `Lemma72Scale` without the
factor four).  The raw unscaled exponential claim from 3C.1.6 is retracted
exactly as the verdict required; the judge's center algebra note
(`I0 = chi0*h0(0)`, `I4 = chi2*h4(0)`, packet center ~ `chi2 - chi0`) is
consistent with this and is the route to any FUTURE sharper rate — not
needed for the current typed bound.

## TEST G — CONDITIONAL-VS-TSUM PLANT

`sum (-1)^(n+1)/n`: symmetric/conditional value `log 2`; but the terms are
not norm-summable, so in Mathlib semantics `Summable` FAILS and `tsum`
returns the junk value `0 != log 2`.  Same displayed summands, different
summation functional.  **Consequence for the production `E_star`
(directive item 7):** `E_star = sqrt(u) * tsum ...` (D0KTrialStage2.lean:24)
applied to the reflected samples `fhat_k(n/u)` (order `1/n` with
oscillation, NOT norm-summable in general) would return the junk `tsum = 0`
— the existing `E_star` is NOT reusable for the reflected object.  A new
canonical object is required, and the Abel family of Tests A–D is exactly
it: absolutely convergent (hence tsum-compatible) at each `r < 1`, with a
canonical L2 limit.  P_ABEL_OBJECT_1 = 0.97: CONFIRMED.

## FORBIDDEN CHECK

```yaml
conditional_symmetric_series_called_tsum: no (Test G separates them; the
  reflected term is never written as production E_star)
raw_center_exponential_without_supplier: retracted; replaced by the exact
  F72 chain citation (Test F)
hilbert_density_as_form_core: not used (Test E quotes NO_FORM_NORM_CORE_DENSITY
  and demands direct membership)
lsc_as_equality_of_forms: not used
scalar_near_radical_as_dual_bound: not used
lean_numerics_aristotle: none
receipt: BASE_HEAD copied verbatim from live git rev-parse output
```

## PREDICTION CHECK

```text
P_ABEL_OBJECT_1 = 0.97 (reflected series not representable by production
  E_star without a new object): CONFIRMED (Test G — tsum junk).
P_ABEL_OBJECT_2 = 0.84 (Abel gives a canonical L2 limit on each window):
  CONFIRMED at classification level (Tests C-D; two named classical inputs).
P_ABEL_OBJECT_3 = 0.58 (Abel limit in shifted domain with polynomial-log
  bound): UNRESOLVED — structurally plausible (BV Fourier decay vs log
  weight), blocked on a direct root-energy computation; the outcome wall.
P_ABEL_OBJECT_4 = 0.95 (Hilbert density cannot close the form crosswalk):
  CONFIRMED — the density closeout itself records NO_FORM_NORM_CORE_DENSITY.
```

## RANKED OPEN SUPPLIERS AFTER THIS PREFLIGHT

```text
U1 (outcome wall): ROOT_ENERGY_BOUND_FOR_THE_ABEL_REFLECTED_OBJECT —
    direct membership of the L2 limit in the shifted form domain with a
    polynomial-log form-norm bound (the P3 = 0.58 question).
U2: FOURIER_CONVENTION_AND_MIDPOINT_SOURCE_LOCK — Lean-level lock of the
    Dirichlet–Jordan/Abel classical chain (two named external theorems;
    the only genuinely classical imports of the whole construction).
U3: GLOBAL_WEIL_TO_PROJECT_SHIFTED_FORM_CROSSWALK — unchanged (direct
    all-domain identity or form-core route; Hilbert density killed).
U4: POLARIZED_FULL_WEIL_DEFECT_BOUND + WINDOW_PROJECTION_DEFECT_RATE +
    SELECTED_RAYLEIGH_SCALAR_BOUND — carried over.
```

SUCCESS_CODE_RETURNED: ABEL_REFLECTED_L2_FOUND_SHIFTED_FORM_NORM_OPEN
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
