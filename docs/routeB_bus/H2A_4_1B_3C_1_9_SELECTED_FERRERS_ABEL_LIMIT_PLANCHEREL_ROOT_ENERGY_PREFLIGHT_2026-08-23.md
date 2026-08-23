# H2A.4.1B.3C.1.9 — selected Ferrers Abel-limit Plancherel/root-energy preflight (READ-ONLY MATH+SOURCE)

```yaml
PRIMARY: H2A_4_1B_3C_1_9_SELECTED_FERRERS_ABEL_LIMIT_PLANCHEREL_ROOT_ENERGY_PREFLIGHT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict 9c20c0c7 — CODEX DIRECTIVE (REQ-2026-08-22-V)
MODE: READ_ONLY_MATH_AND_SOURCE
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: b3acb86b0f9276c65959b4aa71b4c844283eb857   # pasted verbatim from live `git rev-parse HEAD`

OUTCOME_CODE: ABEL_LIMIT_SHIFTED_FORM_DOMAIN_ROUTE_FOUND

SOURCES_READ:
  - "D0PstarSourceLogWindowFourierL2Isometry.lean (118 lines, COMPLETE): private memLp of mode Fourier images; orthonormality via cosine-correlation control; synthesized isometry :83; apply_mode :105; docstring no-claim boundary"
  - "D0LogWindowVNMCompletenessBridge.lean (V_n_m HilbertBasis, logWindowL2Equiv)"
  - "D0Mode4FerrersRegularEvenProlateSolution.lean (interior analytic regularity: (1-z^2)^{m/2} * entire)"
  - "D0Mode4FerrersPhysicalNormalizedZeroExtension.lean, D0ModeZeroFourFerrersProductionProlatePair.lean (Icc.indicator full-endpoint zero extension)"
  - "D0PstarShiftedArchFormDomain.lean, D0PstarShiftedArchClosedForm.lean (domain via the synthesized isometry + sqrt weight)"
  - "D0PstarExactArchSymbolLogDomination.lean (log envelope)"
  - "G6N1SelectedFerrersFactorFourPortRate.lean (:61 source-scaled C0 packet rate)"
  - "lake-manifest.json: mathlib inputRev v4.26.0"
  - "pinned Mathlib Analysis/Fourier directory listing: AddCircle, AddCircleMulti, BoundedContinuousFunctionChar, FiniteAbelian, FourierTransform, FourierTransformDeriv, Inversion, Notation, PoissonSummation, RiemannLebesgueLemma, ZMod — NO LpSpace / Plancherel / L2 Fourier layer"

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## TEST 3 FIRST (the decisive finding) — LITERAL FOURIER-ISOMETRY CROSSWALK

Directive option B is AVAILABLE: a source-specific theorem identifying the
synthesized image with the ordinary Fourier integral, WITHOUT any Plancherel
backport.  The reason is structural: every `H_m` vector lives on a window of
FINITE multiplicative measure, so `L2(window) ⊂ L1(window)` with the explicit
constant `sqrt(|I_m|)` (Hölder).  Route (all steps elementary):

```text
For x in H_m with representative g (zero-extended off the window):
 (i)   S_N := finite basis synthesis of ⟨V_n, x⟩, |n| <= N.
       S_N -> x in L2(window)                     [V_n_m HilbertBasis
                                                   completeness, on disk].
 (ii)  ||S_N - g||_{L1(R)} = ||S_N - g||_{L1(window)}
       <= sqrt(|I_m|) * ||S_N - g||_{L2} -> 0     [finite measure, Hölder].
 (iii) sup_t |F(S_N)(t) - F(g)(t)| <= ||S_N - g||_{L1} -> 0
       — the L1 -> C0 bound of the Fourier integral: UNIFORM convergence
       of F(S_N) to the ordinary pointwise Fourier integral of g.
 (iv)  isometry(S_N) = Lp-class of F(S_N) EXACTLY — by linearity plus the
       kernel-checked `coeFn_sourceLogWindowFourierL2Isometry_apply_mode`
       (:105) on each basis mode (finite sums, no limit needed).
 (v)   isometry(S_N) -> isometry(x) in L2         [isometry continuity].
 (vi)  An L2 limit and a uniform limit of the same sequence agree a.e.:
       hence  isometry(x) = F(g)  almost everywhere.
```

Every ingredient is either on disk ((i), (iv)) or a pinned-Mathlib-available
elementary fact ((ii) Hölder; (iii) norm_fourierIntegral_le-type bound —
present in the pinned FourierTransform layer; (v), (vi) standard measure
theory).  NO new Fourier API is needed; the docstring's no-claim boundary is
closed by a theorem, not an import.  This resolves the verdict's C04 blocker
for ALL window vectors at once — not only the Abel limit.
P_ABEL_ROOT_3 = 0.62: CONFIRMED, and cheaper than a "local Plancherel
extension": the finite-measure window makes general Plancherel unnecessary.

(The pinned `PoissonSummation.lean` covers only the continuous/summable
class — usable for the R2 smooth-compensator route, NOT for the BV packet;
noted for completeness.)

## TEST 1 — EXACT SELECTED MIDPOINT/BV OBJECT

From the literal production files:

```text
regularity: the selected mode is Icc.indicator of a CLOSED-WINDOW CONTINUOUS
  function whose interior is (1-z^2)^{m/2} * (entire g)  — real-analytic
  interior, finite one-sided limits at the edges (RegularEvenProlateSolution;
  zero-extension files).  Hence the packet is piecewise C1 on R with exactly
  TWO jump points (±lambda_k): piecewise-AC, and BoundedVariationOn holds
  QUALITATIVELY with
      Var f_k = 2*|f_k(lambda^-)| + integral |f_k'| over the open window.
quantitative certificate V_k: derivable from the interior derivative bound
  of the entire factor (the Ferrers tail-splice coefficient data);
  NOT source-locked today — this is the P_ABEL_ROOT_2 = 0.84 item, a
  theorem-sized supplier, route clear, not done here.
midpoint object: f_k^mid differs from production f_k at exactly the two
  points ±lambda_k (half-values).  Fourier(f_k^mid) = Fourier(f_k) (a.e.
  equality of L1 representatives); L1/L2 classes equal; production E_star
  and midpoint E_star differ exactly at the finite seam set
  {u = lambda_k/n : n <= lambda_k^2} — pointwise correction at a seam:
      full-endpoint contribution  sqrt(lambda/n) * f(lambda^-),
      midpoint contribution       (1/2) * sqrt(lambda/n) * f(lambda^-);
  equal as L2(window) classes (finitely many points, measure zero).
```

The verdict's repair is honored: nowhere below is the production packet
called a midpoint representative; every identity through Dirichlet–Jordan
is stated for `f_k^mid` and transported to production objects by a.e.
equality ONLY.

## TEST 2 — EXACT ABEL L2 BOUND (explicit envelope, no generic phrases)

For the even piecewise-AC midpoint packet, integrate the partial sum by
parts in Stieltjes form: with `D_N(y) = sum_{n<=N} e(-n y)` and
`S_N(u) = sum_{n<=N} fhat(n/u) = integral f(x) D_N(x/u) dx`, integration by
parts against `df` (finite measure: two atoms of size `f(lambda^-)` plus the
AC part `f' dx`) reduces everything to the universal bound of the conjugate
Dirichlet primitive

```text
sup_{N, y} | sum_{n=1}^{N} sin(2*pi*n*y)/n | <= C_sin   (universal constant),
```

giving the explicit window envelope

```text
sup_{N, u in [lambda^{-1}, lambda]} |S_N(u)|
  <= C * lambda_k * ( |f_k(lambda^-)| + Var_{[0,lambda]} f_k )
  =: C * lambda_k * W_k .
```

Abel means are convex combinations of the S_N, so the same envelope bounds
`E_reflect(r)` uniformly in `r`; the window has finite measure; dominated
convergence gives the L2 limit.  Status: the derivation chain is exact and
short, but TWO inputs are external classical facts with no pinned-Mathlib
instance found: (a) Dirichlet–Jordan pointwise convergence for the
piecewise-AC midpoint class, (b) the universal sine-harmonic bound `C_sin`.
Both are named suppliers, not hand-waves; the quantitative `V_k` (Test 1)
feeds `W_k`.

## TEST 4 — ROOT-ENERGY INEQUALITY (route, with the crosswalk of Test 3)

With `isometry(x_k) = F(g_k)` a.e. (Test 3) and `g_k` = the Abel-limit
representative = production `E_star(f_k)` restricted to the window plus the
exact C13 shadow `+(1/2) f_k(0) sqrt(u)` (sign as locked by the verdict):

```text
g_k in log coordinates: piecewise-C1 with finitely many jumps
  (seams u = lambda_k/n, window endpoints), smooth shadow;
finite-jump Fourier decay: |F(g_k)(t)| <= C_k/(1+|t|),
  C_k = (sum of |jumps|)/pi + ||(g_k)'||_{L1(pieces)}   (one integration by
  parts per piece; exact, elementary);
root energy:
  B_k := || sqrt(mu_arch + c_shift) * F_L2(x_k) ||_2^2
      <= integral (C_arch*(1+log(2+|t|)) + c_shift) * C_k^2/(1+|t|)^2 dt
      < infinity                      [log against 1/t^2 converges],
using the exact symbol envelope (ExactArchSymbolLogDomination) for the
weight.  FINITENESS for each fixed k: ROUTE COMPLETE (modulo Test 1's V_k
certificate feeding C_k).
cofinal growth: C_k collects ~lambda_k^2 seams with amplitudes
  sqrt(lambda/n)*|f_k(lambda^-)| (source-scaled edge values are
  O(lambda^-2)-small by the F72 chain at the edge) plus the interior
  derivative mass — a polynomial(-log) bound B_k <= poly(lambda_k) is the
  P_ABEL_ROOT_4 = 0.78 expectation; PLAUSIBLE, not derived here.
```

## TEST 5 — DOWNSTREAM SUFFICIENCY

Two distinct consumers, answered separately:

```text
(a) DEFINEDNESS of the radical/window pairing identities (the 3C.1.7-8
    representation): needs ONLY B_k < infinity for each fixed k — the
    shifted-form pairing is then defined on the Abel limit.  The route
    above delivers this level.
(b) the eventual polarized RATE (dual_sup = o(m^{1/4}/L^{3/2})): will need
    a quantitative B_k (polynomial-log) and more — this is a LATER supplier
    (U-chain), and per the directive we do NOT prove more than consumer (a)
    needs at this stage.
```

## MANDATORY PLANTS

1. **FULL_ENDPOINT_VS_MIDPOINT_ESTAR_SEAM_PLANT** (verdict's, reproduced):
   compactly supported `f` with `f(lambda^-) != 0`; at `u = lambda, n = 1`:
   full-endpoint E-star contributes `sqrt(lambda)*f(lambda^-)`, midpoint
   contributes half of it — unequal pointwise, equal as L2 classes after a
   finite set of points.
2. **L2_WITHOUT_SHIFTED_ROOT_ENERGY_PLANT** (verdict's, reproduced):
   `|ghat(t)|^2 = 1/(|t| log^2|t|)` for `|t| >= e`: `integral |ghat|^2` is
   finite (so L2), but `integral log(2+|t|)*|ghat|^2 = infinity` — an L2
   vector OUTSIDE the shifted form domain.  Plain L2 convergence is never a
   form-domain certificate; this is exactly why Tests 3-4 go through the
   literal isometry and the weighted bound.
3. **CONDITIONAL_SERIES_VS_TSUM_PLANT** (retained): alternating harmonic —
   conditional value log 2, Mathlib `tsum` junk 0; the Abel family remains
   the only production-compatible object for the reflected series.

## FORBIDDEN CHECK

```yaml
production_packet_called_midpoint: no (Test 1 separates them; a.e. transport only)
pointwise_equality_where_ae: no (seam plant; (vi) of Test 3 concludes a.e. only)
hilbert_density_as_form_core: not used
lsc_as_equality: not used
ordinary_fourier_estimated_without_isometry_identification: no — Test 3
  supplies the identification BEFORE any decay estimate is consumed
api_absent_from_pinned_mathlib_imported: none (route B of Test 3 avoids
  Plancherel entirely; pinned FourierTransform layer suffices)
C0_rate_differentiated: no
form_domain_membership_called_gamma_rate: no (Test 5 separates (a) from (b))
lean_numerics_aristotle_promotion_rhclaim: none
```

## PREDICTION CHECK

```text
P_ABEL_ROOT_1 = 0.99 (full-endpoint vs midpoint differ at seams, agree
  a.e.): CONFIRMED (Test 1, plant 1).
P_ABEL_ROOT_2 = 0.84 (tail-splice yields a quantitative variation
  certificate): ROUTE CONFIRMED, certificate NOT YET DERIVED (the named
  V_k supplier).
P_ABEL_ROOT_3 = 0.62 (local Plancherel without upgrading Mathlib):
  CONFIRMED IN STRENGTHENED FORM — the finite-measure window makes even
  local Plancherel unnecessary; the L1∩L2 uniform-limit argument closes
  the crosswalk with pinned API only.
P_ABEL_ROOT_4 = 0.78 (finite-jump decay proves membership with a
  polynomial bound): ROUTE CONFIRMED for finiteness per k; the polynomial
  cofinal bound remains the expected but underived quantitative half.
LIKELIEST_FAILURE (pinned Mathlib L2-Fourier or weighted crosswalk gap):
  DEFUSED — the crosswalk gap is closed by the Test-3 route; the weighted
  half reduces to the V_k certificate.
```

## SUPPLIERS AFTER THIS PREFLIGHT (ranked)

```text
W1: SOURCE_ISOMETRY_EQUALS_POINTWISE_FOURIER_ON_WINDOW (Test 3 route —
    theorem-sized, elementary, pinned-API-only; unlocks ALL later weighted
    estimates; the single highest-value Lean target of this chain).
W2: SELECTED_PACKET_VARIATION_CERTIFICATE V_k (Test 1; from tail-splice
    derivative data).
W3: DIRICHLET_JORDAN + SINE_HARMONIC_UNIVERSAL_BOUND (two classical
    imports for the Abel L2 lock; W1 does not need them — only the Abel
    limit construction does).
W4: FINITE_JUMP_DECAY + ROOT_ENERGY B_k (Test 4; consumes W1 + W2).
W5: quantitative cofinal B_k (only for the later rate stage, per Test 5).
```

SUCCESS_CODE_RETURNED: ABEL_LIMIT_SHIFTED_FORM_DOMAIN_ROUTE_FOUND
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
