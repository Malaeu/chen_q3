# H2A.4.1B.3C.1.4 — selected Ferrers Rayleigh-centered component discriminator (READ-ONLY)

```yaml
PRIMARY: H2A_4_1B_3C_1_4_SELECTED_FERRERS_RAYLEIGH_CENTERED_COMPONENT_DISCRIMINATOR
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict 7cff44dc — CODEX DIRECTIVE (REQ-2026-08-22-V)
MODE: READ_ONLY
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: 7cff44dce370d7f9d2c4ad82d5edfbc6447c0415

OUTCOME_CODE: COMPONENT_SPLIT_DESTROYS_NECESSARY_CANCELLATION

PREFLIGHT_ASK:
  - "./ask.sh \"selected Ferrers Rayleigh centered component commutator\" — no supplier"
  - "./ask.sh \"W02 corrected commutator endpoint rank two\" — no supplier"
  - "./ask.sh \"prime Rayleigh centered von Mangoldt pairing\" — no supplier"
  - "./ask.sh \"selected sourceScale trial normalizer anchor ratio\" — no NEW supplier beyond the private H2A.3 anchor-ratio helper the verdict names"

SOURCE_LOCKS_READ:
  - "ccmWeilTauN1 = ccmW02Entry - ccmWREntry - ccmPrimeEntryN1 (CCMFiniteWeilSourceMatrixN1.lean:97) — the literal sign convention"
  - "sourceW02ModePairing_eq_rankTwoEndpointModeValues (D0PstarW02AmbientContinuousForm.lean:39): W02(n,r) = conj(minus_n)*plus_r + conj(plus_n)*minus_r"
  - "sourceW02EndpointPlus/MinusModeValue (:12,:19): plus(n) = ∫_{[0,L]} V_n e^{x/2}, minus(n) = ∫ V_n e^{-x/2} — explicit resolvent values"
  - "ccmBetaN1 (CCMFiniteWeilSourceMatrixN1.lean): beta_j = n_j * tau(j, center)"
  - "selectedFerrersFiniteCCMBetaVector/Moment/Energy (3A file:117-136)"

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## TEST 1 — SCALE OMISSION PLANT

One-dimensional scalar example with `s != 1`: take `s = 2, x = 5, t = 1,
e = 4, g = 6`.  Then `s*x = t*(e+g)` holds (`10 = 10`) while `x = t*(e+g)`
fails (`5 != 10`).  The row-derivative consumer is therefore the ratio
`t_k/|s_k|`, exactly as the verdict's repair states:

```text
D q = (t/s) * (D eE + D gE),   relevant scalar: t^2/|s|^2.
```

Existing theorem: the anchor-ratio bound `t_k^2/|s_k|^2 <= L_k/b^2`
(eventually, fixed anchor floor `b > 0`) is kernel-checked as a private
helper inside H2A.3 and consumed by the public odd-mass rate — no new
supplier is opened, no thin wrapper proposed (FORBIDDEN respected).

## TEST 2 — EXACT COMPONENT DECOMPOSITION

Signs read from the source lock: `tau = W02 - WR - Prime` (literal, file
above; no renaming).  With `X in {W02, WR, Prime}` and the SAME complex
selected row, carrier, Rayleigh convention and schedule:

```text
a_k     = a_{W02,k} - a_{WR,k} - a_{Prime,k}          (linearity of <q, . q>, exact);
beta_k  = beta_{W02,k} - beta_{WR,k} - beta_{Prime,k}  (beta_j = n_j * X_{j,center}, linear, exact);
Gamma_k = Gamma_{W02,k} - Gamma_{WR,k} - Gamma_{Prime,k}
          for Gamma_X := D(X - a_X I) q               (linearity of D, exact reconstruction).
```

All three matrices and beta vectors are source-locked disk objects (W02
endpoint form; WR = ccmWREntry with the CCM (4.4) integral; Prime =
ccmPrimeEntryN1 via sourcePrimeModePairing).  Complex-conjugation
conventions checked against the rank-two identity (the star sits on the
first argument).  NO object mismatch.

**New structural finding (theorem-sized, symbolic proof included).**  The
W02 component satisfies its OWN Loewner/divided-difference law, not just as
part of the full tau.  With `a := L/2`, `w := 2*pi`, the endpoint values are
exact resolvents:

```text
plus(n)  = C_p / (a + i*w*n),      minus(n) = C_m / (a - i*w*n),
C_p = sqrt(L)*(e^{L/2} - 1) up to the fixed normalization, C_m analogous.
```

Hence `W02_{jl} = 2*C * Re[ 1/((a + i*w*n_j)(a + i*w*n_l)) ]`, and partial
fractions give

```text
(n_j - n_l) / ((a+i*w*n_j)(a+i*w*n_l)) = [1/(a+i*w*n_l) - 1/(a+i*w*n_j)] / (i*w),
```

so `(n_j - n_l) * W02_{jl} = f(n_j) - f(n_l)` with
`f(n) = (2C/w) * Im[-1/(a+i*w*n)] = 2*C*n/(a^2 + w^2*n^2)`, and one checks
`f(n) = n * W02_{n,0} = beta_{W02}(n)` exactly.  Verified additionally on
the concrete mode pairs `(-1,1)` and `(1,2)`: both sides agree identically.
So the componentwise structured law

```text
(n_j - n_l) * W02_{jl} = beta_{W02,j} - beta_{W02,l}
```

HOLDS for W02, and therefore the two forms of the corrected defect coincide
for this component:

```text
Gamma_{W02} = (W02 - a_{W02} I)(D q) + A*beta_{W02} - B_{W02}*1 = D(W02 - a_{W02} I) q.
```

The same resolvent-times-cosine structure underlies the Q-kernel entries of
WR and Prime, so the componentwise law PLAUSIBLY holds for them by the same
partial-fraction computation — not verified here term by term; if confirmed
(a small dedicated check), each component carries its own exact commutator
identity and the decomposition is fully structured.

## TEST 3 — CORRECTED W02 EXPANSION

Expanding `Gamma_{W02} = D(W02 q) - a_{W02} * D q` with the rank-two law:

```text
(W02 q)_j = conj(minus_j) * P + conj(plus_j) * Mm,
P  := sum_r plus(r) * q_r  = ∫ e^{x/2}  * synthesis(q)(x) dx,
Mm := sum_r minus(r) * q_r = ∫ e^{-x/2} * synthesis(q)(x) dx,

Gamma_{W02} = (D conj(minus)) * P + (D conj(plus)) * Mm - a_{W02} * D q.
```

**Answer to the verdict's question: NO endpoint functional of `D q` remains.**
The correction leaves only (i) two FIXED mode-weighted endpoint vectors
`D conj(minus)`, `D conj(plus)` — explicit resolvent sums, (ii) two
VALUE-LEVEL weighted integrals `P`, `Mm` of the synthesis of `q` itself,
(iii) `a_{W02} * Dq` with `a_{W02} = 2*Re(conj(Mm)*P)` value-level.
P_CENTERED_COMPONENT_2 = 0.90 is CONFIRMED at the structural level; the
boundary-trace input N2 is RETIRED as load-bearing.

**Required falsifier (raw vs corrected).**  Modes `n = (0,1)`, structured
`X = [[0,1],[1,0]]` (Loewner holds with `beta = (0,1)`: `(0-1)*X_{01} = -1 =
beta_0 - beta_1`), row `q = (1,1)/sqrt(2)`.  Then `a_X = <q, Xq> = 1` and
`(X - a_X I) q = 0`, so the corrected defect `Gamma_X = D(X - a_X)q = 0` —
while the RAW term `(X - a_X I)(D q) = (1/sqrt2, -1/sqrt2) != 0`.  Raw
action must never be relabeled as `Gamma_X`.

**Budget (kill ledger, honest).**  The corrected form is structurally clean
but NOT automatically subcritical:

```text
||D conj(minus)||^2 ~ sum_n n^2 * L/(a^2 + w^2 n^2)-scale ~ N * L = m*L;
||D conj(plus)||^2  ~ m * (m*L)-scale factors (C_p^2 carries e^L = m);
P  ~ m^{1/4}-class (the e^{x/2} weight collects the smooth target mass near
     the window middle: ∫ e^{L/4} e^{tau/2} e^{-7|tau|/2} dtau = O(m^{1/4}));
Mm ~ m^{-1/4}-class (mirror computation);
a_{W02} = 2 Re(conj(Mm) P) = O(1)-class.
```

Leading kill bound: `||(D conj(minus)) P||^2 ~ (m*L) * sqrt(m) = m^{3/2} L`
— supercritical against `sqrt(m)/L^2` by `m*L^3`.  The same class for the
plus/Mm term.  So the W02-centered defect is NOT closed by these absolute
bounds; any subcriticality must come from cancellation BETWEEN the two
endpoint terms and/or between components.  "W02 closed" is NOT claimed.

## TEST 4 — CENTERED PRIME PAIRING

Exact expression (source-locked pairing, full signed sum kept):

```text
Gamma_{Prime} = D(Prime - a_{Prime} I) q,
(Prime q)_j = sum_{k <= m} Lambda(k)/sqrt(k) *
              [2 ∫ conj(F V_{n_j})(t) cos(2 pi t log k) (F synth q)(t) dt],
a_{Prime} = Re <q, Prime q>.
```

No absolute-value sum is used as a positive route.  What Rayleigh centering
buys, exactly: subtraction of the projection of `Prime q` onto `q` — i.e.
the leading NONOSCILLATORY (target-diagonal) contribution.  On the
error-free part (smooth fixed target) the pairing decays in `log k`
(bandwidth truncation), so the target-side centered term is plausibly
`O(1)`-class.  On the ERROR part nothing is cancelled by centering: the
kill bound after the known physical error rate remains

```text
||Prime * err|| <= ||Prime||_op * ||err|| ~ sqrt(m) * C/m^{1/4} = C * m^{1/4}
```

(the verdict's `m^{1/4} log m`-class), and the D-weighting worsens it.  The
centered beta vector `beta_{Prime}(j) = n_j * Prime_{j,0}` has resonance
structure (mode `n_j` pairs with `log k ~ 2 pi n_j / L`) with kill-scale
entries `O(L)`-class each — `||beta_Prime||^2` supercritical as an absolute
sum.  **Conclusion: Rayleigh centering gives no asymptotic gain on the
error component; the oscillatory estimate remains the wall** — the judge's
LIKELIEST_FAILURE (no-gain branch) is OBSERVED; no sign mismatch found.

## TEST 5 — TARGET AND SCALAR LEDGER (correct t/|s| factor)

```text
||D q||^2 <= 2 * (t^2/|s|^2) * (||D eE||^2 + ||D gE||^2)
          <= (L/b^2) * (o(sqrt(m)/L^4) + ||D gE||^2)      [anchor ratio, H2A.3]
          =  O(L) * ||D gE||^2 + o(sqrt(m)/L^3).

factor-four target mode-weighted energy ||D gE||^2:
  the target is explicit (E_star of 4*explicitCCMLimitH), inversion-even,
  smooth on the open window; its wrap-around derivative jump is
  O(lambda^{-7/2}); a polynomial-log bound O(polylog) is PLAUSIBLE from the
  explicit formulas WITHOUT new paper input (supports P_CENTERED_COMPONENT_4
  = 0.82) — but the derivative-level decay of the E-star target chain is
  still the OPEN-3/N3 item; not proved here.

selected Rayleigh growth a_k = a_{W02} - a_{WR} - a_{Prime}:
  a_{W02} = O(1)-class (Test 3); a_{WR} = O(L)-class (log-symbol diagonal);
  a_{Prime}: target part O(1)-plausible + error part kill-bounded by
  C*m^{1/4}.  Net: |a_k| <= C*m^{1/4} kill bound, plausibly O(L).  OPEN.

source-scale/normalizer ratio: closed by the existing private anchor-ratio
  helper (Test 1); NOT reopened.
```

## TEST 6 — CANCELLATION FIREWALL

The exact consumer remains the FULL `Gamma_k`.  The repository's own plants
already show the two directions: the 4.1A plant family shows a combined
residual can vanish while separated action terms stay large, and the Test-3
falsifier above is a second exact instance (`Gamma_X = 0`, raw action
nonzero).  Componentwise norm bounds in this report are diagnostics/kill
bounds ONLY; none is promoted to the definition of the consumer.

## WHY THE OUTCOME CODE

The decomposition is algebraically legal and even structurally pleasant
(componentwise Loewner for W02 PROVED symbolically above; reconstruction
`Gamma = Gamma_{W02} - Gamma_{WR} - Gamma_{Prime}` exact).  But the honest
ledgers of the separated centered components are:

```text
Gamma_{WR}  (arch):  subcritical-conditional (log-symbol vs n-weight margin) —
                     the ONLY component with a closing route;
Gamma_{W02}:         m^{3/2} * L-class kill bounds; no closing route without
                     cancellation between its two endpoint terms;
Gamma_{Prime}:       oscillatory wall unchanged; centering removes only the
                     target-diagonal part.
```

Meanwhile the full `Gamma_k` remains the only object with a chance of the
required `o(sqrt(m)/L^2)` smallness — exactly because the W02/WR/Prime
cancellation (the same integral miracle that makes the FULL tau
divided-difference law equal the beta ledger of the Weil explicit formula)
lives BETWEEN the components.  Splitting destroys the necessary
cancellation:

```text
COMPONENT_SPLIT_DESTROYS_NECESSARY_CANCELLATION.
```

The split remains valuable as a diagnostic (it localized the wall to the
W02-Prime cancellation and retired the N2 trace input), but it is not the
positive route.  This assessment favors the verdict's R2
(FULL_SOURCE_WEIL_MELLIN_RADICAL_IDENTITY — preserve the cancellation in
one source-form identity) as the next representation to price, with the new
componentwise-Loewner finding as a cheap structural stepping stone.

## FORBIDDEN CHECK

```yaml
q_eq_t_error_plus_target_without_sourceScale: not used (Test 1 plant kills it)
selectedTrialNormalizerBounded_reopened: no
raw_W02_on_Dq_called_corrected: no (falsifier separates them)
raw_Prime_on_Dq_called_centered: no
prime_declared_unavoidable_before_centered_calculation: no (centered
  calculation performed; the no-gain conclusion is its result, error-part only)
full_Gamma_replaced_by_component_norm_sum: no (Test 6)
absolute_vonMangoldt_as_positive_rate: no (kill bounds only)
inversion_evenness_as_target_action_theorem: no (target bounds marked plausible/open)
large_sieve_before_endpoint_quotient: not used at all here
lean_numerics_aristotle: none
```

## PREDICTION CHECK

```text
P_CENTERED_COMPONENT_1 = 0.99: CONFIRMED — the anchor-ratio helper removes
  the bare-normalizer input (Test 1).
P_CENTERED_COMPONENT_2 = 0.90: CONFIRMED STRUCTURALLY — the corrected W02
  expansion eliminates endpoint traces of Dq (only value-level moments and
  fixed vectors remain); NOT confirmed as a closing budget (kill ledger
  m^{3/2}L without inter-term cancellation).
P_CENTERED_COMPONENT_3 = 0.72: NOT CONFIRMED AS STATED — after the W02
  correction the prime term is NOT the only substantive wall: the W02
  centered defect itself remains supercritical by absolute bounds; the wall
  is the W02-Prime cancellation, not one component.
P_CENTERED_COMPONENT_4 = 0.82: SUPPORTED, not proved — the explicit target
  plausibly admits a polynomial-log mode-weighted/action bound; the
  derivative-level target chain (N3) is still the missing piece.
LIKELIEST_FAILURE: OBSERVED in the no-gain branch (Rayleigh centering gives
  no asymptotic gain on the prime error component); no sign mismatch.
```

SUCCESS_CODE_RETURNED: COMPONENT_SPLIT_DESTROYS_NECESSARY_CANCELLATION
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
