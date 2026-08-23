# H2A.4.1B.3C.1.3 — selected Ferrers E-star-to-Gamma source-action crosswalk preflight (READ-ONLY)

```yaml
PRIMARY: H2A_4_1B_3C_1_3_SELECTED_FERRERS_ESTAR_TO_GAMMA_SOURCE_ACTION_CROSSWALK_PREFLIGHT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex unavailable
TASK: verdict 1386ded1 — CODEX DIRECTIVE (REQ-2026-08-22-V)
MODE: READ_ONLY
LEAN_EDIT: false
ARISTOTLE_USED: false
NUMERICS_USED: false
BASE_HEAD: 1386ded1e7c6a26f47d9de2c31958e58a5aca160

OUTCOME_CODE: DERIVATIVE_PROXIMITY_CONTROLS_ROW_NOT_RIESZ_RESIDUAL

FILES_READ:
  - Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean (defs 596-634, identities 636-757)
  - Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualVariance.lean
  - Q3/Proofs/RouteB/G6N1SelectedFerrersCommutatorResidualDefect.lean (3B Gamma structure)
  - Q3/Proofs/RouteB/G6N1SelectedFerrersEStarWindowMainError.lean
  - Q3/Proofs/RouteB/G6N1ExplicitCCMLimitBeyondSourceWindowTail.lean
  - Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean
  - Q3/Proofs/RouteB/D0PstarSourceWeilSesquilinearForm.lean
  - Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean
  - Q3/Proofs/RouteB/CCMFiniteWeilShiftedRankOne.lean (rank-two commutator)
  - docs/routeB_bus/H2A_4_1B_3C_1_2_..._PREFLIGHT_2026-08-23.md (own prior report)

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## TEST 1 — EXACT TYPE CHAIN

All read literally from disk; no "morally equal", no ambient compression, no
renormalization.

```text
selectedFerrersFullEStarError (physical function level):
    s_k * E_star(prolateCombination(pair k)) - E_star(4 * explicitCCMLimitH)
    on the window I_m; NOT a Hilbert vector by itself.

selectedFerrersFactorFourTargetVector (SourceActionSplit.lean:596):
    MemLp.toLp (E_star (fun x => 4 * explicitCCMLimitH x)) : H_m (index k)
    — the target as an L2 window class.

selectedFerrersScaledPhysicalErrorVector (:605):
    sourceScale k • gTrial_m(...) - selectedFerrersFactorFourTargetVector
    : H_m (index k) — the L2 class of the full E-star error.

selectedFerrersFactorFourTargetProjection gE_k (:616):
    P_m_N (index k) (targetVector) : E_m_N (index k).

selectedFerrersScaledPhysicalErrorProjection eE_k (:624):
    P_m_N (index k) (errorVector) : E_m_N (index k).

selectedFerrersFiniteCCMRow q_k:
    the center-normalized selected row (3B/3C files); satisfies the exact
    vector identity (:636): s_k • x_k = t_k • (eE_k + gE_k), t_k = sTrial
    normalizer — pure projection linearity, kernel-checked.

selectedFerrersFiniteCCMResidual r_k = M_k q_k - a_k q_k (coefficients);
selectedFerrersFiniteCCMCommutatorResidualDefect Gamma_k:
    Gamma = S(Dq) + A*beta - B*1, proved componentwise = D * r (3B).

Riesz split (:681): s_k • (R_k x_k - a_k x_k)
    = t_k • ((R_k - a_k) eE_k + (R_k - a_k) gE_k)   — pure linearity.
```

Carrier note: the physical E-star error and Gamma_k live on the same log
window with the same finite Fourier coordinates, but the first is a graph
proximity object and the second is the shifted source-Weil action defect —
two laws, one carrier (the verdict's C04 boundary is respected throughout).

## TEST 2 — HYPOTHETICAL OPTIMAL DERIVATIVE CONTRACT

Assume, for the discriminator only:

```text
(HDC)  mode-weighted coefficient energy of the full physical E-star error
       sum_{|n| <= N_k} n^2 * |c_n(EStarError_k)|^2 = o(sqrt(m_k)/L_k^4),
       with all periodic-endpoint and seam terms included in the coefficients.
```

Exact consequences (projection is coefficient truncation, so no loss terms):

1. `||D eE_k||^2 = sum n^2 |(eE_k)_n|^2 <= (HDC) = o(sqrt(m)/L^4)` — the
   projected-error row derivative is controlled COMPLETELY.
2. For the row: `q_k = t_k*(eE_k + gE_k)` (exact identity), so
   `D q_k = t_k * (D eE_k + D gE_k)`.  Two NEW inputs appear immediately:
   - `||D gE_k||` — the mode-weighted energy of the projected TARGET.  The
     target is smooth and inversion-even (continuous periodic extension;
     derivative jump at the wrap is O(lambda^-7/2)), so `||D gE||^2 = O(1)` is
     PLAUSIBLE — but the E-star chain on disk bounds target VALUES, not
     derivatives (OPEN-3 of the 3C.1.0 report).  Theorem-sized, NEW.
   - `|t_k|` — the trial normalizer.  Its upper bound needs a LOWER bound on
     the trial norm; the assembly ledger lists exactly this as
     GOAL057 step 13 `SelectedTrialNormalizerBounded` with status OWNER_DATA
     (open).  Named as an input, not assumed.
3. Under (HDC) + both inputs: `||D q_k||^2 = O(1) + o(sqrt(m)/L^4)` — the ROW
   is fully controlled in the derivative topology.

This is the maximum the contract yields: coefficients of `eE_k` and (with the
two named inputs) the mode-weighted energy of the row.  Nothing about the
ACTION of `M_k` is implied yet.

## TEST 3 — SOURCE-ACTION TRANSPORT

**The exact skeleton exists on disk and is the honest crosswalk candidate.**
The rank-two commutator (`ccmShiftedWeilMatFinite_commutator`,
CCMFiniteWeilShiftedRankOne.lean:103) gives, with D the mode diagonal:

```text
Gamma_k = D r_k = D (M_k - a_k) q_k
        = (M_k - a_k)(D q_k) + [D, M_k] q_k,
[D, M_k] = rank-two (eta tensor beta - beta tensor eta structure, exact).
```

So a row-derivative contract feeds `Gamma` through exactly two channels:
`(M-a)(Dq)` and the rank-two commutator term.  Channel by channel, against
existing theorems ONLY:

| channel | existing control | status under (HDC) |
|---|---|---|
| rank-two `[D,M] q` | 3A beta-moment lock (`normSq <= betaEnergy * oddMass`), eta/beta pairings, odd-mass rate H2A.3 | REACHABLE — pairings against `q` are value-level; no derivative needed; budget determined by betaEnergy times oddMass, already in the ratified ledger |
| shifted arch on `Dq` | `abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope`: symbol <= C*(1+log(2+t)); resonance localization of modes | CLOSES conditionally: the arch weight at mode `n` is `(1+log(2+n/L))`, strictly weaker than the `n`-weight, so `||arch(Dq)||^2 <= C*L^2-margin * ||Dq||^2`-class — subcritical margin survives under (HDC) |
| `a_k * Dq` | no bound on `a_k` on disk | OPEN input: `abs(a_k)` bound (plausibly O(L) via the smooth-target Rayleigh, but no theorem) |
| W02 on `Dq` | exact rank-two ENDPOINT structure (`sourceW02ModePairing_eq_rankTwoEndpointModeValues`) | NOT closed by (HDC): the W02 pairing evaluates ENDPOINT VALUES of the derivative of the synthesis; an L2-type mode-weighted contract does NOT control boundary traces.  A C0-derivative (trace) layer at the window edge is an additional, distinct input |
| retained prime on `Dq` | only `norm_sourcePrimeSesquilinearForm_apply_le` (opNorm; Chebyshev scale sqrt(m)) — forbidden as positive route | OPEN, irreducible in this representation: the oscillatory von-Mangoldt pairing estimate does not exist on disk; the absolute bound is supercritical (kill bound) |
| prime/W02/arch on `gE` (projected target action) | none | the smooth fixed target makes the prime pairing decay in `log k` (bandwidth truncation), so `(R-a) gE` is PLAUSIBLY O(1)-class — theorem-sized, NEW, not on disk |

**Conclusion of Test 3.**  Even the optimal derivative contract, with the two
Test-2 inputs granted, controls the ROW and reaches exactly ONE of the three
source components of the Riesz residual action (shifted arch).  The W02
channel needs a boundary-trace layer that no L2-derivative contract supplies;
the retained-prime channel needs the oscillatory identity that has been open
since 3C.1.0 (OPEN-2); `a_k` and the target action need their own (plausible,
smaller) theorems.  No existing theorem identifies the physical E-star
derivative with `Gamma_k` or with any of these channels — the commutator
skeleton is the closest disk object and it is an algebraic identity, not a
rate.  Hence:

```text
DERIVATIVE_PROXIMITY_CONTROLS_ROW_NOT_RIESZ_RESIDUAL.
```

## TEST 4 — PERIODIC ENDPOINT QUOTIENT

Seam phases `x_r = log(lambda/r)/L`, `1 <= r <= m`, `L = 2*log(lambda)`.

1. **Collision (as the verdict found):** `x_1 = +1/2`, `x_m = log(lambda/m)/L
   = log(1/lambda)/L = -1/2` — the same class mod 1.
2. **Quotient:** merge the two atoms.  In the integer-mode detector the
   combined amplitude at mode `n` is `(-1)^n * (J_(k,1) + sigma * J_(k,m))`
   with the orientation sign `sigma` fixed by the jump directions (the `r=1`
   cut enters the window from above, the `r=m` cut leaves it at the bottom
   edge; both jumps are carrier cuts of the same sign convention, so the
   amplitudes ADD with their own signs — the exact `sigma` is determined by
   the two one-sided limits and is a bookkeeping constant, not an estimate).
   Amplitude budget: `|J_1|^2 ~ C^2/lambda^3`, `|J_m|^2 ~ C^2/lambda^5`;
   the combined atom obeys `|J_combined|^2 <= 2*(C^2/lambda^3 + C^2/lambda^5)
   = O(1/m^(3/2))` — same class as the largest single seam.
3. **No further collisions:** for `2 <= r < r' <= m-1`,
   `x_r - x_r' = log(r'/r)/L` with `0 < log(r'/r) < log(m) = L`, hence the
   difference lies strictly in `(0, 1)` — distinct mod 1.  PROVED elementary.
4. **Separation after the quotient:** adjacent gap
   `log(1+1/r)/L >= 1/((r+1)*L) >= c/(m*L)` — the `delta >= c/(m*L)` claim
   survives the quotient.  PROVED elementary.
5. **Sieve exponent:** `(2N + delta^-1) = O(m*L)` unchanged; the seam budget
   remains `O(L^3/sqrt(m))`, ratio to threshold `L^5/m -> 0`.  The
   subcritical power-of-m margin is intact; the quotient costs a constant.
   (The nonharmonic large-sieve inequality itself remains the named external
   classical input M3 — unchanged status.)

Judge prediction P_GAMMA_CROSSWALK_3 = 0.95: CONFIRMED by this arithmetic.

## TEST 5 — SOURCE LEDGER (component-by-component; kill bounds only, the
combined Gamma stays the consumer)

```yaml
shifted_arch:
  on_Dq: closes under (HDC) via the log-symbol domination (margin: n-weight
    vs log-weight); the ONLY component reachable today
  status: CONDITIONALLY_GREEN (needs HDC itself, which is unproved)
W02:
  on_Dq: rank-two endpoint values of the derivative of the synthesis;
    L2-derivative contract gives no boundary trace
  status: OPEN — needs an endpoint C0-derivative (trace) layer;
    kill bound (opNorm ~ sqrt(m/L)-scale factors) supercritical
retained_prime:
  on_error_component: oscillatory Lambda(k)/sqrt(k) pairing estimate absent;
    absolute Chebyshev bound ~ sqrt(m) opNorm is a kill bound only
  status: OPEN — the irreducible wall of this representation (OPEN-2 lineage)
  on_target_component: smooth fixed target truncates the pairing in log k;
    plausibly O(1)
  status: PLAUSIBLE_THEOREM_SIZED, NEW, not on disk
projected_factor_four_target:
  (R-a) gE as a whole: no action theorem exists; the smoothness argument
    above covers prime; arch on gE is log-weighted O(1)-class; W02 on gE is
    an endpoint value of the target derivative — explicit, computable,
    Gaussian-small
  status: PLAUSIBLE_THEOREM_SIZED, NEW
scalars:
  a_k: no disk bound; plausibly O(L); OPEN input
  t_k (normalizer): needs SelectedTrialNormalizerBounded = GOAL057 step 13,
    listed OWNER_DATA; OPEN input
```

## FORBIDDEN CHECK

```yaml
EStarError_identified_with_Gamma: no (Test 1 separates the laws; Test 3 goes
  through the exact commutator skeleton only)
source_action_inferred_from_proximity_without_theorem: no (every channel that
  lacks a theorem is marked OPEN)
target_defect_zero_from_inversion_evenness: not inferred (target-side terms
  carried as open theorem-sized inputs)
absolute_row_sums_or_ambient_opNorm_as_positive_route: no (kill bounds only)
periodic_endpoint_collision_ignored: no (Test 4 performs the quotient first)
lean_written_or_aristotle_submitted: no
```

## PREDICTION CHECK

```text
P_GAMMA_CROSSWALK_1 = 0.97: CONFIRMED — no theorem on disk identifies the
  physical E-star derivative with Gamma; the closest object is the exact
  rank-two commutator identity, which is algebra, not a rate.
P_GAMMA_CROSSWALK_2 = 0.90: CONFIRMED — the optimal contract controls the
  row (given the target-derivative and normalizer inputs) and leaves the
  retained prime action open; additionally the W02 boundary-trace layer is
  open, which the prediction did not name.
P_GAMMA_CROSSWALK_3 = 0.95: CONFIRMED — the endpoint quotient repairs the
  spacing at constant cost; the subcritical margin survives.
```

## RANKED MISSING INPUTS (updated global picture)

```text
N1 (unchanged wall): oscillatory retained-prime pairing estimate on the
    error component — no representation so far avoids it.
N2: W02 boundary-trace layer: endpoint C0-derivative of the synthesis
    (connects to the seam/edge machinery of 3C.1.2, where edge values are
    already controlled at the VALUE level).
N3: target-side derivative ledger: ||D gE|| = O(1) and (R-a)gE = O(1)-class
    (theorem-sized from the explicit target formulas; NEW analysis).
N4: scalar inputs: |a_k| bound; SelectedTrialNormalizerBounded (GOAL057
    step 13, OWNER_DATA).
M1 (inside the derivative representation): multiplicative interior bound —
    still needed to PROVE (HDC) itself; per this verdict, correctly
    deprioritized until the crosswalk (now mapped) shows what it buys:
    answer — it buys the row and the arch channel, not the consumer.
M3: nonharmonic large sieve after the endpoint quotient (benign, classical).
```

SUCCESS_CODE_RETURNED: DERIVATIVE_PROXIMITY_CONTROLS_ROW_NOT_RIESZ_RESIDUAL
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
