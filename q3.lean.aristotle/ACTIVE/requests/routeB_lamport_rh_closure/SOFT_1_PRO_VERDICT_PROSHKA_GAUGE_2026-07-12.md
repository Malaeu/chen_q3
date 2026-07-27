# SOFT_1 — PRO VERDICT (Proshka V1, round 2: gauge + distributional) — 2026-07-12

Status: `EXTERNAL_VERDICT_TRANSCRIPT_VERBATIM / AUTHORITY_FOR_SOFT_1_GATE / NOT_RH`
Channel: V1 (Proshka, breaker, kill+repair mandate). Round 2.
Naming note: Proshka's text calls the proposed contract
`SOFT_0_ZeroFreeGaugeAndDistributionalIdentification`; the repo gate name
SOFT_0 is already consumed by `SOFT_0_ROOF_AND_S2_TYPECHECK`. The repo alias
for this contract is `SOFT_1` (frozen; no other new names).

---

## TOP-LEVEL STATUS

```text
SOFT_GAMMA_POSTHOC_QUOTIENT: CLEARED
SOFT_FIXED_GAMMA_FACTOR:     REFUTED
SOFT_ZERO_FREE_GAUGE_REPAIR: CONDITIONAL_VALID
S2_POINTWISE_INTERVAL:       OPEN
RH:                          NOT_RH
Route score:                 4/5
Progress class:              REPRESENTATION_PROGRESS
```

Main answer: gamma_soft,j(z) = gammaC(1/2+iz) * lambda_j^(-iz) DOES clear the
post-hoc-quotient objection (defined before the limit, not constructed as
F/(c*Xi)). BUT it is NOT one fixed factor gamma in F_{j_k} -> c*Xi*gamma,
because lambda_j^(-iz) depends on j.

## 1. AUDIT OF gamma_soft

For z in S = {|Im z|<1/2}, s(z)=1/2+iz has 0<Re s<1. Gamma(s/2) has no zeros;
its poles are not in 0<Re s<1; pi^(-s/2) is a nonzero exponential factor;
possible s(s-1) factors vanish only on the strip boundary; lambda^(-iz) =
e^(-iz log lambda) is entire and nowhere zero for lambda>0. Hence, provided
the exact gammaC contains no hidden zeta factor or internal denominator,
gamma_soft,j is in O(S)^x — a genuine independent zero-free factor.

BUT it gives no fixed-factor S2: |lambda_j^(-iz)| = lambda_j^y, so at any
fixed 0<eta<1/2 the family blows up as lambda_j -> infinity; the family is
not locally bounded on compacts entering the upper half-strip. On a real
interval, e^(-ix log lambda_j) has ever higher frequency; if log lambda_j ->
infinity there is no pointwise-convergent subsequence on the whole interval
(L2(I) distance between well-separated members tends to 2|I|, not 0).

CONCLUSION: gamma_soft,j is a lawful GAUGE FAMILY, not a fixed limit factor.

## 2. CORRECT REPAIR: zero-free gauge, not fixed gamma

Do not force gamma_soft,j to converge. Remove it BEFORE Montel/Vitali:
define, with exact source-locked orientation,
  Ftilde_j(z) := F_j(z) / gamma_soft,j(z)
(or the exact inverse if D0.6 records the completed tracker with the
reciprocal factor). Since gamma_soft,j is zero-free: Z(Ftilde_j) = Z(F_j),
the real-zero roof is preserved. Correct soft hypotheses:
  {Ftilde_j} locally uniformly bounded in S;
  Ftilde_{j_k} -> c*Xi locally uniformly (or to c*Xi*gamma_0 with gamma_0
  FIXED, j-independent).

### GaugeSoftSubsequenceZeroEscape (proved)

Assume: (1) F_j in O(S); (2) all zeros of F_j in S are real; (3) gamma_j in
O(S)^x; (4) Ftilde_j := F_j/gamma_j; (5) some subsequence Ftilde_{j_k}
converges locally uniformly to c*Xi, c != 0. Then all zeros of Xi in S are
real, hence RH. Proof: division by a zero-free gauge does not change zeros;
a nonzero locally-uniform limit of real-zero functions acquires no non-real
zeros (Hurwitz). QED.

## 3. ATTACK (a): unconditional pointwise explicit formula for F_j(x) on I?

VERDICT: does not exist in the current source-locked corpus. For Xi(x) itself
unconditional representations exist (eta-series, functional equation,
approximate functional equation, Guinand–Weil prime–Gamma explicit formula).
For the detector tracker F_j(x) there is NO current unconditional theorem
F_j(x) = c*Xi(x)*gamma_j(x) + R_j(x) with sup_I |R_j| -> 0. Explicit formula
defines forms, pairings, matrix entries, sums over primes and zeros — it does
not automatically give pointwise convergence of eigenvector transforms to Xi.
Current D0.7e.5/H3c blockers: delta_dict missing; joint (m,N)-limit missing;
uniform compact constant missing; Xi limit identification missing.
FIREWALL: the discrete |A(rho)|^2 moment uses 1-rho = conj(rho), i.e. RH;
unconditional is the full Landau–Gonek type sum, not the critical
modulus-square substitute. Pointwise Variant A/B is therefore NOT posed.

## 4. REALISTIC S2: distributional identification

The machinery naturally produces explicit-formula PAIRINGS, not pointwise
values. Cheapest representation shift: do not prove F_j(x) -> c*Xi(x) for
each x; prove
  for all phi in C_c^inf(I):
    integral_I Ftilde_j(x) phi(x) dx  ->  c * integral_I Xi(x) phi(x) dx.
Name: SOFT_S2_DISTRIBUTIONAL_EXPLICIT_FORMULA.

WHY SUFFICIENT: let S1 give a normal family and Ftilde_{j_k} -> F locally
uniformly. Then for every phi: <F,phi> = c<Xi,phi>, so F = c*Xi as
distributions on I; F - c*Xi is continuous, hence zero on I; the identity
theorem gives F == c*Xi on the connected strip.

FIREWALL: the pairing theorem must come from the prime/Gamma side or the full
symmetric zero-sum; NOT from critical-line-only zeros, |A(rho)|^2 moments,
BFM-type RH-conditional input, or the assumption F_j -> Xi.

## 5. ATTACK (b): what if Fhat_j(0) -> 0?

Case 1 (nonzero but -> 0): the anchor G_j(0)=Xi(0) still works; zero-limit
collapse excluded; but dividing by small bDet_j can inflate the family on
other compacts — S1 becomes a real, not formal, estimate.
Case 2 (Fhat_j(0)=0 on an infinite subsequence): central normalization is
unlawful. CONCRETE FALLBACK: take z_* = i*eta, 0<eta<1/2, e.g. z_* = i/4,
ell(f) := f(z_*). Why better than the center:
  (1) by the real-zero roof, F_j(i/4) != 0 ALWAYS;
  (2) s_* = 1/2 + i(i/4) = 1/4;
  (3) zeta(1/4) != 0 unconditionally: the eta-series is positive for 0<s<1
      and 1-2^(1-s) < 0 there, so zeta(s) < 0;
  (4) the completion factor is zero-free, so Xi(i/4) != 0.
After gauge removal set a_j := c*Xi(i/4)/Ftilde_j(i/4), H_j := a_j*Ftilde_j;
then H_j(i/4) = c*Xi(i/4) != 0. Fixed functional; j-independent; zero-set
preserving; no RH; no cofinal central nonvanishing needed.
NOT free S1: Ftilde_j(i/4) can still tend to 0 and a_j can grow — local
boundedness must be proved independently.
  NONREAL_ANCHOR_WELL_DEFINED:   GREEN under real-zero roof
  NONREAL_ANCHOR_UNIFORM_CONTROL: OPEN

## 6. ATTACK (c): which accumulating set is realistic?

NOT sufficient: x=0 alone; finite value sets; the four probe cells
m=13,14,53,101; the first few zeta zeros; prime nodes on a fixed segment;
moving samples without a mesh theorem. Xi zeros have no accumulation point
inside the strip.
Realistic option 1 — DISTRIBUTIONS (best): pairings against phi in
C_c^inf(I); no point set needed; this is what explicit formula is for.
Realistic option 2 — CONDENSING GRID (`MovingGridToIntervalBridge`): if
D0.6/H3c supplies grids X_j subset I with fill distance h_j -> 0 and
max_{x in X_j} |Ftilde_j(x) - c*Xi(x)| -> 0, then S1 on a slightly larger
compact gives via Cauchy estimates sup_I |Ftilde_j'| <= C_{K'}, and
sup_I |Ftilde_j - c*Xi| <= max_grid + (C_{K'} + ||Xi'||_I) h_j -> 0.
Realistic but the current two-parameter (m,N) ledger does not yet supply the
mesh theorem.
Realistic option 3 — fixed sequence x_* + 1/n: has an accumulation point but
requires unconditional convergence at EVERY fixed point of the set; only the
central calibration exists today, so not posed.

## ROUTE MAP

```text
source-locked gamma_soft,j
   | zero-free on S
   v
GaugeRemoval: F_j -> F_j/gamma_soft,j
   |                         |
   v                         v
real-zero preserved     independent S1 (local normality)
    \                       /
     v                     v
   cluster subsequence exists
              |
              v
distributional explicit-formula identification on I
              |
              v
       cluster point = c*Xi
              |
              v
           Hurwitz
              |
              v
             RH
```

THE REAL WALL NOW: SOFT_S2_DISTRIBUTIONAL_EXPLICIT_FORMULA. Not gamma.

## STRONGEST ATTACKS

(1) "Your gamma_soft,j is independent of Xi but depends on j. On the upper
half-strip its modulus is lambda_j^(Im z), so it destroys the normal-family
bound itself. You cannot both treat it as a fixed limit factor and use
Montel." — fatal for the ORIGINAL S2 wording.
(2) "Explicit formula gives pairing/quadratic-form information. Where is the
theorem converting this into pointwise convergence of eigenvector transforms
on an interval?" — no such theorem exists today.

## FINAL PROPOSAL

Do not rebuild the tree for pointwise S2. One theorem contract (repo alias
SOFT_1) must fix:
 1. exact formula gamma_(m,N)(z) = gammaC(1/2+iz) * m^(-iz/2);
 2. proof gamma_(m,N) in O(S)^x;
 3. exact orientation Ftilde_(m,N) = F_(m,N)/gamma_(m,N) or exact inverse;
 4. zero-set preservation;
 5. central anchor under BDetNonzero;
 6. fallback ell(f) = f(i/4);
 7. S2 not as pointwise formula but as
    for all phi in C_c^inf(I): <Ftilde_j,phi> -> c<Xi,phi>;
 8. full RH-conditional import audit.

STOP CODES:
```text
SOFT_GAMMA_INTERIOR_POLE
SOFT_GAMMA_NOT_ZERO_FREE
SOFT_GAUGE_ORIENTATION_MISSING
SOFT_GAUGE_NORMALITY_GAP
SOFT_EXPLICIT_FORMULA_ONLY_QUADRATIC
SOFT_S2_RH_CONDITIONAL_IMPORT
SOFT_ANCHOR_FUNCTIONAL_ZERO
SOFT_JOINT_LIMIT_QUANTIFIER_MISSING
```

## META CLOSEOUT

Smaller: the main wall is no longer "find an independent gamma" but
"identify the gauge-corrected cluster point DISTRIBUTIONALLY on a real
interval". Killed: post-hoc quotient objection; fixed-gamma reading of
lambda_j^(-iz); sup-normalization; four probe points as S1; the center as the
only possible anchor; pointwise explicit formula as the only path. Preserved:
real-zero roof + zero-free gauge + normal family + unconditional
distributional identification => RH.

NOT_RH.
