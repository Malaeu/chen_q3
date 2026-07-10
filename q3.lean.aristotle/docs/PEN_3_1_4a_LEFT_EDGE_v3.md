# PEN NOTE 3.1.4a — LeftEdgeLeakage (v3.1: cleared for docs + F-results)

STATUS: v3 passed adversarial round 2 (PASS-TO-DOCS, two micro-edits
applied). v3.1 integrates bus-003 falsifier results (Section 9).
Label per adversarial ruling: "conditional diagnostic lemma,
integer-lambda^2 branch only". Node 3.1.4.1 of PROJECT_TREE.

---

## 0. CONVENTION BOX

Finite Fourier convention (Bonami–Karoui): F_c f(x) = int_{-1}^{1}
e^{+i c x y} f(y) dy; mu_n = i^n sqrt(2 pi lambda_n(c)/c);
||psi_{n,c}||_{L2[-1,1]} = 1. Any e^{-...} step downstream conjugates the
phase first (code PHASE_BOOK_SIGN_CONVENTION_GAP).
Starred endpoint convention: at x = lambda (jump point, hit by
m = lambda^2 at u = lambda^{-1}) both sides use f(lambda) := f(lambda^-)/2:
  sum*_m f(m/lambda) := sum_{m < lambda^2} f(m/lambda) + (1/2) f(lambda^-).
Mismatch code: POISSON_ENDPOINT_HALF_WEIGHT_MISMATCH.
BRANCH: main statement = INTEGER BRANCH lambda^2 in Z (Section 5).

## 1. Exact identities

(I1) eigenrelation for all x; (I2) fhat_n(xi) = lambda mu_n
psi_{n,c}(xi lambda/c); (I3) starred Poisson at the left edge;
(I4) node identity fhat(2 pi k lambda) = lambda mu_n psi_n(k), k = 1 the
BK endpoint. NOVELTY: (I4) itself is the standard eigenrelation at
exterior points (integer PSWF samples: Walter–Shen sampling literature);
claimed as new is ONLY the deployment: Poisson nodes of E(f) ->
integer-sampled extended prolate -> k = 1 = BK endpoint -> left-edge
leakage budget inside a zeta explicit-formula pipeline.

## 2. H2 — two-fork lemma

RETRACTED v1 sentence: "the Weil admissible class forces f(0) = 0".
Correct: the CC class S_0 has f(0) = 0 BY DEFINITION; whether the
concrete g_04 constructor lands in S_0 is exactly F0.
  H2-ZERO fork: g_04(0) = 0 (by an exhibited constructor CONSTRAINT,
    not a numerical near-zero — Section 7 rubric). No pole term.
  H2-POLE fork: int g_04 = 0, g_04(0) != 0. Carry the explicit
    counterterm; its FULL contribution to K is
      - (g_04(0)/2) * (lambda^{1/2 - i gamma} - lambda^{-1/2 + i gamma})
                      / (1/2 - i gamma),
    and cancellation against the tau-block is proven POLE-BY-POLE with
    matched sign, half-weight, and Mellin normalization — else the packet
    is re-projected onto S_0 (one extra linear condition on c_n).
    "Cancellation is structural only if every residue matches;
    otherwise wishful."

## 3. Exterior decay: certified-remainder framing

Exact display (even n, two IBPs, X = ck):
  mu_n psi_n(k) = 2 psi_n(1) sin X / X
                + (chi_n - c^2) psi_n(1) cos X / (c^2 k^2) + R_2(k),
with 2 psi_n'(1) = (chi_n - c^2) psi_n(1) (Sturm–Liouville endpoint).
INTEGER BRANCH: sin X = 0, cos X = 1 exactly:
  mu_n psi_n(k) = (chi_n - c^2) psi_n(1) / (c^2 k^2) + R_2(k).
The asymptotic "psi_n(k) ~ -lambda psi_n(1)/k^2" is MOTIVATION ONLY:
the honest IBP parameter is ~1/k (edge derivatives cost powers of c).
For k = 2, 3, 4: FINITE CERTIFIED TABLE (bus 003 / F1 — see Section 9:
the k^{-2} law was REFUTED there; the boundary algebra above remains
exact, but the remainder LEADS). For k >= 5: named obligation, upgraded
in Section 9 to CERTIFIED_STAIL_BOUND.

## 4. Lemma LeftEdgeLeakage-IntegerBranch (CONDITIONAL; v3.1 form)

Label: conditional on { H2 fork resolved } + { certified S_tail } +
{ starred endpoint convention }.
Statement (lambda^2 in Z; H2-ZERO or H2-POLE with counterterm):
  |E(g_04)(1/lambda)| <= lambda^{3/2} |mu| ( |psi(1)|-combo + S_tail ),
  S_tail := sum_{k>=2} |sum_n c_n mu_n psi_n(k)| / |mu|  — a NAMED
  CERTIFIED QUANTITY (numeric certificate per working point; analytic
  obligation CERTIFIED_STAIL_BOUND via WKB-phase amplitude control).
Zero-sum consequence (unchanged class, now certificate-based):
  2 sum_{gamma > Gamma} |B_L|^2 <= C' lambda^3 (log lambda) E.
This does NOT migrate into the main chain as unconditional until the
obligations are discharged.
GENERIC BRANCH (never in the concluding chain): keep the k^{-1} endpoint
term; class degrades ~ one endpoint order; G3a budget not re-verified.
Code: GENERIC_LAMBDA_EDGE_LEAKAGE_BUDGET_GAP.

## 5. Integer branch suffices — via a NAMED import

Required imported detector lemma:
  AlphaDetectorPointwise:
    not-RH  =>  exists c_0 > 0, exists Lambda_0,
                forall lambda >= Lambda_0:  alpha(lambda) >= c_0.
PROJECT STATUS: direction (i) of node 2.1 (AlphaDetector equivalence),
pen-proven CONDITIONAL on the unconditional cap |a| <= poly * E (= G3a).
POINTWISE in lambda (off-line zero pair pumps fixed spectral mass at
every large lambda) — hence restricts to every divergent sequence.
Integer-branch argument: lambda_j = sqrt(j) -> infinity; witness
liminf_j alpha(lambda_j) = 0 contradicts AlphaDetectorPointwise => RH.
Consumption chain: G3a -> AlphaDetectorPointwise -> integer witness.
If the detector were only averaged/smoothed, this section FAILS
(adversarial condition adopted).

## 6. Verbatim literature imports

(B1) Bonami–Karoui, arXiv:1012.3881v3, eq. (43):
  d/dc ln lambda_n(c) = 2 |psi_{n,c}(1)|^2 / c   [VERIFIED, twice].
CONSTANT CAVEAT: derivative identity; psi(1)^2 ~ c(1 - lambda_n) must be
DERIVED from a stated asymptotic with explicit constants (pi/2-type
factor in the Kulikov normalization). TODO: lambda^11 prefactor constant.
(B2) Kulikov, arXiv:2603.07407, Theorems 1.6 / 1.7 (pre-plunge);
convention conversion c_K = 2 c_BK / pi (= 52 at c_BK = 2 pi * 13);
n in {0, 4} fine; GUARD: unspecified c_0 => scaling law only.

## 7. Falsifier mapping (bus) + F0 rubric

F0 -> H2 fork. STRICT RUBRIC (pre-registered): numerical near-zero is
NOT H2_ZERO; required is the exhibited constructor CONSTRAINT row, plus
numeric cross-check. Numeric-only => H2_NUMERIC_ONLY => follow-up gate.
Forbidden: no numerical zero; no "admissible hence f(0)=0"; no dropping
-g_04(0)/2; no Section 4 before F0.
F1 -> certified table (outcome: Section 9). F2 -> direct-vs-Poisson
under the starred convention (outcome: Section 9).

## 8. Remaining attack surface (v3.1)

(a) H2 constraint-row exhibition (goal 006/G1).
(b) CERTIFIED_STAIL_BOUND (analytic; WKB-phase amplitude).
(c) lambda^11 prefactor CONSTANT derivation.
(d) Assembly of B_L into the 3.1 triangle line (3.1.4.2 pending).
(e) AlphaDetectorPointwise quantifier form frozen in the node-2.1
    paper statement.
(f) EDGE_SAMPLE_AMPLITUDE: why the integer-sample amplitude is ~0.017
    psi(1) (WKB phase near pi/2? — open).

## 9. F-RESULTS (bus 003) — integrated [v3.1]

F0: |g_04(0)| / ||E(g_04)|| = 3.26e-60. Packet structure revealed:
  g_04 = h0/h4 (modes n = 0 and 4 ONLY) — two modes, two S_0 conditions
  (int f = 0, f(0) = 0): an exactly determined constructor. Status per
  rubric: H2_HOLDS(numeric); constraint row = goal 006/G1.
F1: SIN_VANISHING_REFUTED as the DOMINANT small-k mechanism:
  ratios |psi_n(k)| k^2/(lambda |psi_n(1)|) = 0.019..0.073 for k = 2..4
  (registered band was [0.5, 1.5]); erratic signs; power fits
  p = 0.24..1.24 over k = 2..8. Boundary sin-terms DO vanish (exact),
  but the integral remainder LEADS — consistent with a WKB turning-point
  PHASE: far field ~ cos(ck - theta_n)/x, integer samples ~
  cos(theta_n)/k with small amplitude ~ 0.017 psi(1) (n = 0).
  Quadrature validated against the Legendre/Bessel closed integral
  (rel. 1e-38..1e-42). Named open object: EDGE_SAMPLE_AMPLITUDE.
F2: NODE IDENTITY (I4) CONFIRMED at 1.2%: direct -1.63792e-29 vs
  Poisson(k<=8) -1.65715e-29; magnitude 3.4898e-29 INSIDE the registered
  band => the class lambda * k_edge * O(1) survives EMPIRICALLY.
  Mismatch 1.17%: NOT the half-tooth convention (half-tooth 2.4e-30 abs
  vs measured diff 1.9e-31 — 12x smaller); registered hypothesis:
  truncation of the slowly decaying signed Poisson tail at k = 8
  (decided by goal 006/G2, extension to k <= 40).
K1 plant: structurally INERT for h0/h4 (i^0 = i^4 = +1) — design flaw
  of the plant, not a pass; redesigned conjugate-convention plant in
  goal 006/G4.
NET: the analytic k^{-2} ROUTE is dead at small k; the IDENTITY, the
  MAGNITUDE CLASS, and the H2 resolution stand. The lemma of Section 4
  is restated certificate-based (S_tail).
