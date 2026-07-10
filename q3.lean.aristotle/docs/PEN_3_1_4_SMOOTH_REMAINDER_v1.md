# PEN NOTE 3.1.4 — SmoothRemainderTail via Poisson (draft v1)

STATUS: DRAFT v1 (Mythos pen). Node 3.1.4 of PROJECT_TREE. Feeds 3.1 -> G3a.
Sub-split introduced: 3.1.4a LeftEdgeLeakage (this note, pen-closed modulo
one flagged import + one construction check) and 3.1.4b
InteriorSmoothRemainder (named, parked).

---

## 0. Setup

f = g_04 = even combination of prolates psi_{n,c} (n in {0,2,4}) on
[-lambda, lambda], c = 2*pi*lambda^2, normalized ||psi||_{L^2[-1,1]} = 1
after rescaling t = x/lambda. E(f)(u) = u^{1/2} sum_{m>=1} f(mu);
window [lambda^{-1}, lambda]. One IBP in the Mellin integral splits
K = K^comb (teeth; nodes 3.1.1-3.1.3) + B_L (left-edge boundary term)
+ K^smooth (AC part; node 3.1.4b). This note bounds B_L.

## 1. Exact identities

(I1) Prolate eigenrelation, valid for ALL x in R:
     int_{-1}^{1} psi_{n,c}(t) e^{i c x t} dt = mu_n psi_{n,c}(x),
     |mu_n| = sqrt(2*pi*lambda_n(c)/c),  mu_n = i^n |mu_n|  (FT phase book).
(I2) Fourier transform of the TRUNCATED rescaled prolate:
     f_n := psi_{n,c}(x/lambda) 1_{[-lambda,lambda]}  ==>
     fhat_n(xi) = lambda * mu_n * psi_{n,c}(xi * lambda / c).
(I3) Poisson at the left window edge (f even, midpoint convention):
     E(f)(1/lambda) = lambda^{1/2} sum_{k>=1} fhat(2*pi*k*lambda)
                      - lambda^{-1/2} f(0)/2,
     using fhat(0) = int f = 0 (Weil condition #1).
(I4) THE NODE IDENTITY (from I2): fhat(2*pi*k*lambda) = lambda*mu_n*
     psi_{n,c}(k) — the Poisson nodes sample the EXTENDED prolate at the
     positive INTEGERS. k = 1 is the Bonami–Karoui endpoint psi_n(1):
     the same quantity as the comb amplitude of node 3.1.2.
     ("Everything is the endpoint.")

## 2. Hypotheses and the Weil-class structure

(H1) int f dx = 0  — imposed (zero-integral packet).
(H2) f(0) = 0 — REQUIRED for int f d*x to converge; the Weil admissible
     class (digest item 3.1: int g dx = 0 AND int g d*x = 0) forces it.
FORK (registered, bus goal 003 / F0): if the concrete g_04 construction
     satisfies (H2), the -f(0)/(2 sqrt(lambda)) term in (I3) vanishes.
     If NOT: the term is an EXPLICIT elementary function u^{1/2} on the
     window whose Mellin is closed-form,
       int_{1/lambda}^{lambda} u^{1/2 - i gamma} d*u
         = (lambda^{1/2-i gamma} - lambda^{-1/2+i gamma}) / (1/2 - i gamma),
     to be carried through the tau-block ("poles inside") — repair path
     named REPAIR_H2_POLE_CANCEL; it is not an error term, it must cancel
     against the archimedean/pole structure or the packet must be
     re-projected with the d*x-condition. This fork is decided by ONE
     evaluation g_04(0).

## 3. Exterior decay at integer samples (lambda^2 in Z kills the leader)

For even psi, two integrations by parts of (I1) at x = k (integer):
  mu_n psi_n(k) = 2 psi_n(1) sin(ck)/(ck)
                 + (2/(ck)^2) [ psi_n'(1) cos(ck) - psi_n'(0) ] + R_3(k).
With c = 2*pi*lambda^2 and lambda^2 in Z:  sin(ck) = 0 EXACTLY;
psi_n'(0) = 0 (even); prolate ODE at the endpoint gives
psi_n'(1) = (chi_n - c^2) psi_n(1) / 2  (chi_n ~ (2n+1)c << c^2), hence

  (D)   psi_n(k) ~ - lambda * psi_n(1) / k^2   for  2 <= k << c,

sign-constant (no alternation), amplitude lambda * endpoint / k^2.
FLAGGED IMPORT: the rigorous two-sided version of (D) needs the
Bonami–Karoui exterior/Liouville estimates (Constr. Approx. 43 (2016);
arXiv:1405.3676; plus arXiv:2603.07407 pre-plunge) — verbatim check
required before the paper (digest Stage-4 list).
Consistency check (done): the 1/x oscillatory far-field carries
out-of-interval L^2 mass psi(1)^2/(pi c) ~ (1 - lambda_n) — matches the
concentration defect exactly. The extension used is the INTEGRAL
extension (I1), not the singular-ODE continuation.

## 4. Lemma LeftEdgeLeakage (3.1.4a)

Under (H1) + (H2), with (D):
  |E(g_04)(1/lambda)|
    = lambda^{3/2} | sum_n c_n mu_n [ psi_n(1) + sum_{k>=2} psi_n(k) ] |
    <= C * lambda^{3/2} * (1/lambda) * lambda * max_n |psi_n(1)|
    =  C * lambda^{3/2} * sqrt(c * E-class)   ~   C' * lambda^{5/2} E^{1/2}.
Boundary term B_L(gamma) = E(g)(1/lambda) * lambda^{i gamma} / (i gamma):
zero-sum over gamma > Gamma with unconditional RvM density:
  2 sum_{gamma > Gamma} |B_L|^2  <=  C'' * lambda^5 E * log(Gamma)/Gamma
                                  ~   C'' * lambda^3 (log lambda) E.
SUBDOMINANT to the comb classes (lambda^9..11 E). G3a-grade.
NOTE the phase book: mu_n = i^n |mu_n| makes the left-edge combination
sum_n (-1)^{n/2} c_n psi_n(1) — a DIFFERENT signed combination than the
right-edge g(lambda) = sum_n c_n psi_n(1); order-of-magnitude predictions
carry a x/5 sign-cancellation caveat (registered in bus 003 / F2).

## 5. Parked: 3.1.4b InteriorSmoothRemainder

AC part K^smooth = (1/(i gamma)) int E(f)'_ac(u) u^{-i gamma} du.
Route: same integer-sampling machinery on the derivative packet +
E-zeta intertwining; expected class <= comb class. One more pen session.
Until closed, the 3.1 assembly line carries K = K^comb + B_L + K^smooth
by triangle inequality with K^smooth as the single remaining open budget.

## 6. Numerical falsifiers -> bus goal 003 (constants for (13,120))

F0: g_04(0) — decides the (H2) fork.
    REGISTERED: |g_04(0)| / ||g_04||_{window-scale} <= 1e-8 (0.5) OR
    O(1) => REPAIR_H2_POLE_CANCEL path activated (0.5).
F1: psi_n(k), n in {0,2,4}, k = 1..8, via (I1) integral at c = 26*pi
    (mpmath quad, dps 40). REGISTERED: |psi_n(k)| * k^2 / (lambda *
    |psi_n(1)|) in [0.5, 1.5] for k = 2,3,4; constant sign (no
    alternation). NULL: ratios scaling like 1/k (not 1/k^2) kills the
    sin-vanishing mechanism.
F2: direct vs Poisson left edge: E(g_04)(1/lambda) computed directly
    (13 evaluations of g) vs lambda^{1/2} sum_{k<=8} ghat(2*pi*k*lambda).
    REGISTERED: relative agreement <= 1e-3; magnitude
    |E(g)(1/lambda)| / ||E(g)|| in [1.7e-29, 4.2e-28]
    (center 0.645 * lambda * k_edge = 8.4e-29; x/5 for the i^n
    sign-book caveat of Section 4).

## 7. Attack surface for Прошка (self-declared)

(a) The (H2) fork and the d*x-condition on the CONCRETE g_04 build.
(b) Validity of Poisson with midpoint convention for the truncated
    (jump-at-endpoint) packet — BV justification line.
(c) The IBP remainder R_3(k) uniformity for k up to ~c (WKB window).
(d) The i^n phase book in mu_n (FT convention consistency with the
    project's Mellin convention).
