# SUPERSEDED REQUEST POINTER — DO NOT EXECUTE

Этот файл — исторический math spec старого диагностического pilot, а не
текущая задача. Не запускать его и не выводить из него current gate.

Текущий адрес:

- `ROUTE_B_EXECUTION_STATE.json`;
- `ROUTE_B_EXECUTION_CONTROL.md`;
- физический минимальный `bus/NNN_*.goal.md` без matching answer и без
  `STATUS: PAUSED_RESTORABLE`.

Текущий машинный статус:

```text
IDLE_AWAITING_EXPLICIT_PROSHKA_MATHEMATICAL_TARGET
RB-IDLE / RB-IDLE-CONTROL / NoSelectedMathematicalTarget
BUS_010: VOID
```

Если физического goal нет, оставаться в `RB-IDLE-CONTROL` до отдельного
решения Proshka, выбирающего ровно один из G2/G3/G5/G6. `RB-IDLE-CONTROL` —
не математический goal. Codex не создаёт Bus 010, не авторизует Goal 051
неявно и не возобновляет старый spec ниже.

Бывшая ветка D0.7e.5a закрыта терминально с исторической причиной
`D0_7E_WPRIME_CONSUMER_MISSING`. CCM-класс —
`SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY`, только conditional G3/H2b
evidence. Ниже сохранён архивный spec только для provenance.

---

# Route B — TwoLevelSpectralLadder Pilot v2 (historical merged spec)

## Status
NOT a proof of RH. Diagnostic FALSIFIER for the Connes-prolate Route B
branch, attacking ONLY G4 (true Weil gap). Not Step32. Not Step33. Not
Q3.Main. Do not mix with the PSD-pd/Q3 mainline.

Route B compression (context only):
  RH follows if W_lambda -> 0, where
  W_lambda = |b_lambda| * sqrt(lambda) * eta_lambda / Delta_lambda.
Known blocks: ZeroEscapeObstruction (detector), Davis-Kahan bridge,
E3 strip upgrade. Open walls: G3 (residual), G4 (gap). This node = G4.

## Registered predictions (fit targets, E := exp(-4*pi*lambda^2))
  mu_1  ~ lambda^9  * E
  mu_2  ~ lambda^13 * E  (primary: odd branch g26 sets level 2)
        ~ lambda^17 * E  (backup: next even branch sets it)
  Delta ~ same class as mu_2
  W     ~ lambda^{-3.5} (primary) or lambda^{-7.5} (backup)
Failure to see decay of W is a serious Route B warning, not RH-negative.

## Definitions policy
FIRST search the repo for existing implementations (QW_lambda, prolate,
E-map, k_lambda, b_lambda). If found — use them, report file paths.
If NOT found — do NOT stop, do NOT invent: implement from the MATH SPEC
below, which is self-contained. DEFINITIONS_NOT_FOUND is only for
objects absent from BOTH repo and spec.

## MATH SPEC (self-contained; source [S1] = arXiv:2511.22755)
Parameters: lambda in ladder below; L = 2*log(lambda); basis V_n,
n = -N..N (dim 2N+1); bandwidth c = 2*pi*lambda^2.

(1) Matrix T = QW_lambda^N, tau_{n,m} = W02 - WR - WP  [S1 Sec 4]:
  q_{n,m}(y) = [sin(2 pi m y/L) - sin(2 pi n y/L)] / (pi (n-m)), n!=m
             = 2 (1 - y/L) cos(2 pi n y/L),                      n=m
  W02(n,m) = 32 L sinh(L/4)^2 (L^2 - 16 pi^2 m n)
             / ((L^2 + 16 pi^2 m^2)(L^2 + 16 pi^2 n^2))
  WP(n,m)  = sum over prime powers 1 < k <= exp(L) of
             Lambda(k) k^{-1/2} q_{n,m}(log k)
  WR(n,m)  = (alpha_L(m)-alpha_L(n))/(n-m)  (n!=m);
             2 gamma_L(n) - 2 beta_L(n)     (n=m),
     alpha_L, beta_L, gamma_L, c(L), w(L) EXACTLY per [S1] Prop 4.2
     and eqs (4.11)-(4.14): 2F1, digamma psi, trigamma psi',
     Hurwitz-Lerch Phi at z = e^{-2L} (fast convergence).
  Structure checks (Lemma 5.1): tau real symmetric,
  tau_{n,m} = tau_{-n,-m}.

(2) Prolate eigenfunctions h_{n,lambda}, n in {0,2,4,6,8}: solve
  -d/dx[(lambda^2-x^2) d/dx] + (2 pi lambda x)^2 on [-lambda,lambda]
  by Legendre expansion in P_k(x/lambda) (Bouwkamp / Xiao-Rokhlin),
  parity blocks, mpmath eigensolve. L2-normalize. Validate n=0..4
  against scipy pro_ang1 at small bandwidth (c<=10) first.
  chi_n(lambda) = hat(h_{n,lambda})(0) / h_{n,lambda}(0)
  (concentration eigenvalue of the +1/-1 Fourier branch).

(3) Zero-integral combos (I_n := int h_{n,lambda} dx):
  g04  = c0 h0 + c4 h4,  c0 I0 + c4 I4 = 0
  g26  = c2 h2 + c6 h6,  c2 I2 + c6 I6 = 0
  g048perp: zero-integral element of span{h0,h4,h8}, L2-orthogonal
  to g04. Normalize all.

(4) E-map and packet: E(f)(u) = u^{1/2} sum_{m>=1} f(m u),
  u in [lambda^{-1}, lambda] (at most lambda/u terms).
  V-coefficients: <E(f),V_n> = L^{-1/2} *
      int_0^L E(f)(e^{x}/lambda) exp(-2 pi i n x/L) dx
  (adaptive quadrature; refine until coefficients stable).
  k1 = normalize(P_N E(g04));  k2_odd = normalize(P_N E(g26));
  k2_even = normalize(P_N E(g048perp)).
  Report RAW norms before normalizing; set b := ||E(g04)||_{L2(d*u)}.
  No fitted constants anywhere.

## MANDATORY CALIBRATION (run before ladder; K1 judge)
C1. lambda=1.5, N=20: compute tau_{0,0} and tau_{1,2} two independent
    ways: (a) closed forms; (b) brute-force numerical integral of the
    Weil functional applied to q. Relative agreement < 1e-8, else
    STOP: MATRIX_CONVENTION_MISMATCH.
C2. Parity: tau_{n,m} == tau_{-n,-m} to working precision.
C3. Planted violation: perturb one prime term by +1e-3; C1 MUST catch
    it; if it does not, the judge is broken — STOP.
C4. Precision: mpmath with dps = 120 + ceil(4*pi*lambda^2 / ln 10)
    (approx 197 at lambda^2=14, 251 at lambda^2=24; [S1] itself uses
    200 digits). Spot-check one (lambda,N): recompute mu1 at dps+80;
    require agreement to >= 30 significant digits, else
    PRECISION_UNSTABLE. Justification: mu1 emerges from cancellation
    of O(L)-size Arch vs Prime parts down to ~E; this is genuine
    scale, not a rewritable formula (documented Viazovska-rule
    exception). Fit X/E, not X, wherever possible.
Eigen-solve note: only the bottom of the spectrum is needed; if full
mp.eigsy is too slow at N=120, use shifted inverse iteration,
validated against a full solve at the smallest (lambda,N).

## Ladder
Phase 1: lambda in {sqrt(12), sqrt(13), sqrt(14)}, N in {60, 90, 120}.
Phase 2 (only if Phase 1 N-stable, drift 90->120 < 1%, runtime OK):
         add {sqrt(18), sqrt(24)} at N=120 (+150 spot check).
Log runtimes and dps per (lambda,N); tqdm progress bars; save
intermediate JSON per (lambda,N).

## Compute per (lambda, N)
  a1=<T k1,k1>; a2o; a2e; eta1=||(T-a1)k1||; eta2o; eta2e
  mu1, mu2, mu3; Delta = mu2 - mu1
  Eigenvector diagnostics: parity(xi_i) = sum_j xi_{i,j} xi_{i,-j}
    for i=1,2; overlaps |<xi1,k1>|, |<xi2,k2_odd>|, |<xi2,k2_even>|
  Packet M = span{k1,k2_odd,k2_even}: Gram-orthonormalize (report
    Gram condition number; if degenerate: NUMERICAL_CONDITIONING_INVALID)
  G_M (3x3), lambda1_G..lambda3_G; rho = ||P_Mperp T |_M||;
  nu = lambda_min(P_Mperp T P_Mperp)
  LB_2D_odd  = a2o - a1 - sqrt(eta1^2+eta2o^2)
  LB_2D_even = a2e - a1 - sqrt(eta1^2+eta2e^2)
  LB_3D      = lambda2_G - a1 - rho
  W_actual = b*sqrt(lambda)*eta1/Delta
  W_bound  = b*sqrt(lambda)*eta1/LB_3D
  Leakage cross-check: chi4(lambda); ratio eta1/(1-chi4)
If b unavailable from repo AND spec norm fails: report W without b
and flag NORMALIZATION_B_LAMBDA_MISSING (do not fit b).

## Fits (log-log vs lambda, N-stable values only; report slope+-stderr)
  mu1: expect 9 | mu2: 13 (odd active) else 17 | Delta: 13 or 17
  nu: report slope; check nu >= lambda3_G + margin
  eta1/(1-chi4): report slope (expect polynomial, NO extra exponential)
  W_actual: expect -3.5 or -7.5 | W_bound: same if LB_3D stable
  b: report slope (guard: b*sqrt(lambda) bounded away from 0)
  Also report mu1/E, mu2/E, Delta/E directly.

## Forbidden
No RH claims; no zero-side matching as evidence; no fitted constants;
no plots-only reporting; do not skip Delta, nu, or N-stabilization;
do not orthonormalize without Gram conditioning; numerical evidence
is never a theorem.

## Failure codes (first that fires)
DEFINITIONS_NOT_FOUND | MATRIX_CONVENTION_MISMATCH | PRECISION_UNSTABLE
N_LIMIT_NOT_STABLE | FIRST_LEVEL_EXPONENT_MISMATCH
ODD_BRANCH_NOT_ADMISSIBLE | SECOND_LEVEL_NOT_PROLATE
ROGUE_STATE_BELOW_LADDER (nu < lambda3_G)
TAIL_GAP_ASSUMPTION_FAILS | GAP_COLLAPSE_E2CLASS
ETA_VS_LEAKAGE_MISMATCH | NORMALIZATION_B_LAMBDA_MISSING
NUMERICAL_CONDITIONING_INVALID | W_NOT_DECAYING
Status flags (not failures): ODD_BRANCH_ACTIVE / ODD_BRANCH_INACTIVE

## Output -> ACTIVE/requests/routeB_twolevel_spectral_ladder/report.md
THREE HEADLINE LINES FIRST:
  1. Does k2_odd set mu2?  [YES/NO; parity(xi2); overlaps; slopes]
  2. Tail: nu >= lambda3_G + margin?  [YES/NO; margin value]
  3. W_actual decay slope: -3.5 / -7.5 / other?  [value +- stderr]
Then: files searched & definitions used; conventions; calibration log
(C1-C4 incl. planted-violation catch); N-stabilization table
(lambda=sqrt(14)); full ladder table; all fits; failure codes or PASS;
next exact theorem/gap suggestion.
