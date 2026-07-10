# 003 — LeakageFalsifier_v1

/goal LeakageFalsifier_v1 for Route B / Route Z E5. CHEAP compute
(a handful of 1D quadratures + ~30 packet evaluations). NOT_RH.
No Phase 2. No QW/packet changes. ACTIONS LOG mandatory.
Answer file: bus/003_leakage_falsifier.answer.md (handoff format).
Reference pen note: docs/PEN_3_1_4_SMOOTH_REMAINDER_v1.md (READ-ONLY).

Point (13,120): lambda = sqrt(13), c = 2*pi*13, prolate basis as in the
true-precision packet constructor (same normalization, ||psi||_{L2[-1,1]}=1).

F0 H2-FORK DECIDER: evaluate g_04(0) (the packet value at the origin,
  time side, BEFORE applying E). Report |g_04(0)| and the window-scale
  reference ||E(g_04)||.
  REGISTERED fork: |g_04(0)| <= 1e-8 * scale  => H2_HOLDS (0.5);
  else O(1)*scale => H2_FAILS -> code REPAIR_H2_POLE_CANCEL (0.5).

F1 INTEGER SAMPLES OF THE EXTENDED PROLATE: for n in {0, 2, 4} and
  k = 1..8 compute
    psi_n(k) = (1/mu_n) * int_{-1}^{1} psi_{n,c}(t) e^{i c k t} dt,
  mpmath quad, dps >= 40 (integrand oscillates ~ c*k/(2*pi) = 13k periods;
  use breakpoint splitting per Viazovska discipline if needed).
  Report the table psi_n(k) and mu_n (with phase i^n).
  REGISTERED: |psi_n(k)| * k^2 / (lambda * |psi_n(1)|) in [0.5, 1.5]
  for k = 2, 3, 4 (all three n); constant sign in k (no alternation).
  NULL control: if the ratios scale like 1/k instead of 1/k^2, code
  SIN_VANISHING_REFUTED (kills the lambda^2-integrality mechanism).

F2 LEFT-EDGE CROSS-CHECK (two independent computations of one number):
  (a) direct: E(g_04)(1/lambda) = lambda^{-1/2} * sum_{m=1..13} g_04(m/lambda);
  (b) Poisson: lambda^{1/2} * sum_{k=1..8} ghat_04(2*pi*k*lambda)
      [ghat via (I2) of the pen note: lambda * sum_n c_n mu_n psi_n(k)]
      minus lambda^{-1/2} g_04(0)/2 if F0 gave H2_FAILS.
  REGISTERED: relative agreement |a - b|/|a| <= 1e-3;
  magnitude |E(g_04)(1/lambda)| / ||E(g_04)|| in [1.7e-29, 4.2e-28]
  (center 8.4e-29 = 0.645 * lambda * k_edge; wide band = i^n sign-book
  caveat, pen note Section 4).
  PLANTED violation (K1): recompute (b) with mu_n phases forced to +1
  (drop i^n) — the direct/Poisson agreement MUST break; report by how much.

Codes: H2_HOLDS / REPAIR_H2_POLE_CANCEL | INTEGER_SAMPLING_CONFIRMED /
  SIN_VANISHING_REFUTED | LEFT_EDGE_MATCH / LEFT_EDGE_MISMATCH.
FINAL STEP: one history line in ROUTE_B_STATE.md; write
bus/003_leakage_falsifier.answer.md; git add gate files; STOP.
Do not select next gate.
