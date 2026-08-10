# 004 — SplitIdentityCheck_v1

/goal SplitIdentityCheck_v1 for Route B / Route Z E5. CHEAP compute
(a few high-precision evaluations). NOT_RH. No Phase 2. No QW/packet
changes. ACTIONS LOG mandatory.
Answer file: bus/004_split_identity_check.answer.md (handoff format).
Reference: docs/PEN_3_1_3_LG_INCOHERENCE_v2.md Section 0 (half-open split).

Purpose (one line): the adversarial pass (A3) demanded a deciding
numerical check that the half-open split K = K^comb + B_L + K^smooth
has no double counting at the window edge u = lambda^{-1}, where at
integer lambda^2 the m = M tooth coincides with the edge.

Point (13,120), anchored portable K (sha-pinned coefficients), mp dps>=50.

S1 SPLIT IDENTITY at four points gamma in {gamma_1, gamma_62, gamma_500,
  (gamma_62+gamma_63)/2}:
  (a) K(gamma) — the full anchored transform (as in AnchorLocked);
  (b) K^comb(gamma) = g04(lambda)*lambda^{1/2-i*gamma}/(i*gamma) *
      sum_{m=1..12} m^{-1/2+i*gamma}   [NOTE: m <= M-1 = 12, half-open];
  (c) B_L(gamma) = E(g04)(lambda^{-1}+) * lambda^{i*gamma}/(i*gamma),
      with E(g04)(lambda^{-1}+) computed directly (sum m=1..13 of
      g04(m/lambda), lambda^{-1/2} prefactor);
  (d) K^smooth(gamma) = K - K^comb - B_L (residual, reported).
  REGISTERED: |K^smooth(gamma)| <= 0.5 * |K^comb(gamma)| at gamma_500
  and at the midpoint (the AC part is subdominant in the far zone);
  report all four residuals with signs/phases.
S2 PLANTED double count (K1): recompute with the m = M = 13 tooth ALSO
  included in K^comb (i.e. sum m=1..13) while keeping the full B_L.
  REGISTERED: the identity residual at gamma_500 must JUMP by exactly
  the tooth magnitude |g04(lambda)*13^{-1/2}/gamma| within 5%;
  judge must fire with code K_SPLIT_EDGE_ACCOUNTING_GAP on the planted
  branch and stay silent on the half-open branch.
S3 REPORT-ONLY: mean_{j<=62} |D_12(gamma_j)|^2 with D_12 = sum_{m<=12}
  m^{-1/2+i*gamma} (near-crossover mean; BFM error not controlled here,
  no registered band — curiosity output for the S-branch bracket 0.24-0.29).

Codes: SPLIT_IDENTITY_PASS / K_SPLIT_EDGE_ACCOUNTING_GAP /
  SMOOTH_NOT_SUBDOMINANT (if S1 registered bound fails).
FINAL STEP: one history line in ROUTE_B_STATE.md; write
bus/004_split_identity_check.answer.md; git add gate files; STOP.
Do not select next gate.
