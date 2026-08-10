# 001 — CombMeanValueFalsifier_v1

/goal CombMeanValueFalsifier_v1 for Route B / Route Z E5. Near-zero compute
(13-term sums at known zeros). NOT_RH. No Phase 2. No QW/packet changes.
ACTIONS LOG mandatory (files+sha256, script+args, datasets+sha256, git status).
Answer file: bus/001_comb_meanvalue_falsifier.answer.md (MYTHOS_PROSHKA_HANDOFF format).

Context (one line): pen note PEN_3_1_3 predicts prime-repulsion suppression
of the truncated-zeta comb at zero ordinates; this gate falsifies/confirms
the discrete mean value on our own certified zeros.

F1 MEAN OVER ZEROS:
  D(gamma) = sum_{m<=13} m^(-1/2 + i*gamma).
  Zeros: high-precision cache out/anchor_locked_zeros_first_2000.json
  (sha256 must be quoted in ACTIONS LOG; do NOT recompute zeros).
  Report mean_{j<=J} |D(gamma_j)|^2 for J = 500, 1000, 2000 (float64 is
  enough: values are O(1), no cancellation below 1e-3 — Viazovska rule).
  REGISTERED:
    J=2000: in [1.55, 2.15]; prediction 1.853 = H_13 - A_13*(T/pi)/N(T)
            with H_13 = 3.18013, A_13 = 3.31466, T = gamma_2000 = 2515.29.
    J=500:  in [1.10, 1.90]; prediction 1.468 (T = 811.18).
  NULL control: the no-repulsion value 3.18 must be EXCLUDED at J=2000.
  PLANTED violation (K1): shadow run with zeros shifted by +0.25 each ->
  mean must move toward 3.18 (report shadow value; judge must see it).

F2 MIDPOINTS (direction only):
  Same mean over midpoints (gamma_j + gamma_{j+1})/2, j <= 500.
  REGISTERED (direction, no numeric band): midpoint mean >= zero mean;
  report the ratio midpoint/zero.

Codes: COMB_MEANVALUE_CONFIRMED / COMB_MEANVALUE_REFUTED / AMBIGUOUS.
FINAL STEP: append one history line to ROUTE_B_STATE.md; write
bus/001_comb_meanvalue_falsifier.answer.md; STOP. Do not select next gate.
