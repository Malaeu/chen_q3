# 002 — TailReturnProbe_v1

/goal TailReturnProbe_v1 for Route B / Route Z E5. MEDIUM compute
(~1h dominated by zeros 2001..5000). NOT_RH. No Phase 2. No QW/packet
changes. Q3 mainline untouched. ACTIONS LOG mandatory.
Answer file: bus/002_tail_return_probe.answer.md (handoff format).

Purpose (one line): close the TroughBoundary fork — does the tail profile
return to the ledger envelope past the trough [1419, 2515], and does the
mass exponent settle to p~1 in the marathon regime (gamma > ~4940)?

H0 HYGIENE (before compute):
  - git add: bus/ (protocol, 001 goal+answer), comb_meanvalue_falsifier_v1.py,
    out/comb_meanvalue_falsifier_v1.json.
  - Create archive_duplicates/ and MOVE (not delete) the Finder duplicates
    "handoff_to_proshka 2.md" and "handoff_to_proshka 3.md" there.
  - Quote VERBATIM in the answer the "READ-ONLY IMPORTS" section of
    ROUTE_B_STATE.md including sha256 lines (reviewer verification).

T1 ZEROS EXTENSION: extend the high-precision zero cache to j=5000 with
  the SAME loader/dps discipline as anchor_locked (no float roundtrip);
  write out/anchor_locked_zeros_first_5000.json + sha256 in ACTIONS LOG.
  Print progress every 500. Do NOT recompute j<=2000 (load cache, verify
  sha 60dba843b9dca732b232d1bf4f3a133b174ca403fd9929d99d49122a38303356).

T2 TAIL PROFILE on anchored portable K at (13,120) (coefficient file
  sha-pinned as in AnchorLocked; ceiling judge S_J/a1 <= 1.05 ON; zoned
  realness judge ON):
  - S_J/a1 at J = 2500, 3000, 4000, 5000.
  - Per-window DeltaS/a1 and window C_eff via
    C_eff^2 = DeltaS * a1 * pi / (f(g_lo) - f(g_hi)),
    f(g) = (ln(g/2pi)+1)/g, for windows
    W5=[g_2000,g_2500], W6=[g_2500,g_3000], W7=[g_3000,g_4000],
    W8=[g_4000,g_5000].
  - Adjacent p_mass (root-finding as in extraction gate) for W6/W7, W7/W8.
  - Ledger C refit over J in [500,5000].

REGISTERED (before run):
  R1 trough exit: C_eff(W8) in [6e-29, 1.1e-28]  (weight 0.6);
     FORK: if all W5..W8 C_eff < 4e-29 => TROUGH_EXTENDED — structural
     finding feeding SmoothRemainderTail (weight 0.25).
  R2 S_5000/a1 in [0.90, 0.96], strictly rising at every checkpoint.
  R3 ledger C refit within +-15% of 7.9e-29.
  R4 p_mass(W7/W8) in [0.7, 1.5] (marathon regime past gamma ~ 4940).
  Ceiling never fires (any S_J/a1 > 1.05 => CHANNEL_OBJECT_MISMATCH, STOP).

Codes: TAIL_RETURN_CONFIRMED / TROUGH_EXTENDED / AMBIGUOUS
  (+ LEDGER_CONSISTENT/INCONSISTENT, MASS_P_*).
FINAL STEP: one history line in ROUTE_B_STATE.md; write
bus/002_tail_return_probe.answer.md; git add this gate's files; STOP.
Do not select next gate.
