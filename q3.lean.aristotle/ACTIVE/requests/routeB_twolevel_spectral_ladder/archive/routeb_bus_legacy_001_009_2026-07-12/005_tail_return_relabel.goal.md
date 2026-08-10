# 005 — TailReturnRelabel_v1

/goal TailReturnRelabel_v1. ZERO compute; state/labels only per reviewer
ruling on bus 002. NOT_RH. ACTIONS LOG mandatory.
Answer file: bus/005_tail_return_relabel.answer.md.

R1 RELABEL: 002 verdict AMBIGUOUS -> TAIL_RETURN_CONFIRMED +
   P_TRANSIENT_RECOVERY. Grounds (quote verbatim):
   - budget judges all PASS: C_eff(W8)=8.887e-29 in band; S_5000=0.9113
     rising; C_refit 8.771e-29 (11%); ceiling silent.
   - the p-judge measured the recovery ramp, not a law: predicted
     DeltaS(W7)/DeltaS(W8) from the measured C_eff ramp
     = 1.539 * (7.9185/8.8872)^2 = 1.222 vs measured 1.2235 (0.1%);
     p_mass sequence 0.117 -> 0.468 climbing toward 1 with envelope
     saturation. Point-estimator family: OLS 2.58 (dips bias up),
     trough-pair p (structure), ramp-pair p (bias down) — all retired
     as LAW judges; kept as PROFILE probes.
R2 REGISTER TailProfileArc (named): plateau [811,1419] ~0.8-1.05e-28;
   trough [1419,2515] ~2.7-3.0e-29; recovery ramp [2515,~4900];
   ledger level from ~4900 (= two-layer overtake gamma ~ 4940 inside W8).
   Interpretation line: destructive->node->single-layer asymptotics;
   measured target for pen node 3.1.4.2 (derivative-jump second layer).
R3 ENVELOPE NOTE: global upper envelope holds with thin margin:
   C_resid(5000)=1.0248e-28 <= C_env=1.05e-28 (2.4%); paper-facing
   constant to be quoted as <= 1.1e-28.
R4 FUTURE MARKER (report-only, not scheduled): if the tail is ever
   extended to J=6000+, REGISTERED: p_mass(W8/W9) in [0.7, 1.3].
FINAL STEP: STATE history line; answer file; git add; STOP.
Do not select next gate.
