# Edge ledger Probe 2 / Probe 3 / Probe 4 report

**INCOMPLETE SCHEDULE: run on partial ledger data (not all of m in [13, 23, 43, 83, 163] present); schedule-wide verdicts below are marked UNRESOLVED_INCOMPLETE_SCHEDULE rather than a real CONFIRMED/REFUTED/BOUNDED/GROWS.**

Generated: 2026-09-03 12:28:32 CEST
Precommit: `docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md` (frozen before any run; ADDENDUM adds Probe 4)

DIAGNOSTIC_NEVER_A_PROOF. No Lean. No route promotion. PX_RH_CLAIM: NOT_MADE.

## Probe 3 verdict (quoted rule)

- GROWS (confirmed): R_m(0.40) monotone increasing over the schedule and R_163(0.40)/R_13(0.40) >= 3.
- BOUNDED: max/min of R_m(0.40) over the schedule <= 1.5.
- GEOMETRY_FIRST: at fixed m the N-check changes R_m(0.40) by a factor >= 2.
- else UNRESOLVED.

**VERDICT: UNRESOLVED_INCOMPLETE_SCHEDULE**

Detail: `{"insufficient_precision_mn": [], "have_full_schedule": false, "geometry_first_hits": []}`

## Probe 2 verdict (quoted rule)

- CONFIRMED: c_m > 0 for every m in the schedule and max c_m / min c_m <= 3.
- REFUTED: sign of c_m changes across the schedule, or max/min >= 100.
- else UNRESOLVED.

AMENDMENT 2 (2026-09-03 12:25): HF_FD_MISMATCH is a Probe-2-only per-cell flag (recorded below; no longer a stop for Probes 3/4, and no longer this probe's own verdict label). The sign/stability rule above is amended: a consistently NEGATIVE c_m across the whole usable schedule -- observed at the checkpoint cells, where dlambda1/dL is positive at every cell so c_m = -(dlambda1/dL)/edge_sq < 0 everywhere -- is itself REFUTED for P_FUCHS_IDENTITY_NUMERICALLY_HOLDS on this (fixed-primes, kernel-parameter-L) variation; it does not test the domain-only variation of the continuous form Q_W^a (open question for the judge, Q9-1).

**VERDICT: REFUTED**

Detail: `{"dps_used": 240, "schedule_c_m": {"13": -1.824237039925201e+20, "23": -1.4499564780057173e+34, "43": -1.520342850329087e+64}, "insufficient_precision_m": [], "hf_fd_mismatch_m": [13, 23, 43], "have_full_schedule": false, "ratio_max_over_min": 8.334129924208892e+43, "all_positive": false, "all_negative": true, "sign_changes": false}`

## Probe 4 verdict (quoted rule, ADDENDUM P_CURVATURE_SOURCE_1)

- CONFIRMED: kappa_m > 0 for every m and max kappa_m / min kappa_m <= 2 over the schedule.
- REFUTED: kappa_m grows monotonically with kappa_163/kappa_13 >= 10, or kappa_m < 0 for some m (a negative kappa contradicts the real-zero product and is a STOP: KAPPA_NEGATIVE).
- else UNRESOLVED. N-check pairs are descriptive.

**VERDICT: UNRESOLVED_INCOMPLETE_SCHEDULE**

Detail: `{"dps_used": 240, "schedule_kappa_m": {"13": 0.02589626740503931, "23": 0.026263016505022364, "43": 0.025843056802214937}, "insufficient_precision_m": [], "have_full_schedule": false, "ratio_max_over_min": 1.0162503881031377}`

## sigma-table (Probe 3), all records

| m | N | dps | sigma | numerator | denominator | ratio | grid_converged |
|---|---|-----|-------|-----------|-------------|-------|-----------------|
| 13 | 13 | 120 | 0.1 | 0.9203377698 | 0.9035577426 | 1.018571062 | True |
| 13 | 13 | 120 | 0.15 | 0.9289085649 | 0.9035577426 | 1.028056671 | True |
| 13 | 13 | 120 | 0.2 | 0.9376027794 | 0.9035577426 | 1.037678872 | True |
| 13 | 13 | 120 | 0.25 | 0.9464226443 | 0.9035577426 | 1.047440135 | True |
| 13 | 13 | 120 | 0.3 | 0.9553704375 | 0.9035577426 | 1.057342981 | True |
| 13 | 13 | 120 | 0.35 | 0.9644484847 | 0.9035577426 | 1.067389984 | True |
| 13 | 13 | 120 | 0.4 | 0.9736591609 | 0.9035577426 | 1.077583772 | True |
| 13 | 13 | 120 | 0.45 | 0.9830048912 | 0.9035577426 | 1.08792703 | True |
| 13 | 13 | 240 | 0.1 | 0.9203377698 | 0.9035577426 | 1.018571062 | True |
| 13 | 13 | 240 | 0.15 | 0.9289085649 | 0.9035577426 | 1.028056671 | True |
| 13 | 13 | 240 | 0.2 | 0.9376027794 | 0.9035577426 | 1.037678872 | True |
| 13 | 13 | 240 | 0.25 | 0.9464226443 | 0.9035577426 | 1.047440135 | True |
| 13 | 13 | 240 | 0.3 | 0.9553704375 | 0.9035577426 | 1.057342981 | True |
| 13 | 13 | 240 | 0.35 | 0.9644484847 | 0.9035577426 | 1.067389984 | True |
| 13 | 13 | 240 | 0.4 | 0.9736591609 | 0.9035577426 | 1.077583772 | True |
| 13 | 13 | 240 | 0.45 | 0.9830048912 | 0.9035577426 | 1.08792703 | True |
| 23 | 23 | 120 | 0.1 | 0.9233662021 | 0.906420563 | 1.018695118 | True |
| 23 | 23 | 120 | 0.15 | 0.9320229914 | 0.906420563 | 1.028245639 | True |
| 23 | 23 | 120 | 0.2 | 0.9408054027 | 0.906420563 | 1.037934753 | True |
| 23 | 23 | 120 | 0.25 | 0.9497157269 | 0.906420563 | 1.047764984 | True |
| 23 | 23 | 120 | 0.3 | 0.9587563033 | 0.906420563 | 1.057738916 | True |
| 23 | 23 | 120 | 0.35 | 0.9679295211 | 0.906420563 | 1.067859182 | True |
| 23 | 23 | 120 | 0.4 | 0.9772378204 | 0.906420563 | 1.078128476 | True |
| 23 | 23 | 120 | 0.45 | 0.9866836935 | 0.906420563 | 1.088549547 | True |
| 23 | 23 | 240 | 0.1 | 0.9233662021 | 0.906420563 | 1.018695118 | True |
| 23 | 23 | 240 | 0.15 | 0.9320229914 | 0.906420563 | 1.028245639 | True |
| 23 | 23 | 240 | 0.2 | 0.9408054027 | 0.906420563 | 1.037934753 | True |
| 23 | 23 | 240 | 0.25 | 0.9497157269 | 0.906420563 | 1.047764984 | True |
| 23 | 23 | 240 | 0.3 | 0.9587563033 | 0.906420563 | 1.057738916 | True |
| 23 | 23 | 240 | 0.35 | 0.9679295211 | 0.906420563 | 1.067859182 | True |
| 23 | 23 | 240 | 0.4 | 0.9772378204 | 0.906420563 | 1.078128476 | True |
| 23 | 23 | 240 | 0.45 | 0.9866836935 | 0.906420563 | 1.088549547 | True |
| 43 | 43 | 120 | 0.1 | 0.9195957037 | 0.9028519977 | 1.01854535 | True |
| 43 | 43 | 120 | 0.15 | 0.9281478268 | 0.9028519977 | 1.028017692 | True |
| 43 | 43 | 120 | 0.2 | 0.936823021 | 0.9028519977 | 1.037626348 | True |
| 43 | 43 | 120 | 0.25 | 0.9456235115 | 0.9028519977 | 1.047373782 | True |
| 43 | 43 | 120 | 0.3 | 0.9545515704 | 0.9028519977 | 1.057262511 | True |
| 43 | 43 | 120 | 0.35 | 0.9636095176 | 0.9028519977 | 1.067295105 | True |
| 43 | 43 | 120 | 0.4 | 0.9727997221 | 0.9028519977 | 1.077474187 | True |
| 43 | 43 | 120 | 0.45 | 0.9821246033 | 0.9028519977 | 1.087802437 | True |
| 43 | 43 | 240 | 0.1 | 0.9195957037 | 0.9028519977 | 1.01854535 | True |
| 43 | 43 | 240 | 0.15 | 0.9281478268 | 0.9028519977 | 1.028017692 | True |
| 43 | 43 | 240 | 0.2 | 0.936823021 | 0.9028519977 | 1.037626348 | True |
| 43 | 43 | 240 | 0.25 | 0.9456235115 | 0.9028519977 | 1.047373782 | True |
| 43 | 43 | 240 | 0.3 | 0.9545515704 | 0.9028519977 | 1.057262511 | True |
| 43 | 43 | 240 | 0.35 | 0.9636095176 | 0.9028519977 | 1.067295105 | True |
| 43 | 43 | 240 | 0.4 | 0.9727997221 | 0.9028519977 | 1.077474187 | True |
| 43 | 43 | 240 | 0.45 | 0.9821246033 | 0.9028519977 | 1.087802437 | True |

## Probe 2 per-record

| m | N | dps | c_m (HF) | c2_m (HF) | sign dGap/dL (HF) | HF/FD mismatch |
|---|---|-----|----------|-----------|-------------------|-----------------|
| 13 | 13 | 120 | -1.82423704e+20 | -1.403762986e+16 | -1 | True |
| 13 | 13 | 240 | -1.82423704e+20 | -1.403762986e+16 | -1 | True |
| 23 | 23 | 120 | -1.449956478e+34 | -2.194788136e+29 | -1 | True |
| 23 | 23 | 240 | -1.449956478e+34 | -2.194788136e+29 | -1 | True |
| 43 | 43 | 120 | -1.52034285e+64 | -4.409194592e+58 | -1 | True |
| 43 | 43 | 240 | -1.52034285e+64 | -4.409194592e+58 | -1 | True |

## Probe 4 (kappa) per-record

| m | N | dps | bracket | bracket*12 | kappa | kappa_forced_lower | kappa/0.0231 |
|---|---|-----|---------|------------|-------|---------------------|--------------|
| 13 | 13 | 120 | 0.004441463438 | 0.05329756126 | 0.02589626741 | 0.01233859868 | 1.121050537 |
| 13 | 13 | 240 | 0.004441463438 | 0.05329756126 | 0.02589626741 | 0.01233859868 | 1.121050537 |
| 23 | 23 | 120 | 0.002734886715 | 0.03281864059 | 0.02626301651 | 0.01059543792 | 1.136927121 |
| 23 | 23 | 240 | -0.002734886715 | -0.03281864059 | 0.02626301651 | 0.01059543792 | 1.136927121 |
| 43 | 43 | 120 | 0.001700882603 | 0.02041059124 | 0.0258430568 | 0.008237297759 | 1.118747048 |
| 43 | 43 | 240 | 0.001700882603 | 0.02041059124 | 0.0258430568 | 0.008237297759 | 1.118747048 |
