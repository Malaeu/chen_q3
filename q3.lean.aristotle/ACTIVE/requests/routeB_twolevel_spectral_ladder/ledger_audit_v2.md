# Route B TwoLevelSpectralLadder LedgerAudit v2 Preflight

1. Saved eigenpairs and Feshbach block identity valid grid-wide? [UNKNOWN/BLOCKED: saved grid JSON has scalars but not xi_i/T/G/B/C/m/y]
2. Ledger N-stable? [NO/SCALAR_ONLY: max saved mu drift N90->N120 = 2.0757277251360681996837131141285103325331835984605300344938037681100789848363765E-1]
3. xi1 aligned with k1 and even? [YES/SCALAR_GRID: min |<xi1,k1>|=9.999999580008574E-1, min parity(xi1)=9.999999999999998E-1]
4. Static S0 grid-wide confirmed? [NO - ANCHOR_ONLY; no new C inverse computed here]
5. Verdict code: `LEDGER_AUDIT_BLOCKED`

Status: diagnostic preflight only. Not a proof of RH. Not a Route B kill.
This report does not replace `StaticSchurEffectivePacketAudit`; it records why the cheap saved-data preflight cannot certify grid-wide J0-L2 from the currently persisted artifacts.

## Data Availability

The saved `lambda_sq_*_N_*.json` grid contains scalar diagnostics (`mu_i`, `lambda_G`, overlaps, parity, eta), but not the eigenvectors or matrices needed for matvec ledger checks.

Missing objects:

- `grid-wide saved eigenvectors xi1,xi2,xi3 for lambda_sq={12,13,14}, N={60,90,120}`
- `saved matrices or matvec cache sufficient to compute T xi_i without rerunning eigensolve/full matrix path`
- `saved packet projections m_i=P_M xi_i and y_i=xi_i-m_i for grid-wide L1/L2 identity ledger`
- `stored tau entries or saved T entries for J0 closed-form entry verification`

Available vector-rich artifacts: `full_low_eig_lambda_sq_14_N_120.json, rogue_tail_lambda_sq_14_N_120.json, rogue_tail_lambda_sq_14_N_90.json`.
Only `full_low_eig_lambda_sq_14_N_120.json` has eigenvector-style audit data, and even that is report data/top coefficients, not a reusable grid-wide saved eigenpair cache.

## J0 Saved Data Judge

- `tau` entry verification against saved matrix entry: `BLOCKED_NO_SAVED_T_ENTRY`.
- eigen-residual `||T xi_i - mu_i xi_i||`: `BLOCKED_NO_SAVED_XI_GRID_WIDE`.
- planted violation by corrupting one `xi` entry: `BLOCKED_NO_SAVED_XI_GRID_WIDE`.

## L1-L2 Block Ledger

`B^* y_i = (mu_i I - G)m_i` and the energy ledger require saved `xi_i`, `m_i`, `y_i`, or enough cached matvec data. Those objects are not present grid-wide. No new eigensolve or LU was run in this preflight.

## L3 Alignment / Handoff Scalars

| lambda_sq | N | |<xi1,k1>| | |<xi1,k2_odd>| | |<xi1,k2_even>| | parity(xi1) | parity(xi2) |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | 60 | `0.9999999977871581` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `1.0` | `-1.0` |
| 12 | 90 | `0.9999999947629036` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `0.9999999999999999` | `-0.9999999999999998` |
| 12 | 120 | `0.9999999958194159` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `1.0` | `-1.0000000000000004` |
| 13 | 60 | `0.9999999997928805` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `1.0` | `-1.0` |
| 13 | 90 | `0.9999999967938608` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `1.0` | `-1.0` |
| 13 | 120 | `0.9999999976540588` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `0.9999999999999999` | `-1.0` |
| 14 | 60 | `0.9999999580008574` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `0.9999999999999999` | `-0.9999999999999998` |
| 14 | 90 | `0.9999999979507344` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `0.9999999999999998` | `-1.0` |
| 14 | 120 | `0.9999999980715731` | `not_saved_grid_scalar` | `not_saved_grid_scalar` | `1.0` | `-1.0000000000000002` |

Note: `xi1_k2_odd` and `xi1_k2_even` are not stored in the regular grid JSON; full values exist only in the Feshbach/full-low key audit for `14,120`.

## L4 N-Stability Scalar Tables

| lambda_sq | drift mu1 | drift mu2 | drift mu3 | drift eta1 | drift |<xi1,k1>| | drift parity(xi1) |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | `1.2900531515922219734197021311061671014955508091119751546904550505524977579358550E-1` | `9.3683869122441615018664383021589205983330038194968542206573082668143896004033138E-2` | `9.4511993687825853566705745250462410976281565055870415855773752088245415640125388E-2` | `3.5007217875227059702766123083281283745713655958582687801437115852173134160456563E-1` | `1.0565123044168385412993949780234439847446593498641654379584671896987043936260874E-9` | `1E-16` |
| 13 | `1.6860556276686476127516953064878857110720166697024595911304451735272102062959020E-1` | `1.3881338973705078174320190246661402415670450002954146358339475408349745266560019E-1` | `1.5916042908410565838495465504454995740560912878425753315795970698649207548671937E-1` | `3.1845752125343291911623530704822090990885696121931432861453639252208712697840178E-1` | `8.6019800201797393309164819016574086521524632423209322016462584742486655805890836E-10` | `1E-16` |
| 14 | `2.0757277251360681996837131141285103325331835984605300344938037681100789848363765E-1` | `1.6689944399527350775030189010533801426582454886420937453246801945747929516017007E-1` | `1.4512791468040696429731519924842797391947775886886304540372418807669542602812556E-1` | `4.4608564713504037076044429876409002125712994570798773050941509935615561286651207E-1` | `1.2083870023302860009040862088368641650400265675092268094994589776399322279273438E-10` | `2E-16` |

Scalar verdict: saved `mu_i` drift is large (about 9% to 21% from `N=90` to `N=120`), while `xi1` alignment/parity scalars are stable. This is `NO/SCALAR_ONLY` for ledger N-stability, not a full block-ledger verdict.

## L5 Static-vs-Dynamic Conditional Bridge

Static Schur evidence remains anchor-only. No new `C^{-1}` was computed in this gate.

| lambda_sq | N | source | max rel err theta(S0) vs mu |
|---:|---:|---|---:|
| 12 | 60 | `static_schur_progress` | `1.85085883584117871245128532417631253821377526569096846190977338821220973462270234211135128E-8` |
| 12 | 90 | `static_schur_progress` | `3.36375364254436835246144939414461875382951968271821819971724767360393340131955518847533981E-8` |
| 14 | 120 | `FeshbachGate` | `2.7829597914348580034377361994040392356119546652559590454462478146954549738952952E-8` |

Static S0 grid-wide stability remains unproved until another static/deflated anchor exists, e.g. `lambda_sq=13,N=120`.

## L6 Future Deflated Static Solve Plan

Plan only, not executed here: one future `SingleAnchorDeflatedStaticSchur` at `lambda_sq=13,N=120`, with persisted `G`, `K_schur=B^*C^{-1}B`, `S0`, eig(S0), residuals, and low-mode contribution diagnostics. This is the correct next mathematical purchase if the cheap preflight is accepted.

## Verdict

- Verdict code: `LEDGER_AUDIT_BLOCKED`
- Secondary scalar flag: `LEDGER_N_UNSTABLE_SCALAR_ONLY`
- Handoff status: `XI1_HANDOFF_SCALARS_OK`
- Static status: `STATIC_SCHUR_ANCHOR_ONLY`

## Files

- JSON: `out/ledger_audit_v2_preflight.json`
- This audit did not run Phase 2, full ladder, LU, eigensolve, fitted-law proof, or any proof-mainline edit.
