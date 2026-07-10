# MYTHOS_PROSHKA_HANDOFF: SplitIdentityCheck_v1

STATUS: STOP.
SCOPE: NOT_RH; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.

## Verdict

Code: `SMOOTH_NOT_SUBDOMINANT + K_SPLIT_EDGE_ACCOUNTING_GAP`.

The half-open edge bookkeeping test is useful but not enough: the planted
double-count branch fires exactly, so the edge-tooth judge is alive. However,
the registered far-zone smallness condition for the residual fails by a large
margin.

Interpretation: the half-open split removes the m=13 double count, but
`K^smooth` cannot be treated as subdominant to `K^comb` at this working point.
Node 3.1.4 is not optional bookkeeping; it is the live obstruction.

## Scoreboard

All split atoms were normalized to the same `pN_norm_g04` convention as the
full anchored coefficient cache.

| Test | Measured | Verdict |
| --- | ---: | --- |
| S1 at `gamma_500`: `|K_smooth| <= 0.5 |K_comb|` | ratio `2.57227201607` | MISS |
| S1 at midpoint `(gamma_62+gamma_63)/2` | ratio `2.03867370592` | MISS |
| S2 planted m=13 double count at `gamma_500` | jump rel error `0` | PASS, planted code fires |
| S3 report-only mean `j<=62 |D12|^2` | `0.698370441127` | reported |

## Four split points

| Point | `gamma` | `|K|` | `|K_comb|` | `|B_L|` | `|K_smooth|` | `|K_smooth|/|K_comb|` | phase/sign of `K_smooth` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `gamma_1` | `14.1347251417` | `9.62894947161e-33` | `6.75397351069e-31` | `2.46894570015e-30` | `2.21019215373e-30` | `3.27243236923` | phase `-2.55707202392`, signs `--` |
| `gamma_62` | `167.184439978` | `7.67947503080e-31` | `1.39330659418e-31` | `2.08738737086e-31` | `7.80486902263e-31` | `5.60168813902` | phase `-0.0298815346762`, signs `+-` |
| `gamma_500` | `811.184358847` | `6.75878226945e-32` | `2.82270242989e-32` | `4.30208848098e-32` | `7.26075847011e-32` | `2.57227201607` | phase `2.50914269533`, signs `-+` |
| midpoint | `168.139477697` | `2.60283910919e-31` | `1.97391920174e-31` | `2.07553094249e-31` | `4.02417717420e-31` | `2.03867370592` | phase `1.84395482347`, signs `-+` |

## Left-edge atom

Direct model recomputation:

- raw `E(g04)(lambda^-1+) = -1.63792282855e-29`
- normalized by `pN_norm_g04`: `-3.49057341077e-29`
- sanity rel diff vs `out/leakage_falsifier_v1.json`: `2.33335361599e-17`

This closes the "computed directly" requirement without relying on the old
left-edge JSON as the source of truth.

## ACTIONS LOG

Command:

- `/Users/emalam/GitHub/rh_lean_01_2026/venv_djo/bin/python split_identity_check_v1.py`

Artifacts:

- `bus/004_split_identity_check.goal.md`
  sha256 `7fdbdb6ee0a17ad56d1e84a8cc388b39ddface9c5ab3afdce4bc3bb156f8c3fc`
- `split_identity_check_v1.py`
  sha256 `24b883fceef7f1528fc2030d0f9876da916cc576c056910f77d74053bb77ca1c`
- `out/split_identity_check_v1.json`
  sha256 `1d8efd6ce740b6f958908e094c0a0355477e2af7c24e4e449393200947b08eaa`

Read-only inputs:

- `docs/PEN_3_1_3_LG_INCOHERENCE_v2.md`
- `out/portable_k_coeffs_lambda_sq_13_N_120.json`
  sha256 `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88`
- `out/anchor_locked_zeros_first_5000.json`
  sha256 `79cf9c8f678321ca75a35aa84bf7e7dbe6b277463bf0fbb89fb62b27382caf33`
- `out/leakage_falsifier_v1.json`
  sha256 `69fe0bf62bfab2172dd47cdffd6572acdd8fbd4a792a0237b5d1871097e4719e`

State:

- One history line added to `ROUTE_B_STATE.md`.
- `bus/005_tail_return_relabel.goal.md` and `bus/006_leakage_closeout.goal.md` remain queued and unexecuted.
- No next gate selected by SplitIdentityCheck_v1. STOP.
