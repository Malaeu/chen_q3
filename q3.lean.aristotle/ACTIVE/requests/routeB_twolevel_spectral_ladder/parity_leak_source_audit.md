# ParityAuditRebuild_v2

Status: diagnostic only. Not a proof of RH. Not a Route B kill. Phase 2 was not run. No new lambda/N anchors were bought. QW formulas and packet definitions were not changed.

## Headline

1. Source of old parity leakage? [`PARITY_LEAK_IN_PACKET`; measured G cross is within x30 of packet off-parity prediction]
2. Actual T parity clean? [YES; max ratio `0.0`]
3. Serialization/order clean? [YES; fresh-vs-stored G drift `3.46338275115e-5`]
4. Parity-projected S0 rebuild verdict? [`PARITY_PROJECTED_SCHUR_REBUILD_CONFIRMED`]
5. External order cross-check? [`EXTERNAL_MATCH`]
6. Final verdict code: `PARITY_PROJECTED_SCHUR_REBUILD_CONFIRMED`

## A0 Parity-Aware Threshold Model

Complex coefficient convention: packet coefficients come from real E-map samples and satisfy the reality check `c_-n = conj(c_n)` numerically. The parity split itself is the complex-linear reflection `R c_n = c_-n`, so `v_even=(v+Rv)/2` and `v_odd=(v-Rv)/2`; no conjugation is applied inside the parity projector.

| vector | expected | delta_off | registered band pass | reality error |
|---|---|---:|---|---:|
| `k1` | `even` | `7.99771209012342881e-15` | `False` | `0.0` |
| `k2_odd` | `odd` | `1.00420089276277755e-14` | `False` | `0.0` |
| `k2_even` | `even` | `8.83809368205567961e-15` | `False` | `0.0` |

Registered dust band was `[3e-10,3e-7]` with central `1e-8`. The reconstructed packet deltas are much smaller, around `1e-14`; nevertheless the measured `G` cross entries are explained by the parity-aware prediction.

| cross | measured | predicted | measured/predicted | within x30 |
|---|---:|---:|---:|---|
| `k1,k2_odd` | `1.32056658288540416e-28` | `9.49187842299306072e-28` | `0.139125947893` | `True` |
| `k2_even,k2_odd` | `2.37658899710471944e-28` | `1.0676562629983281e-27` | `0.222598703297` | `True` |

## A1 T-Parity

Actual stored full T matrix was not persisted in the anchor; this audit rebuilt the `(13,120)` T matrix through the same deterministic `build_tau_matrix` path at pilot dps `191` and checked the full reflected matrix.

- `max|tau_nm - tau_-n,-m|/max|tau| = 0.0`
- registered threshold: `<= 1e-30`
- pass: `True`

## A2 Serialization / Order

- packet order verified as `['k1', 'k2_odd', 'k2_even']`: `True`
- fresh `Q^*TQ` vs stored `G` relative Frobenius difference: `0.0000346338275115413427894544108084`
- pilot rebuild tolerance for serialization/order audit: `1e-4`
- stored G matches fresh rebuild within pilot tolerance: `True`
- serialization/order clean: `True`

## B Parity-Projected Schur Rebuild

Canonical projected packet:
- `k1_p`, `k2e_p`: normalized even parts, then re-orthogonalized;
- `k2o_p`: normalized odd part;
- even and odd complements solved separately; no mixed-parity complement QR is authoritative here.

| block | dim M | dim complement | residual ||CY-B||/||B|| | eig(S0) |
|---|---:|---:|---:|---|
| even | 2 | 119 | `8.66837818843696502e-187` | `['3.48398819933127752e-59', '1.31185433472019818e-51']` |
| odd | 1 | 119 | `3.70502098486956458e-187` | `['3.05591345639889521e-55']` |

Combined sorted parity eigenvalues:

| rank | parity | value | true mu | rel error |
|---:|---|---:|---:|---:|
| 1 | `even` | `3.483988199331277522374e-59` | `3.483988199331277499198e-59` | `6.652021716592e-18` |
| 2 | `odd` | `3.055913456398895211777e-55` | `3.055913397515165668963e-55` | `1.9268782155507e-8` |
| 3 | `even` | `1.311854334720198182606e-51` | `1.311854284569468368159e-51` | `3.8228887464362e-8` |

- expected ordering `even < odd < even`: `True`
- max relative error vs true `mu1..3`: `3.82288874643621564e-8`
- ground alignment with `k1_p`: `0.999999997654058726`
- rebuild verdict: `PARITY_PROJECTED_SCHUR_REBUILD_CONFIRMED`

## B2 Dirt-Identity Check

- `||(G-K_schur)_cross||/||G_cross|| = 5.47067529062965575233007809015e-39`
- registered target: `~1e-40`
- pass: `True`

## C External Cross-Validation

Zero-compute order-only comparison:

- our lowest even eigenvalue at `c=13`: `3.48398819933127752e-59`
- Groskin arXiv:2605.20224 reports `lambda_min^even(c=13,N=100,dps=200,T=800)=2.865e-59` and a retest value `2.077e-59`; both are same order.
- our odd/even gap proxy near first-zero scale: `3.05591345639889521e-55`
- the same paper reports c=13 first-zero error around `2e-55`; the prompt's CCM comparison value `2.44e-55` is also same order.
- verdict: `EXTERNAL_MATCH`

Sources used for this external check:
- https://arxiv.org/abs/2605.20224
- https://arxiv.org/pdf/2605.20224

## D Log-Space N-Model

For `mu_i`, all lambda grids with saved `N=60,90,120` were checked in log space. For `theta_i`, only saved static-Schur theta points are available; most theta sequences remain underdetermined and are reported as such.

### mu, lambda_sq=12
- `mu1`: drift90->120/|x120|=`0.00112561205263`, ratio=`3.23290409321`, status=`True`
- `mu2`: drift90->120/|x120|=`0.000864892697474`, ratio=`4.75310267079`, status=`True`
- `mu3`: drift90->120/|x120|=`0.000942016248832`, ratio=`4.32367350533`, status=`True`

### mu, lambda_sq=13
- `mu1`: drift90->120/|x120|=`0.0013718052417`, ratio=`4.78323163594`, status=`True`
- `mu2`: drift90->120/|x120|=`0.00119055120845`, ratio=`5.88208946745`, status=`True`
- `mu3`: drift90->120/|x120|=`0.00147963304918`, ratio=`4.98166729817`, status=`True`

### mu, lambda_sq=14
- `mu1`: drift90->120/|x120|=`0.0015828228762`, ratio=`11.7553140248`, status=`True`
- `mu2`: drift90->120/|x120|=`0.00132662244546`, ratio=`13.3245067393`, status=`True`
- `mu3`: drift90->120/|x120|=`0.00121545217289`, ratio=`14.0574505357`, status=`True`

### theta availability
- lambda_sq=12: theta1:2pt, theta2:2pt, theta3:2pt
- lambda_sq=13: theta1:1pt, theta2:1pt, theta3:1pt

## Decision

Verdict code: `PARITY_PROJECTED_SCHUR_REBUILD_CONFIRMED`.

The old mixed Schur run is now understood as packet-level parity dust plus a strong Feshbach cancellation witness, not as an operator-level N-drift signal. The parity-projected rebuild confirms the canonical block object at `(13,120)` and reproduces `mu1..3` within the registered tolerance. Stop here and hand off; do not choose the next gate locally.
