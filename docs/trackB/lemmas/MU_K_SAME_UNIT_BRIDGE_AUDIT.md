# Track B E5p Lemma Audit: `mu_K_same_unit_bridge`

Status: `E5P_BRIDGE_NORMALIZATION_GAP`.  Documentation/audit only: no Lean proof
files, no `Q3.Main` edit, no web proof evidence, and no E5p closure claim.

## Issue

GitHub issue #13 asks for the remaining bridge:

```text
For K in {2,3,3.5}, prove that the analytic E5p budget mu_K is in the same
G_K/Q_K/raw-edge units as the finite raw-edge certificate and satisfies

  mu_2   >= 0.45 + guards_2
  mu_3   >= 0.51 + guards_3
  mu_3.5 >= 0.75 + guards_3.5.
```

The finite side is already an interval certificate for supplied constants:

```text
mu * G_K - (P_edge,K - P0_edge,K) + tau * Q_K^T Q_K >= 0.
```

This file audits only the missing analytic source for `mu_K`.

## Commands Used

```bash
gh issue view 13 --json number,title,state,body,url,labels,author,updatedAt

rg -n -i \
  "inverse Dirichlet|Dirichlet expansion|mollifier|second moment|off-diagonal|Conrey|Ghosh|B_K|mu_K|mu budget|mu_budget|same-unit|Selberg extremal|Selberg|Vaaler|Beurling|Connes|adelic|class space|edge budget|Weil-side|raw-edge" \
  docs/trackB q3.lean.aristotle Q3 docs scripts trackB
```

No raw-edge PSD/eigenvalue search was run for this audit.

Additional local source requested by the user:

```text
/Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/sections/
/Users/emalam/Documents/GitHub/RH_2025_V3_October/cert/bridge/
```

Read files:

```text
Q3_paper/sections/scope_notation.tex
Q3_paper/sections/Main_closure.tex
Q3_paper/sections/Weil_linkage.tex
Q3_paper/sections/A3/main.tex
Q3_paper/sections/A3/arch_bounds.tex
Q3_paper/sections/A3/local_positivity.tex
Q3_paper/sections/A3/rayleigh_bridge.tex
Q3_paper/sections/A3/matrix_guard.tex
Q3_paper/sections/A3/locks.tex
Q3_paper/sections/A3/param_tables.tex
cert/bridge/K2_A3_floor.json
cert/bridge/K3_A3_floor.json
cert/bridge/K4_A3_floor.json
cert/bridge/K2_A3_lock.json
cert/bridge/K3_A3_lock.json
cert/bridge/K4_A3_lock.json
```

## Required Bridge Statement

Current target:

```text
mu_K >= mu_cert,K + transfer_guards_K
```

for the same raw-log packet object used by the finite certificate:

```text
mu_cert,2   = 0.45
mu_cert,3   = 0.51
mu_cert,3.5 = 0.75
```

and then:

```text
mu_K * G_K - E_edge,K + tau_K * Q_K^T Q_K >= 0
```

or the restricted `ker(Q_K)` equivalent.  The bridge must identify units:
raw-log coordinate, sign of `E_edge,K = P_edge,K - P0_edge,K`, packet basis,
`G_K` norm, boundary receiver, and transfer guards.

## Local Evidence By Route

| Route | Local source | Evidence found | Result |
| --- | --- | --- | --- |
| B: mollifier / atlas 028 | `docs/trackB/TRACKB_MOLLIFIER_S51_REVIVAL.md` | It records no Track B inverse Dirichlet expansion of the margin and no first/second moment formula for K-cell margins. | no usable `mu_K` source |
| A: Selberg extremals / atlas 009 | `docs/trackB/TRACKB_SELBERG_ROUTE_B_REPAIR.md`, `docs/trackB/b2_uncertainty_tax_preflight.md`, `docs/trackB/b2b_explicit_formula_route_gap.md` | Selberg gives a scalar hard-edge surplus `1/B_K` and a sharp tax, but not a PSD/cone-preserving operator bound in the Track B packet `G_K` norm. | no same-unit `mu_K` lower bound |
| C: Connes adelic/class-space | `q3.lean.aristotle/docs/insights/connes_zeta_spectral_triples_2026_01_29.md` | The note is architectural validation for a parallel Toeplitz/Weil route and explicitly says it is not directly wired into the Lean chain. It has no Track B K-cell constants. | not an E5p bridge source |
| D: Q3 2025 Toeplitz-A3 archive | `RH_2025_V3_October/Q3_paper/sections/A3/*`, `cert/bridge/K*_A3_lock.json` | Gives an analytic Toeplitz bridge for total Weil positivity: `lambda_min(T_M[P_A]-T_P) >= c_arch(K)/4`. It uses the same `xi=log n/(2*pi)` and `w_Q=2 Lambda(n)/sqrt(n)` normalization. | candidate source, but no Track B local edge ledger map |

## Q3 2025 Toeplitz-A3 Candidate

The old Q3 2025 paper already reserves the name `A3` for the Toeplitz bridge:

```text
T0 -> A1' -> A2 -> A3 -> RKHS -> T5
```

where `A3` means:

```text
lambda_min(T_M[P_A] - T_P)
  >= min P_A - C*omega_P_A(pi/M) - ||T_P||.
```

The notation in `scope_notation.tex` matches the global Q3 convention:

```text
xi_n = log n/(2*pi)
w_Q(n) = 2 Lambda(n)/sqrt(n)
Q(Phi) = int a_*(xi) Phi(xi) dxi - sum w_Q(n) Phi(xi_n)
```

The proof object, however, is not the Track B local raw-edge matrix.  It is a
total Toeplitz-minus-prime operator for a Fejer-times-heat window on `W_K`.
Track B needs the local domination object:

```text
E_edge,K = P_edge,K - P0_edge,K
mu_K * G_K - E_edge,K + tau_K * Q_K^T Q_K >= 0.
```

The candidate numerical margins from the proof-grade lock JSON are:

| K source | file | lock `c0` | `omega_condition_ok` | `barrier_ok` | comparison to active cert threshold |
| ---: | --- | ---: | --- | --- | --- |
| 2 | `K2_A3_lock.json` | `0.9028668493703329` | true | true | above `0.45` before transfer losses |
| 3 | `K3_A3_lock.json` | `0.9043681970359332` | true | true | above `0.51` before transfer losses |
| 4 | `K4_A3_lock.json` | `0.9050660039059131` | true | true | potential proxy for K=3.5; above `0.75` before transfer losses |

The raw `K*_A3_floor.json` files have much larger `c0` values near `5.37`, but
for K=3 and K=4 they report `M_min=0` and `omega_condition_ok=false`.  They are
therefore not the bridge-lock evidence to spend.  The conservative candidate
source is the `K*_A3_lock.json` row with `c0≈0.90`.

## Missing Ledger Map

The Q3 2025 candidate does not yet close E5p because it lacks four bridges:

| Missing bridge | Why it matters |
| --- | --- |
| window/edge scale | Q3 2025 works on frequency windows `W_K=[-K,K]`; Track B edge cells use raw-log intervals `[2K,4K]` with `xi=a/(2*pi)`. |
| operator object | Q3 2025 bounds total `T_M[P_A]-T_P`; Track B needs only `P_edge,K-P0_edge,K` in the packet backend. |
| vector space/norm | Q3 2025 uses Toeplitz trigonometric-polynomial/RKHS geometry; Track B certificate uses B-spline packet coefficients with `G_K` and `ker(Q_K)`. |
| budget extraction | No lemma states that the Toeplitz margin `c0` or `c0/4` may be allocated as `mu_K` for the Track B raw-edge defect after transfer guards. |

## Verdict

```text
E5P_BRIDGE_NORMALIZATION_GAP
```

Reason:

```text
Q3 2025 provides a plausible analytic reserve source through the Toeplitz-A3
lock, with conservative candidate margins about 0.90 for K=2,3,4.  But no
current artifact identifies that total Toeplitz/Weil margin with the Track B
local raw-edge budget in the B-spline G_K/Q_K packet normalization.
```

This is not `E5P_BRIDGE_THRESHOLD_FAIL`, because no same-unit analytic source
has been proved comparable to the thresholds after transfer guards.  It is not
`E5P_BRIDGE_PASS`, because the missing ledger map is exactly the proof.

## Exact Remaining Obligation

One of the following must be supplied before E5p can close:

```text
1. A theorem defining analytic mu_K in raw-log Track B units and proving
   mu_K >= (0.45, 0.51, 0.75) + transfer_guards_K for K = 2,3,3.5.

2. A ledger extraction theorem from Q3 2025 Toeplitz-A3:

   total Toeplitz margin on W_K
     -> Track B local raw-edge budget in B-spline G_K/Q_K units
     -> transfer guard table.

3. A replacement finite certificate with lower supplied thresholds that are
   paid by an existing analytic budget source.

4. A fatal same-unit inequality, if a future analytic source is found but
   gives mu_K < mu_cert,K + transfer_guards_K for some active K.
```

Until then, the finite interval PSD certificate remains conditional on supplied
`mu` values and E5p remains open.
