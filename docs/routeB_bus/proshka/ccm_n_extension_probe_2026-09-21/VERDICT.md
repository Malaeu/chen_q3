# STATUS: KILL_FORCING_N_EXTENSION_ANALOGY_AT_M2
```yaml
OPERATIVE_CLASS: KILL_ATTEMPT
KILL_SCOPE: ATTEMPT
KILL_TARGET: FORCING_STYLE_N_EXTENSION_OF_ANALYTIC_Q_SOURCE
KILL_EVIDENCE_KIND: DIAGNOSTIC_NUMERICS_STRICTLY_INCREASING_ETA
DATE: 2026-09-21
M: 2
N: [1, 2, 3]
VERIFIER: DIAGNOSTIC_MPMATH_DPS_40
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
LEAN_CHECKED: false
```

## Result

At fixed `m=2`, analytic 0/4 Ferrers packet (angular ODE at `c^2=m`, Mellin generator, no cache), `η=‖B^{-1}r‖` **rises** with Fourier `N`:

| `N` | dim | `a=q^*Kq` | `‖r‖` | `η=‖B^{-1}r‖` | `β(q)` | `Δ-2e` |
|---|---|---|---|---|---|---|
| 1 | 3 | 0.21694 | 0.34644 | **0.95234** | −0.0646 | −0.274 |
| 2 | 5 | 0.31067 | 0.49063 | **1.40011** | −0.1850 | −0.493 |
| 3 | 7 | 0.34580 | 0.55353 | **1.68676** | −0.2329 | −0.577 |

`β(q)<0` already at `N=1`. Rayleigh energy **increases** with `N`: the longer row is a worse trial for the ground state of `K`, not a stronger certificate.

Plant: `K=ccmWeilMatFinite(2,1)` matches the Proshka witness (`a_sym=0.725463`, `y^* (K-aI)y=-0.653264`, identity `yE+2√2 b = 0` to `10^{-41}`). The matrix object is the same.

## What this kills

The forcing-style claim «a larger truncation is a stronger condition in a poset of finite certificates» **on this analytic packet at `m=2`**. Dense `D_k = {error < 2^{-k}}` is not entered by raising `N`.

## What this does not kill

- `FiniteGroundTransformToCCMTrialLocallyUniform` at large `m` with the Lean `selectedFerrers` inhabitant.
- Condition C for a different constructor.
- Route B / RH.

`DIAGNOSTIC_NEVER_A_PROOF`. Next named CCM node remains the Ferrers identity to `c_n`, not a certificate poset.

Script: `probe_n_extension.py`. Numbers: `result.json`.
