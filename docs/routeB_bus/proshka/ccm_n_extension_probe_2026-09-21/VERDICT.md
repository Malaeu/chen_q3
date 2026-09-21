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

## 2026-09-21 addendum — m>2 defects, N=13 is not noise

Two script bugs at m>2, found by the observer and re-checked from disk:

1. Seeded `findroot` in `even_chi` collapsed the 0/4 pair at c²=13 to the same root 48.6737 (log: `probe_m13.log`, ZeroDivisionError). Replaced by the ordered even tridiagonal Legendre eigenproblem. At m=2 the patched packet reproduces `result.json` to the stored 12 digits (chi, plant, a, η, λ₀, gap, excess).
2. Hardcoded DPS=40 printed a FALLS token on N=26 where λ₀ came out negative (−1.09e−40 vs MAC even-block 4.947e−45). `measures` now refuses when |λ₀| or the gap is under 10^(−dps+5).

The first m=13 dps-40 table is **not** discarded at N=13. Independent reruns:

| source | dps | N | a | λ₀ | gap |
|---|---|---|---|---|---|
| analytic full block | 40 | 13 | 0.154560525732 | 7.92103597312e−31 | 6.40881979904e−28 |
| analytic full block | 240 | 13 | 0.154560525732 | 7.92103597375e−31 | 6.40881979904e−28 |
| MAC even block cache | 240 | 13 | 4.226e−16 | 7.921e−31 | — |

e = a to the printed digits because λ₀ ~ 10⁻³¹, not because λ₀ = 0 in working precision. Same K, different Rayleigh: analytic ~ 0.15, cache ~ 4e−16. Token FALLS at N=13 is a real non-coercive trial, not FiniteGroundTransform evidence. N=26 at dps 40 remains refused.

G4 `c_n` (`D0KTrialStage3.lean:81`) is `inner V_n_m kTrial_m_N` in `hTrial_m`; it does not import the JSON cache. Identity node stays clean iff the inhabitant is `prolateCombination`.

`DIAGNOSTIC_NEVER_A_PROOF`. Discriminator below: analytic Rayleigh at m=13 N=90.

## 2026-09-21 addendum — IF_B: analytic source stays O(0.1) at N=90

`n90_decider.py` (dps 80, one thread) was killed after ~50 min with SIGTERM 143, still on `building K`. Parallel rebuild (dps 40, 20 workers, 16471 upper-triangle entries) finished K in 179 s.

| q at m=13 N=90, full block dps 40 | a = q*Kq | ‖r‖ |
|---|---|---|
| cache row (`portable_k_coeffs_lambda_sq_13_N_90.json`) | −5.480e−41 (floor; MAC even-block a = 5.533e−59) | 1.8368725e−30 |
| analytic 0/4 Ferrers → Mellin, J=16 | **0.0842498998528** | 0.34271707 |
| MAC even-block cache (dps 240) | 5.533e−59 | 1.837e−30 |

Cache ‖r‖ matches the MAC audit to four digits: the matrix and the cache row are the same objects. Analytic Rayleigh is O(0.1), same order as m=2 and as m=13 N=13 (a=0.15456). It does not fall to 10⁻⁵⁹.

Ferrers truncation is not the gap. At m=13 N=13, `j_convergence.py` froze a=0.154560525732 from J=12 through J=32; coefficient tail a_J/a_0 dropped from 8.5e−9 to 2e−71.

Verdict token: coercivity at this cell is a property of the pinned cache row, not of the analytic Ferrers–Mellin source. G4 remains a true identity for that analytic object; it does not supply positivity. DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM not made.
