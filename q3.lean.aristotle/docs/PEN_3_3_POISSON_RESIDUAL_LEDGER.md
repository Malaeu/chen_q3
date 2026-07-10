# PEN 3.3 — Exact Poisson residual ledger at lambda^2 = 13

STATUS: `MIDPOINT_POLE_LEDGER_REPAIR / NOT_RH`.

This note records the request-local result of
`PoissonResidualChannelAudit_v1`.  It does not change the packet, `QW`, the
Fourier convention, Phase 2, or the Q3 Lean mainline.

## 1. Source lock

The decisive local sources are:

- `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:112-167`, which defines the starred
  endpoint convention and states that the old direct diagnostic used full
  endpoint weight;
- `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:246-290`, which proves
  `h_lambda(0) < 0` and selects `H2-POLE/CORRECTION`;
- `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:360-379`, which records the endpoint
  and canonical starred left-edge values;
- `docs/PEN_3_1_4a_LEFT_EDGE_v3.md:10-31,33-48`, which locks the Fourier phase,
  starred Poisson identity, and H2 fork;
- `leakage_falsifier_v1.py:337-361` and `leakage_closeout_v1.py:151-179`, which
  define the old full-endpoint direct diagnostic and its finite Poisson sums;
- `poisson_residual_channel_audit_v1.py:136-197,235-265`, which performs the
  exact finite Legendre/Bessel reduction and signed-tail summation.

The primary-source preflight found structural background for the Poisson
operator in Connes--Consani, *The Scaling Hamiltonian* (arXiv:1910.14368), but
no external source was used to infer or fit a correction term.  Every nonzero
term below comes from the locked local identity.

## 2. Direct observable and midpoint convention

Put `M = lambda^2 = 13`, and let `h` be the locked two-mode packet.  Bus 006
used the full-endpoint diagnostic

```text
D_full = lambda^(-1/2) * sum_{m=1..M} h(m/lambda).
```

The canonical starred observable is instead

```text
D_star = lambda^(-1/2)
         * (sum_{m=1..M-1} h(m/lambda) + (1/2) h(lambda^-)).
```

Therefore the exact correction needed when the Bus 006 full-endpoint number is
retained as `D_direct` is

```text
C_mid = D_full - D_star
      = (1/2) lambda^(-1/2) h(lambda^-).
```

At the fixed cell:

```text
h(lambda^-) = -8.9446729900892226424357567094911359214e-30
D_full       = -1.6379228285530899819583299084969347241e-29
D_star       = -1.4023915259194169028411085554511312035e-29
C_mid        = -2.3553130263367307911722135304580352058e-30
```

This is not a fitted residual.  It is exactly the difference between full and
half endpoint weight.

## 3. Exact signed Poisson sequence

For even Legendre degree `ell`, the locked phase gives

```text
integral_{-1}^1 P_ell(x) cos(C*k*x) dx
  = 2 * (-1)^(ell/2) * j_ell(C*k),

C = 2*pi*lambda^2 = 26*pi.
```

Since `C*k` is an integer multiple of `2*pi`, `sin(C*k)=0` and
`cos(C*k)=1` exactly.  The spherical-Bessel recurrence therefore reduces the
combined canonical contribution to the finite inverse-power identity

```text
p_k = sum_{r=1..90} A_(2r) / k^(2r).
```

No asymptotic fit or brute-force extrapolation is used.  The leading term and
the uniform remainder guard for `k >= 40` are

```text
A_2                                      = 5.4590805652940673241490843188875e-29
sum_{r>1} |A_(2r)| / 40^(2r-2)           = 7.8324263257883890216812329052429e-30
A_2 > scaled remainder                   = true
```

Thus `p_k > 0` for every `k >= 40` in the fixed finite model, and its decay is
certified as `k^-2` with explicitly bounded higher inverse powers.

For `K=40`, zeta summation of the finite inverse-power polynomial gives

```text
P_40 = -1.5312841846390214802879049825692321041e-29
T_40 = +1.2889265871960457744679642711806058544e-30
```

An independently bounded, lower-order evaluation is

```text
T_40 through k^-8       = 1.2889264318072060336150217273025028720e-30
omitted absolute bound  = 1.5706907050164817066286204917600675756e-37
certified interval      =
  [1.2889262747381355319668510644404536960e-30,
   1.2889265888762765352631923901645520480e-30].
```

The signed tail is therefore certified, but it is `SIGNED_TAIL_INSUFFICIENT`
for the old full-endpoint `D_direct`: it closes the canonical starred identity
with the H2 term, while the exact `C_mid` is still required for the Bus 006
full-endpoint target.

## 4. Channel ledger

The H2 value is nonzero:

```text
h_lambda(0) = -1.5310318562555484463256665821922872937e-60.
```

For this left-edge Poisson observable the exact correction is

```text
C_pole = -(1/2) lambda^(-1/2) h_lambda(0)
       = +4.0315160529297652469520199869532881486e-61.
```

No cancellation is assumed; the term is displayed in the ledger.  The channel
statuses are:

| Channel | Status | Value / reason |
| --- | --- | --- |
| `P_40` | `PRESENT_EXACT` | finite canonical signed Poisson prefix |
| `T_40` | `PRESENT_EXACT` | finite inverse-power/zeta certificate |
| `C_pole` | `PRESENT_EXACT` | exact H2 correction above |
| `C_mid` | `PRESENT_EXACT` | exact full-to-starred endpoint correction |
| `C_left` | `ABSENT_FROM_CURRENT_IDENTITY` | the left edge is the target observable, not an added channel |
| `C_right` | `ABSENT_FROM_CURRENT_IDENTITY` | no independent right-edge term occurs in the derived starred identity |
| `R_other` | `ZERO_EXACT` | the finite inverse-power polynomial and its exact zeta tail exhaust the fixed-model sequence |

In particular, the Bus 006 label `SECOND_EDGE_CHANNEL` was a diagnostic
placeholder caused by an incomplete ledger; no second-edge formula is present
or needed.

## 5. Whole-ledger closure

For the Bus 006 full-endpoint target,

```text
D_ledger = P_40 + T_40 + C_pole + C_mid + C_left + C_right + R_other
         = -1.6379228285530899819583299084969347241e-29.
```

The high-precision fixed-model relative closure error is

```text
2.2179588642445167111e-89.
```

Propagating the lower-order signed-tail interval gives the conservative worst
relative closure error

```text
1.9076473249873470275e-8 < 2e-3.
```

The independent period-split quadrature check for mode 0 at `k=18` has
relative error `1.0225618512815655e-58`; the closure satisfies the registered
instrument-floor guard.

## 6. Planted failures

All registered plants fire:

| Plant | Relative closure error | Result |
| --- | ---: | --- |
| Poisson-side `c4 -> -c4` | `1.7124150341882018` | fires |
| endpoint weight `1/2 -> 0` | `0.20185048554525588` | fires |
| endpoint weight `1/2 -> 1` | `0.14379877887271220` | fires |
| delete largest correction `C_mid` | `0.14379877887271220` | fires |

## 7. Verdict and weakest implication

Primary verdict: `MIDPOINT_POLE_LEDGER_REPAIR`.

Weakest justified implication: at the fixed cell, the direct/Poisson mismatch
reported by Bus 006 is fully explained by the locked midpoint convention plus
the explicit H2 correction and a certified signed tail.  This removes the
local need for an independent second-edge channel.  It is not an RH result, a
Phase 2 result, or a proof of any downstream positivity gate.

No next gate is selected here.
