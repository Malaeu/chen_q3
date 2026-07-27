# 004 — centered critical moment

Date: `2026-07-27`

Verdict:

```text
REPAIRABLE_LEAK
```

Success code `CENTERED_TRIAL_CRITICAL_MOMENT_RATIO_PROVED` is not issued.
Underlying open obligation: `CENTERED_S1_WEIGHTED_PROJECTION_GAP`.

## Exact source formula

For `i=(m,N)`, `L_m=log m`, and the normalized post-Galerkin coefficients
`c_{i,n}=CoefficientFamily.kTrial i n`,

```text
q_i(t)
  = L_m^(-1/2)
      * ∑_{n=-N}^{N} (-1)^n c_{i,n} exp(2π i n t / L_m).
```

Lean declaration:

```text
Q3.RouteB.D0Pstar.centeredTrialDensity
```

The chain actually present on disk is:

```text
E_star(hTrial_m)
→ gTrial_m
→ P_m_N(gTrial_m)=gTrial_m_N
→ sTrial_m_N * gTrial_m_N=kTrial_m_N
→ c_n=<V_n_m,kTrial_m_N>.
```

The only proved norm statement at the end of this chain is
`norm_kTrial_m_N = 1` in ordinary `H_m=L²(I_m,du/u)`.

## Exact missing inequality

On one fixed cofinal path `p(k)=(m_k,N_k)`, for every
`0 ≤ σ < 1/2`, the missing statement is

```text
∃ Cσ ≥ 0, ∀ k,
  ∫_{-L_mk/2}^{L_mk/2} ‖q_p(k)(t)‖ exp(σ|t|) dt
    ≤ Cσ ‖rawFplus p(k) 0‖.
```

It is materialized as:

```text
Q3.RouteB.D0Pstar.CenteredTrialCriticalMomentRatio
```

The full-weight `L²(exp(|t|))` projection estimate has been removed from the
active Lean contract. It is neither required nor proposed as a repair.

## Leakage dependence

The direct quantity is now materialized as

```text
centeredMomentLeakage(D,i,σ)
  = centeredCriticalMoment(D,i,σ) / ‖rawFplus(D,i,0)‖.
```

- `m` enters through `L_m=log m`, the interval endpoints, Fourier scale, and
  the maximal weight `exp(σ L_m/2)=m^(σ/2)`.
- `N` enters through the projected coefficient row and its endpoint leakage.
- `σ` enters only through `exp(σ|t|)`; a different finite `Cσ` is allowed for
  every fixed `σ<1/2`.

The required result is boundedness of this direct ratio on the one fixed
cofinal path. No uniformity as `σ ↑ 1/2` is claimed.

## Denominator behavior

Lean proves the exact identity

```text
rawFplus(D,i,0) = sqrt(log m) * D.kTrial(i,0).
```

Thus

```text
|Fplus_(m,N)(0)| = sqrt(log m) |c_(m,N),0|.
```

`CentralIndex` gives pointwise nonvanishing, but unit normalization of the
whole coefficient row gives no uniform positive lower bound for `|c0|`.

Existing binary64 diagnostics, not used as proof:

```text
sampled cells: (13,90), (13,120), (14,120), (53,120),
               (101,120), (149,120), (197,120), (257,120)
min |Fplus(0)| = 0.864797966349
max |Fplus(0)| = 0.878438550145
fit exponent in m = 0.00543083895502
verdict = SAMPLED_INF_GT_DELTA_NO_COMPENSATION_DIAGNOSTIC
```

The sample is stable and supports repairability, but it is not an anchor-floor
theorem.

## Plants

```text
constant mode:
  sin(zL/2)/(zL/2), removable value 1 at z=0;
  on z=-iσ its moment ratio grows exponentially in L.

endpoint-Dirichlet:
  endpointDirichletWeightedProjectionPlant = PASS;
  the same two-cell orthogonal projection contracts the ordinary square norm
  and strictly expands the endpoint-weighted square norm.
```

Therefore the forbidden inference

```text
unweighted L² contraction
⇒ uniform L²(exp(|t|)) contraction
```

is false and the full-weight branch is retired. This does not falsify the
guarded `L¹(exp(σ|t|))` target.

## Weakest repair

Add `CenteredTrialCriticalMomentRatio D p` itself as the explicit S1 source
input, or prove a direct bound for `centeredMomentLeakage D (p k) σ` for each
fixed `σ<1/2`. A separate analytic anchor-floor theorem would remove the
denominator risk. No full-weight `L²` estimate, `Set.univ`, float64 proof,
`bareTransform` family, RH input, or zero-side input is used.

## Outcome classification

```text
GREEN:
  not issued; no uniform cofinal bound is proved.

REPAIRABLE_LEAK:
  issued; finite-cell objects and the exact denominator identity are sound,
  the sampled denominator is stable, and the remaining obligation is the
  direct cofinal L1 leakage bound plus an analytic anchor floor.

FATAL_PATH:
  not issued; neither plant contradicts the weakened L1 target.
```

## Artifact and validation

```text
Q3/Proofs/RouteB/D0CenteredCriticalMoment.lean
0 sorry
0 admit
0 new axiom
lake env lean Q3/Proofs/RouteB/D0CenteredCriticalMoment.lean: exit 0
lake build Q3.Proofs.RouteB.D0CenteredCriticalMoment: exit 0
```

## Numerator measurements

Binary64/complex128; `N=120`; every integer `m=13,...,257`.
The complete 245-row `R` table is materialized in:

```text
CENTERED_MOMENT_RATIO_PROBE.md
CENTERED_MOMENT_RATIO_PROBE.csv
CENTERED_MOMENT_RATIO_PROBE.json
```

| m | R(0.10) | R(0.25) | R(0.40) | R(0.45) |
|---:|---:|---:|---:|---:|
| 13 | 1.0169705584 | 1.04326528221 | 1.0706111391 | 1.07996902819 |
| 53 | 1.01741647441 | 1.04442724529 | 1.07254975294 | 1.08218081711 |
| 257 | 1.01752781631 | 1.04471758393 | 1.07303451553 | 1.08273403228 |

Fit on all 245 rows:

```text
log R = intercept + beta log m
```

| σ | beta | SE(beta) | R² | R(257)/R(13) | min R | max R |
|---:|---:|---:|---:|---:|---:|---:|
| 0.10 | 0.00011958904057 | 3.39369398542e-06 | 0.836337103787 | 1.00054795874 | 1.0169705584 | 1.01752781631 |
| 0.25 | 0.000303712832102 | 8.61707249224e-06 | 0.836390481924 | 1.00139207327 | 1.04326528221 | 1.04471758393 |
| 0.40 | 0.000493678723399 | 1.40038204395e-05 | 0.836450013579 | 1.00226354494 | 1.0706111391 | 1.07303451553 |
| 0.45 | 0.000558329235082 | 1.58364879621e-05 | 0.836471190967 | 1.00256026239 | 1.07996902819 | 1.08273403228 |

`N` sensitivity at `m=53`; each cell is `R / (R at N=120)`:

| N | σ=0.10 | σ=0.25 | σ=0.40 | σ=0.45 |
|---:|---:|---:|---:|---:|
| 90 | 1.01741647449 / 1.00000000008 | 1.0444272454 / 1.00000000011 | 1.07254975309 / 1.00000000014 | 1.08218081728 / 1.00000000015 |
| 150 | 1.01741647443 / 1.00000000002 | 1.04442724533 / 1.00000000004 | 1.07254975301 / 1.00000000007 | 1.0821808172 / 1.00000000008 |

| binary64 check | value |
|---|---:|
| max relative delta, FFT 32768 vs 16384 | 1.07256235866e-08 |
| max coefficient norm error | 2.22044604925e-16 |
| direct midpoint check at `σ=0.45`, `m=13` | 7.94103006009e-10 relative |
| direct midpoint check at `σ=0.45`, `m=53` | 1.85589532567e-09 relative |
| direct midpoint check at `σ=0.45`, `m=257` | 3.60311407067e-09 relative |
