# OffAxisGrowthProbe — D0.7e.2 completed tracker

Status: `COMPLETE_DIAGNOSTIC_ONLY / NOT_RH`.
Verdict: `OFF_AXIS_PROBE_NONDECISIVE_FALSIFIER_PASS`.

The computation is IEEE-754 float64/complex128 only. The normalized
tracker is evaluated with both the `lambda^(-iz)` phase and
`gammaC(1/2+iz)` completion. The constant `bDet` cancels in `R`.
This means only that the registered sampled raw-growth falsifier did not fire;
it does not prove that the soft route is alive, locally normal, or identified
with Xi.

| m | N | R(0.1) | R(0.2) | R(0.3) | R(0.4) |
|---:|---:|---:|---:|---:|---:|
| 13 | 90 | `0.965754581876` | `0.949398132721` | `0.953179048664` | `1.1416419088` |
| 13 | 120 | `0.965754581876` | `0.949398132721` | `0.953179048664` | `1.1416419088` |
| 14 | 120 | `0.965802368067` | `0.949581703784` | `0.953629332004` | `1.14467532844` |
| 53 | 120 | `0.96625512258` | `0.951329417538` | `0.957945174897` | `1.17316992128` |
| 101 | 120 | `0.966331719911` | `0.951626373249` | `0.958684042175` | `1.17794516726` |

OLS slope `d log R(0.3;m) / d L_m = 0.00291661813153` 
(standard error `0.0003355`, R2 `0.9742164`).
The fit uses one `N=120` cell per distinct m; `(13,90)` is the
N-stability duplicate and is not double-weighted.

The window is `[gamma_1,gamma_11]` from the persisted zero cache,
exactly ten empirical mean spacings. New cells `(53,120)` and
`(101,120)` use the same g04 -> E-star breakpoint -> Fourier
pipeline in float64; fixed N=120 is diagnostic, not an N(lambda)
selector. Their prime/prime-power support through m is recorded
for provenance but is not consumed by the D0.7e.2 tracker itself.

The statistic is completion-class dependent. Multiplying the object by the
zero-free gauge `lambda^(-i*c*z)` multiplies `R(y;m)` by `lambda^(c*y)` and
shifts the fitted slope versus `L_m=log(m)` by `c*y/2`, without changing any
zero. At `y=0.3`, one extra lambda phase moves the slope to
`0.1529166181315253`, whereas the inverse phase moves it to
`-0.14708338186847467`.

The next theorem-facing family is normalized once at the center:

```text
F_j(z)=Xi(0)/Ghat_j(0)*Ghat_j(z),  Ghat_j(0)!=0,
```

so that `F_j(0)=Xi(0)!=0`. Per-compact and strip-sup normalizations are
forbidden. The current D0 `G=Fhat/bDet` already has the central anchor on
`BDetNonzero`.

`D0.7e.5a` remains BLOCKED/ACTIVE; mint inactive; no Bus 010.
