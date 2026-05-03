# Q3 PSD-pd Step 14 Worst-vector Autopsy (2026-05-03)

Status: in progress / reconnaissance

Placement:

- This continues the finite numerical pilot for the fallback `PSD-pd`
  certificate route.
- It does not claim RH.
- It diagnoses the near-kernel detected in Step 13.

Script:

```text
scripts/q3_psdpd_step14_worst_vector.py
```

## Parameters

```text
L=3.0
ell=0.35
delta=0.25
k_spline=5
arch_tmax=260
arch_nt=48001
p0_na=24001
top=12
```

## Near-kernel

The generalized eigenproblem is

```math
C^\circ x=\lambda G^\circ x,
\qquad
C^\circ=N^\ast(A-P)N.
```

Baseline output:

```text
lambda_min(Cc,Gc) = 1.0106683708616412e-08
v^T G v            = 1.0000000000000000e+00
||Qv||_2           = 7.0216669371534024e-16
Qv                 = [-6.661338e-16, -2.220446e-16]
```

The boundary-null lift is numerically clean.

## Energy decomposition

For the lifted vector `v`, normalized by `v^T G v=1`:

```text
E_A      =  3.7635347242996264e-01
E_P      =  3.7635346232327871e-01
E_P0     = -2.2961126388225173e-02
E_Pnu    =  3.9931458871150383e-01
E_R      =  3.9931459881818770e-01
E_C      =  1.0106684035842653e-08
A-P      check = 1.0106683934196781e-08
R-Pnu    check = 1.0106683878685629e-08
split residual = 1.572e-16
```

Ratios:

```text
E_P / E_A   = 9.9999997314576672e-01
E_Pnu / E_R = 9.9999997468992141e-01
(-E_P0)     = 2.2961126388225173e-02
```

Interpretation:

- this is a true cancellation direction, not a random numerical failure;
- `A` and `P` are both about `0.376`, but their difference is about `1e-8`;
- the Green block `-P0` contributes positively, but the fluctuation `Pnu`
  nearly saturates the base energy on this vector.

## Coefficient profile

Largest lifted coefficients:

| rank | `u_j` | `v_j` |
| ---: | ---: | ---: |
| 1 | `-2.4000000000e+00` | ` 4.7514316242966903e-01` |
| 2 | ` 2.3500000000e+00` | `-4.7514316196392398e-01` |
| 3 | `-2.6500000000e+00` | `-2.9216694834588847e-01` |
| 4 | ` 2.6000000000e+00` | ` 2.9216694825264916e-01` |
| 5 | ` 1.3500000000e+00` | ` 2.4731547056925604e-01` |
| 6 | `-1.4000000000e+00` | `-2.4731547037833601e-01` |
| 7 | ` 1.6000000000e+00` | `-2.4314505936606437e-01` |
| 8 | `-1.6500000000e+00` | ` 2.4314505936088329e-01` |

The profile is strongly antisymmetric across the origin, with boundary-near
mass around `|u|≈2.35--2.65` and secondary packets around `|u|≈1.35--1.65`.

## Top prime-shift contributors

Top contributors to `P` on the worst vector:

| rank | energy | `a=r log p` | weight | `p` | `r_pow` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | ` 3.6698404156466835e-01` | `2.9444389792e+00` | `6.7550062924e-01` | 19 | 1 |
| 2 | `-3.2978622976449223e-01` | `3.9702919136e+00` | `5.4536153629e-01` | 53 | 1 |
| 3 | ` 3.2634671205497556e-01` | `3.7612001157e+00` | `5.7357764038e-01` | 43 | 1 |
| 4 | ` 3.1864804251973922e-01` | `3.7135720667e+00` | `5.7996251970e-01` | 41 | 1 |
| 5 | `-3.1578464903053116e-01` | `1.6094379124e+00` | `7.1976251555e-01` | 5 | 1 |
| 6 | ` 2.7224600074560779e-01` | `6.9314718056e-01` | `4.9012907173e-01` | 2 | 1 |
| 7 | `-2.6638028564759109e-01` | `3.4339872045e+00` | `6.1676230902e-01` | 31 | 1 |
| 8 | ` 2.5401655284014674e-01` | `4.2626798770e+00` | `5.0588702928e-01` | 71 | 1 |

The near-kernel is not driven only by the smallest shifts.  Several prime
shifts at distances `~3.4--4.3` dominate, matching large separations between
the antisymmetric packets.

## Kappa split

Use the identity

```math
C=A-P=(A-\kappa P_0)-(P-\kappa P_0).
```

Output:

| `kappa` | min eig `R_k` | max eig `(S_k,R_k)` | pass |
| ---: | ---: | ---: | :--- |
| 0.5 | `-1.7444505429718795e+00` | indefinite | false |
| 1.0 | `-1.2860683102394381e+00` | indefinite | false |
| 1.5 | `-8.8909463815863843e-01` | indefinite | false |
| 2.0 | `-6.9970496139819116e-01` | indefinite | false |
| 3.0 | `-4.4710653247230459e-01` | indefinite | false |
| 4.0 | `-2.7376179225702102e-01` | indefinite | false |
| 6.0 | `-4.0089855199570257e-02` | indefinite | false |
| 8.0 | ` 1.2101132090230482e-01` | `9.9999998199983842e-01` | true |
| 10.0 | ` 2.4144504135148093e-01` | `9.9999998347768304e-01` | true |

This is the main new signal:

```math
\boxed{
\kappa\text{-split revives the relative certificate at }\kappa\approx8.
}
```

But the certificate is still knife-edge: the relative max is below `1` only by
about `1.8e-8` at `kappa=8`.

## Verdict

The Step 13 near-kernel is meaningful:

- it is boundary-null to numerical precision;
- it has exact `A/P` and `R/Pnu` near-saturation;
- it is shaped like an antisymmetric multi-packet mode;
- it is fed by several prime-shift bands, not just `log 2`;
- the original `R=A-P0` split fails, but a stronger `kappa` base can make the
  relative certificate formally pass on this finite level.

The next target is not another broad sweep.  It is a focused `kappa` and
profile-stability diagnostic:

```math
\boxed{
\kappa_{\min}(L,\ell,k,\Delta)
\quad\text{and worst-vector stability.}
}
```

## Next target

Step 15 should:

- binary-search the smallest `kappa` where `R_k` becomes positive;
- measure `max eig(S_k,R_k)-1` versus `kappa`;
- compare worst-vector profiles across nearby `(k_spline,ell,delta)`;
- add optional CSV/NPZ export for the worst vector and matrix diagnostics.
