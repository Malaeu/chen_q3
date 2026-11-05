# Part B judge preflight (no scientific run)

This preflight built J3-head, the OEIS reference check for J4, and the literal
J5 control before any 10^8 Mertens sweep. The source-locked literal J5 plant
has a nonzero constant offset, so its required exponent is inconsistent with
the formula. The centered companion below diagnoses the intended 0.3 power;
it does not replace J5 or alter its score. Per the task's judge gate, no full
Part B run has been started.

## J3 head and head-error interface

For the Limit 9 coefficients,

```text
m1(N-1) = sum_{d<N} mu(d)/d
c_n = -mu(n), 2 <= n < N
c_N = N*m1(N-1)
H_N(k) = sum_{n=2}^N c_n*(k mod n)/n.
```

The preflight checked every `1 <= k < N` at `N = 2, 3, 5, 10, 20, 50, 100,
200, 500`. The largest float64 `|H_N(k)-1|` was `5.33e-15`, below the `1e-12`
judge tolerance.

The exact floor-form residual, useful to Part A's J2 comparison, is

```text
R_N^h(k) = 1 - k - sum_{2 <= n < N} mu(n)*floor(k/n)
           + N*m1(N-1)*floor(k/N).
```

It is zero for `k<N`. `head_residual_k` and
`head_error_partial_interval` in `part_b_judge_preflight.py` expose this form.
The latter returns a lower partial sum plus the explicit source-L14 tail bound
`9 N^2/(K+1)`; it does not label a finite truncation as the full error. That
bound is too loose at `N=10^5` for a feasible direct cutoff, so the full
`E_N^h` computation still needs a sharper exact-tail method.

## J4 source values

The published sequence is [OEIS A084237](https://oeis.org/A084237), with
`a(j)=M(10^j)`. The small sieve/indexing preflight matches `M(10)=-1`,
`M(100)=1`, and `M(1000)=2`. The full checks through `10^8` remain pending the
scientific run.

## Exact B1 counterexample

The B1 preregistration says `max_{N<=10^8} sqrt(N)*|gamma(N)| <= 0.6`.
Already `M(1)=1` and `M(2)=0`, so the exact sum gives

```text
gamma(2) = 1/2,       sqrt(2)*|gamma(2)| = sqrt(2)/2 > 0.6.
gamma(3) = 1/2,       sqrt(3)*|gamma(3)| = sqrt(3)/2 > 0.6.
```

Thus B1 is a `MISS` by an exact small-N witness; this makes no claim about the
actual maximum over the full range. The overall Part B disposition remains
`INCONCLUSIVE` because J5's structural mismatch voids the scientific run.
B2 is `NOT_RUN` because the required `E_N^h` grid was not computed. B3 splits:
the literal plant has visible `N^0.5` growth (`HIT` for growth), but it misses
the registered approximately `0.3` slope; the registered J5 validation is
therefore `INCONCLUSIVE`. The centered companion's `0.3` envelope is diagnostic
only.

## J5 literal plant and centered companion

The literal change in `gamma(N)` is

```text
delta_gamma(N) = 0.01 * sum_{k<N} k^0.8*cos(14 log k)/[k(k+1)].
```

Its infinite series converges absolutely. Separating `k=1` and expanding
`1/(1+1/k)` for `k>=2` gives

```text
C/0.01 = 1/2 + Re sum_{j>=0} (-1)^j*(zeta(1.2+j-14i)-1)
         = 0.1096036273049255821169210092495875878046...
```

After 64 terms, the unscaled series remainder is at most
`zeta(65.2)-1 = 2.35963202997e-20`. Thus the planted `gamma(N)` tends to the
nonzero constant `C = 0.001096036273049255821169210092495875878046...`. The
literal `sqrt(N)*gamma(N)` therefore has exponent `1/2`, not `0.3`; the
original J5 judge is a `FAIL`.

On 201 log-spaced points from `10^6` to `10^8`, the plant-only literal
root-statistic regression slope is `0.4997859247`. Representative prefix
values are:

| N | planted `gamma(N)` | `sqrt(N)*gamma(N)` |
|---:|---:|---:|
| 10^6 | 0.001051825789018143 | 1.0518257890 |
| 10^7 | 0.001081038607693033 | 3.4185442389 |
| 10^8 | 0.001100728887042734 | 11.0072888704 |

For diagnosis only, subtract the limit: `gamma_centered(N)=gamma_plant(N)-C`.
Its infinite tail is evaluated using the Euler trapezoid formula and a
geometric expansion of the integral. For
`f(x)=x^0.8/[x(x+1)]*exp(14 i log x)`,

```text
sum_{k>=N} f(k) = integral_N^infinity f(x) dx + f(N)/2 + R,
|R| <= 13.23 N^-2.2.
```

Expanding the integral through five terms adds at most
`N^(-5.2)/5.2` to that bound. The centered root-statistic's absolute-sample
regression slope is `0.3093413230`; its oscillatory amplitude envelope is
`0.01*N^0.3/sqrt(0.2^2+14^2)`, with slope exactly `0.3`. This is a companion
control only, not a J5 pass.

Artifacts:

- `part_b_judge_preflight.py` — reproducible J3/J4/J5 preflight and head-error
  helpers; run with `uv run --with mpmath python .../part_b_judge_preflight.py`.
- `part_b_judge_preflight.json` — judge results and scope.
- `part_b_preflight_run.log` — exact `uv run` command and persisted outcome.
- `part_b_j5_centered.csv` and `part_b_j5_preflight.svg` — 201-point literal
  and centered plant diagnostics with per-point tail error bounds.
- `part_b_j5_plot_metadata.json` — plot scale, series, colors, and fitted slopes.
