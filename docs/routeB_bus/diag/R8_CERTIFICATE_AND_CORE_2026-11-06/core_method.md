# Part 2 method and bounded result

This note covers only the crossing scan and the finite core. The pinned
definitions are from Round 8 source commit `70c4e6b0`, freeze `6d50c6f9`,
§§5–7 and the J3/J4 instructions. The run is diagnostic and does not establish
RH; `PX_RH_CLAIM` remains `NOT_MADE`.

## Definitions and evaluation

For each integer `N`, with `L=log(N)`, the taper is

```text
a_n = mu(n) (1 - log(n)/L),     1 <= n <= N
s_N = sum(a_n/n),               b_N = 1 + (sum(a_n)-s_N)/2
```

The sign computation uses the equivalent identity

```text
q_n = mu(n) (n-1)/n
2 L b_N = X_N = L (2 + sum(q_n)) - sum(q_n log(n)).
```

The Möbius values and von Mangoldt prime-power support were sieved through
`10,000,001`. Each `log(n)` and rational `q_n` was enclosed by MPFR at 192 bits;
the prefix additions, products and final sign interval used directed
`RNDD`/`RNDU` rounding. A sign was emitted only when the outward interval for
`X_N` excluded zero. Every interval for `N=3..10,000,001` excluded zero on the
first 192-bit pass; no high-precision replay or unresolved sign remained.
The endpoint `b_10,000,001` was included only to decide membership at
`N=10,000,000`.

The stored decimal `b_N` values are interval midpoints converted to the
platform C++ `long double`; head and plant values use compensated prefixes in
that same format. This Apple arm compiler has `LDBL_MANT_DIG=53`, so the extra
printed digits are formatting, not extra precision. These head and plant
numbers are diagnostics, not interval certificates.

For every `N=3..10,000,000`, the head is evaluated from

```text
A_N = sum(psi(k)^2/[k(k+1)])
B_N = sum(psi(k)/(k+1))
C_N = sum(k/(k+1))
x_N = L s_N
head_N = (A_N - 2 x_N B_N + x_N^2 C_N)/L^2.
```

`psi(k)` is the sum of `log(p)` over all prime powers `p^j<=k`. No prime powers
or head indices are truncated. `core_scan_*.csv.gz` retains every requested
row, while the endpoint sign is in `core_signs_*.csv.gz` and
`core_endpoint.csv`.

For a selected `N`, `K_N=ceil(N^(3/2))` was computed as the exact integer
ceiling of `sqrt(N^3)` using 128-bit integer arithmetic. Checks include
`K_3=6`, `K_10=32`, `K_200=2829`, and `K_10000=1,000,000`. The shoulder sums
every `N<k<K_N` and uses the full divisor expression

```text
R_N(k) = 1 + k s_N
         - sum_{n<=min(k,N)} mu(n)(1-log(n)/L) floor(k/n).
```

For each `k`, equal values of `floor(k/n)` are grouped with prefix sums in
native C++. No shoulder term is omitted. The preregistered 100-point rounded
log grid from 3 through 10,000 yields 92 distinct integer points after
deduplication. There are no sign crossings in `S` through 10,000, so the
full-core run consists of these 92 grid points only. The scan found 27 total
crossings through 10,000,000.

## Core results and predictions

| Decade | `|S|` | Head range on `S` | Head times `log(N)` range on `S` | Full `H_N` / shoulder on `S` |
|---|---:|---:|---:|---|
| 3–9 | 0 | no `S` | no `S` | no `S` |
| 10–99 | 0 | no `S` | no `S` | no `S` |
| 100–999 | 0 | no `S` | no `S` | no `S` |
| 1,000–9,999 | 0 | no `S` | no `S` | no `S`; P4 empty domain |
| 10,000–99,999 | 5 | 0.0135622–0.0154222 | 0.156070–0.164645 | unavailable: shoulder not computed above 10,000 |
| 100,000–999,999 | 10 | 0.0100910–0.0132573 | 0.138270–0.154455 | unavailable: shoulder not computed above 10,000 |
| 1,000,000–10,000,000 | 12 | 0.00785503–0.00988553 | 0.125441–0.137119 | unavailable: shoulder not computed above 10,000 |

The exact crossings and their `b_N`, `b_(N+1)`, head and head-times-log values
are in `core_crossing_values.csv`. Decade minima/maxima and the log-grid
head/shoulder/full ranges are in `core_decade_summary.csv` and
`core_grid_summary.csv`. Full `H_N` over `S` has no computed point: `S` is empty
through 10,000 and full shoulders were intentionally not run above 10,000.
The 92 grid values are separately preserved in `core_full_H.csv` and
`core_full_grid_points.csv`.

- **P3 — MISS.** There are zero crossings in `[3,10^4]` (required: at least
  ten), and the first four listed decades are empty. Later counts are 5, 10,
  and 12.
- **P4 — MISS, `NOT_TESTABLE_EMPTY_SET`.** `S intersect [1000,10000]` is empty;
  no maximum over that set is reported.
- **P5 — HIT on this finite scan.** At the 27 crossing points `N>=10,000`,
  `head_N log(N)` ranges from 0.1254411 to 0.1646451, inside `[0.02,0.3]`.
  This is not an asymptotic claim.
- **P6 — HIT.** See J4 below; the fitted full planted-head slope differs from
  the exact discrete plant self-term slope by `0.00242455`, below `0.05`.

## J3 finite identity subjudge

For each `N=3..200`, a literal residue-basis sum over every `1<=k<K_N` was
compared with the requested `A/B/C` prefix head plus the grouped full shoulder.
All 198 comparisons pass `1e-10`; the maximum absolute discrepancy is
`2.456368441983159e-15` at `N=165` (`core_j3.csv`). This is recorded as
`J3_finite_identity`, a clarified finite normalization subjudge. The literal
infinite tail was not independently summed. Although `E_N^S=H_N+exact_tail`
is an identity, the source's `5/log^2(N)` is only an upper bound and was not
subtracted as though it were the exact tail.

## J4 planted control

Use the literal plant

```text
rho = 5/6 + 7i
f(k) = 2 Re(k^rho/rho)
     = k^(5/6) [60 cos(7 log(k)) + 504 sin(7 log(k))] / 1789.
```

This starts with `f(1)=60/1789`; it is never recentered or subtracted. The
unchanged `s_N` is used. With `x_N=L s_N`, the planted head is computed from

```text
1/L^2 * [A_N - 2 x_N B_N + x_N^2 C_N
         - 2(Q_N - x_N R_N) + P_N],
Q_N=sum(psi(k) f(k)/[k(k+1)]),
R_N=sum(f(k)/(k+1)),
P_N=sum(f(k)^2/[k(k+1)]).
```

The discrete self term `P_N/L^2` is accumulated from `k=1` through each
selected `N` and supplies the preregistered finite-window slope reference. The
analytic self-energy has power `2 Re(rho)-1=2/3`, logarithmic factor
`log(N)^-2`, and relative oscillation `1/sqrt(442)`:

```text
P_N/L^2 = (108/1789) N^(2/3)/L^2
          * [1 + cos(14L - 2 atan(42/5) - atan(21))/sqrt(442)] + O(L^-2).
```

On 101 rounded log-spaced points in `[10^5,10^7]`, the raw fitted log slopes
are `0.5191977397533443` for the full planted head and `0.5216222853522573`
for the discrete self term; their difference is `0.00242454559891303`. After
multiplication by `log(N)^2`, the slopes are `0.6647929112398049` and
`0.6672174568387180`. The nonoscillatory local trend is
`2/3 - 2/log(N)`. `core_j4.csv` preserves every prefix result;
`core_j4_analysis.json` records the fits and no-offset check.

## Runtime, plots, and rounding

The completed 10-million scan took `88.7376 s` with the final native source;
the matching source SHA-256 is in `core_runner_metadata_scan.json` and equals
the full-core runner's hash. Before full shoulders, a 20,000-row sample at
`N=10,000` measured `2.0692e8` quotient groups/s. The exact total across the
92-point grid is `7,576,920,786` groups; its estimated runtime was `36.62 s`.
The full run took `32.2368 s` and evaluated `8,519,108` shoulder rows.
Runners used `uv run --no-project --python 3.15`; the complete commands and
environment are in `core_runner_metadata_*.json` and progress/ETA is preserved
in `core_*_run.log`.

SVG plots are provided. Quick Look thumbnail PNGs were omitted because that
renderer cropped the right side of these wide log plots. The two full-`H_N` plots cover only the 92
full-grid points; they have no `S` marker because there is no `S` point in that
computed domain. The two head plots use 1,500 rounded log-spaced display points
plus every crossing, while the compressed source CSVs retain all 9,999,998
head rows with no display decimation.

No mathematical rows were truncated. The 100 log-grid locations were rounded
to the nearest integer and deduplicated (92 unique values). Printed head and
plant values show 21 significant digits but carry only the platform's 53-bit
mantissa; sign classifications alone are interval-certified. The J3 difference
is finite floating arithmetic, not a proof certificate. All reported slope
fits and P5 scores apply only to the stated finite ranges.
