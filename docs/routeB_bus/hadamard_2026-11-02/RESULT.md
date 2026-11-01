# Hadamard CCM diagnostics

STATUS: DIAGNOSTIC_NEVER_A_PROOF

This archive records the computations performed on 2026-11-01, under the
owner-requested 2026-11-02 directory. No RH, NOESCAPE, uniform edge bound,
interval certificate, or converged infinite-dimensional bottom is claimed.

## Source and normalization

The matrix is the literal `matrix_K` in
`../fokas_k_sign_2026-09-25/full_center_probe.py`, with L free and modes -N..N.
All prime powers with log(n)<L are retained. At equality their energy is zero;
left/right derivatives use the appropriate atom set. Computations use the
real even block, unit L2 ground vector, and the physical endpoint trace.

The identities checked are (4.5) and (5.3) of
`../proshka/PROSHKA_VERDICT_HADAMARD_CCM_2026-11-02.md`, source commit
`0f7006e1351ca0e7e454338db34440f833c96a56`.
The second imported verdict is
`PROSHKA_VERDICT_CCM_HADAMARD_WINDOW_2026-11-02.md` at
`3d1febdc77d8e153eee6097ab9b5836fadcb8ee9`.

The theta profile is

    h(x) = sum_{n>=1} (16*pi^2*n^4*exp(9*x/2)
                      -24*pi*n^2*exp(5*x/2))*exp(-pi*n^2*exp(2*x)),

with its even continuation, Fourier convention exp(-itx), and hat(h)=4*xi(1/2-it).
P_N h is the literal L2 projection on the window Fourier modes, not full-line
Fourier samples and not an independently normalized theta profile.

## Results

- Formula (4.5) numerically confirmed: all five terms (pole, arch interior,
  arch boundary, active-atom interior, active-atom boundary) sum to the
  independently differentiated Hellmann--Feynman slope. The same 94-point
  grid at N=8,12 gives 206 side-resolved rows. Worst relative discrepancy
  is 1.474e-51. Cancellation reaches 29.47 decimal digits.
- Formula (5.3) numerically confirmed at every prime-power threshold in
  [log 8,log 16]: slope jump = -2*Lambda(n)/sqrt(n)*|f(L/2)|^2.
  Worst finite-difference relative discrepancy is 1.164e-18; the HF check
  is tighter. Non-prime-power thresholds have zero arithmetic slope jump.
- Fixed-N slope signs are resolution-sensitive artifacts in this scan,
  not a demonstrated failure of full-support min--max monotonicity.
  At log12 the slope changes from +7.58735310314e-50 at N40 to
  -4.22832454845e-50 at N44. This does not prove that every positive
  finite-N slope disappears in the infinite-dimensional limit.
- No relative 1e-3 N-convergence at either tested L>=log12 (log12 and log16)
  through N44. The ratios lambda40/lambda44 are 12.94450617 and 395.0670596.
  Log8 also fails through the extension: lambda64/lambda68=1.009226498.
  Therefore no scan is labelled as using a converged N(L).
- w0(N44)=0.998555907367 / 0.999437782206 / 0.999844937250 at
  log8/log12/log16, respectively (approximately 0.9986/0.9994/0.9998).
  Bottom approximately h survives as a normalized L2-overlap observation;
  energy-scale or boundary-trace equivalence does not follow.
- The proposed R_N plateau approximately 27 at log8 needs qualification.
  The extension does NOT stay in 26--28: R60=25.37705144,
  R64=24.95498870, R68=25.61714944. These are moderate finite ratios with
  a rebound, not an established plateau, monotone decay, or uniform bound.

Here R_N=|f_N(L/2)|^2/lambda_N. At L=log8:

| N | R_N | R_N/L |
|---:|---:|---:|
|48|27.6381908293|13.2911602829|
|52|27.3075076486|13.1321352879|
|56|26.4087177854|12.6999087284|
|60|25.3770514445|12.2037820905|
|64|24.9549886977|12.0008128132|
|68|25.6171494410|12.3192448201|

## Data and validation

- `hadamard_2026-11-01/`: original scan, five-term decomposition, threshold
  jumps, literal m=4..20 edge and mode-insertion tests, and validation.
- `hadamard_convergence_2026-11-01/`: three-anchor N8..44 eigenvalue
  convergence tests and N40/44 anchor derivatives.
- `hadamard_resolution_2026-11-01/`: overlap and edge tests for every
  integer N8..44, log8 eigenvalue extension through N68, and edge extension.

All CSVs and Python code are retained, along with JSON/JSONL inputs and
validation summaries required by the reporting scripts. Historical partial
scan output, process logs, and bytecode caches are excluded. The validation
source path was adjusted to the new archive location; numerical code and
data otherwise retain their recorded values. SHA256SUMS covers every other
file in this archive.

The base scan uses 80 dps. Convergence and resolution use 100 dps, independently
checked at 140 dps with increased quadrature order. Worst relative checks:
N-convergence eigenvalues 1.071e-37; overlap 1.847e-46; edge ratios 1.041e-37;
log8 extended eigenvalues and edge ratios 5.47e-68. These are floating
cross-checks, not rigorous quadrature/roundoff enclosures.

## Replay

Run from this directory, with Python and mpmath available, for example:

```sh
uv run --with mpmath hadamard_2026-11-01/probe.py 64
uv run --with mpmath hadamard_2026-11-01/finalize.py
uv run --with mpmath hadamard_2026-11-01/decomposition.py 64
uv run --with mpmath hadamard_convergence_2026-11-01/convergence.py 96 100
uv run --with mpmath hadamard_convergence_2026-11-01/convergence.py 128 140
uv run --with mpmath hadamard_resolution_2026-11-01/overlap_edge.py 96 100
uv run --with mpmath hadamard_resolution_2026-11-01/overlap_edge.py 128 140 --validation
uv run --with mpmath hadamard_resolution_2026-11-01/push.py 128 100
uv run --with mpmath hadamard_resolution_2026-11-01/push.py 160 140
uv run --with mpmath hadamard_resolution_2026-11-01/push_edge.py 128 100
uv run --with mpmath hadamard_resolution_2026-11-01/push_edge.py 160 140
```

The original scan/decomposition scripts resume from existing JSONL data.
For a fresh recomputation, use a disposable copy and remove its
`results_gl64.jsonl` and `five_terms.jsonl` before running those scripts;
run `finalize.py` after the original scan to produce `hadamard_results.jsonl`.
