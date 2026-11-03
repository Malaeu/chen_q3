# Real-positive spectral controls

**DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER / NOT_RH.**

The registered ordering `Poisson < zeta approximately GUE < picket` does not
pass the stated finite tests. A weaker Poisson-below-GUE trend is present in
the surrogate models. The real-zero zeta surrogate also fails its quantitative
calibration against the actual arithmetic source on the two fine grids, so
this experiment supplies no law for the actual zeta margin.

Primary statistic: median one-endpoint clearance over old history a in[1,6],
with the next endpoint a+Delta. Each row below summarizes20 independent
Poisson and20 independent GUE-bulk replicates, except the deterministic
picket, zeta and arithmetic-reference columns.

| Delta | Poisson median | GUE median | zeta<=400+tail | arithmetic zeta | picket |
|---|---:|---:|---:|---:|---:|
|1/32|.237982|.247752|.257741|.259794|.250062|
|1/64|.258631|.270311|.282886|.279368|.251209|
|1/128|.295509|.314313|.311142|.290764|.296345|
|1/256|.368360|.392600|.391776|.358555|.393689|

The paired Poisson-below-GUE fractions are .75,.80,.85,.90 across the four
meshes. The GUE-below-picket fractions are .60,0,0,.60, failing the registered
.75 criterion on every mesh. Thus the full proposed order is rejected in
these models; simple median comparisons alone would hide ensemble overlap.
The zeta surrogate lies inside the empirical central95% GUE interval on all
meshes, but the actual arithmetic zeta lies outside it on the two fine meshes.
That comparison is not a significance test or an actual-zeta universality law.

## Matched mean density and spectral generation

Positive zeta ordinates come from the existing180digit table through400:
202points, last399.9851198761949. No zero above this verified table is
invented. Every spectral world includes the negative partner with the same
weight, and uses g(t)=2sum_(gamma>0)(cos(gamma*t)-1)/gamma², plus the
specified common tail. Every world is PSD by construction; positivity is
not an independent result about the arithmetic zeta source.

Use the smooth counting coordinate
F(T)=T/(2pi)*(log(T/(2pi))-1)+7/8. Synthetic heights are F^-1(u).
Every synthetic realization is anchored at the same gamma1 as zeta.
Poisson spacings in u are independent exponential mean1; this anchoring is
explicit conditioning, not a stationary process with an arbitrary origin.
Picket spacings in u equal1.

GUE controls use the central bulk of20 size4096 Hermite-beta2 tridiagonal
samples: diagonal N(0,1), off-diagonal chi_(2*(n-i))/sqrt2. Semicircle
unfolding uses radius2sqrt(n). Their realized mean unfolded spacings average
.9999844 and range.9981602..1.0011161. These are finite GUE bulk controls,
not an assertion that zeta is GUE. Seeds are20261103+replicate index;
Poisson and GUE draws use the registered generator sequence. Pairing by
index is a registered comparison, not a physical coupling.

An initial harness used the wrong semicircle radius sqrt(2n), violating the
same-density contract. It was corrected before outcome interpretation.
`initial_density_error_metrics.csv` preserves its invalid comparison;
it is excluded from every conclusion. Full initial raw outputs are retained
locally under /tmp/ladder_spectra_wrong_density_initial. The corrected script,
proper scale, and repair are explicit in the preregistration.

## Tail, rank and conditioning controls

The primary discrete cutoff is400. Beyond it, each world receives the same
continuous density rho(gamma)=log(gamma/(2pi))/(2pi). Positive frequency-bin
weights integrate rho/gamma² on bins of width2pi/16. FFT evaluates their
cosine sum on the exact dyadic time grid. The unrepresented high-frequency
mass is added as a **positive independent-point-noise** tail. It is a
numerical finite-grid tail approximation, not an exact continuous screw
function: at ever smaller scales that remainder is discontinuous.

Primary FFT size2^22; fixed-world checks use2^20,2^22,2^24. Changes from
2^22 to2^24 are at most5.17e-11 in the primary metric and7.77e-9 in
q32 margins at a6. Thus numerical tail-grid resolution is not responsible
for the failed arithmetic-source calibration. Independent positive frequency-bin
refinement (period16/32/64, the same upper frequency cutoff) changes primary
metrics by at most2.67e-6 and q32 block margins by7.96e-6.
Model scalar and block matrices
need no PSD clipping. All tail-included tested model cells remain positive.

The same generated spectra are also examined at cut800 and1600 for the first
four registered random replicates, with a common density tail beyond each
cut. At mesh1/256 the Poisson metric medians are .362753,.316570,.301078;
GUE medians .394398,.371119,.368978; picket .393689,.393690,.393714.
The material cutoff dependence is retained as model uncertainty, not called
convergence of true zeta. No true zeta ordinate above400 was supplied.

The registered .02 arithmetic-calibration gate fails: absolute differences
are .002053,.003518,.020378,.033221 across the four meshes. **This blocks
interpreting the spectral ordering as an explanation of actual zeta.**
A continuum tail can erase discrete high-zero information important to
prediction, even when its mean density and scalar numerical quadrature are
well controlled. The actual arithmetic reference uses the same old-history
indices; one extra MP90 g(6+Delta) value extends the saved MP100 covariance
so the endpoint labels are not accidentally shifted by one step.

The pure zero-table truncation, with no tail, is a negative numerical
control. Its exact Gram rank is at most404. Resolved positive prefixes stop
at354,275,24 on meshes64,128,256 under the stated numerical guard. These
are conditioning/rank failures of a PSD construction, never negative-world
or RH evidence. The coarse mesh32 resolves all193requested prefixes.

A second robustness control fixes exactly202points and the first ordinate
for the first four random replicates. Unfolded offsets are rescaled so the
203rd position is the cutoff boundary; the202interior points are retained.
This is a rescaled count-matched control, not an unmodified GUE ensemble.
Poisson-below-GUE survives in3/4,4/4,4/4,4/4 pairs, but it does not restore
the registered GUE-below-picket order. Hence the observed weaker trend is
not solely the larger Poisson point-count variance.

## Artifacts and reproduction

`scalar_profiles.csv` retains all resolved one-step histories; `future_blocks.csv`
retains q1,4,8,16,32 at a1,3,6. `generated_spectra.json` permits exact replay
of the model inputs. Ordering, density/count controls, FFT convergence and
no-tail rank failures have separate CSVs. SUMMARY.json records the kill gates.
All floating failures are labelled unresolved; no eigenvalue or pivot is clipped.

```
uv run --with numpy --with scipy python spectra.py
uv run --with numpy --with scipy --with mpmath python controls.py
uv run --with numpy --with scipy python zero_tail.py
uv run --with numpy --with scipy python bin_convergence.py
uv run --with numpy --with scipy python analyze.py
uv run --with numpy --with matplotlib python plot.py
```

No infinite-history positivity, real-zero completeness, uniform margin floor,
arithmetic source law or RH conclusion is inferred. See CARDS.md for the
hypotheses, evidence, killers and exact handoff limitations.
