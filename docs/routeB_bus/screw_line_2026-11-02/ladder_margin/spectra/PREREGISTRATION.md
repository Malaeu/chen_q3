# Spectral-world margin comparison, before execution

DIAGNOSTIC_NEVER_A_PROOF. All spectra in this control are real and have positive
weights by construction; this is not an unconditional spectral representation
of the arithmetic zeta source.

Mythos prior .5: Poisson < zeta approximately GUE < picket in clearance.
Primary metric is the median one-endpoint margin over history lengths[1,6]
for each mesh1/32,1/64,1/128,1/256. All fixed endpoints1,3,6 and q1,4,8,16,32
will also be retained. No favorable interval or choice of normalization after
results. Define approximate equality before run: zeta surrogate is within the
central95% GUE ensemble interval for that primary metric. Strict ordering
requires at least75% of paired Poisson/GUE replicates to have Poisson below
GUE and at least75% GUE below picket, on each mesh.

Use20 independently seeded finite Hermite GUE bulk samples and20 Poisson
spacing samples. Seed base20261103. GUE: Dumitriu-Edelman beta2 tridiagonal
size4096, diagonal N(0,1), off-diagonal chi_(2*(n-i))/sqrt2. Unfold central
bulk using the integrated semicircle density; then transport unfolded
positions to physical heights using the smooth Riemann-von-Mangoldt counting
function F(T)=T/(2pi)*(log(T/(2pi))-1)+7/8. Poisson uses exponential mean1
unfolded spacings. Picket uses exact spacing1. All synthetic spectra are
anchored at the same first height gamma1 to isolate spacing from a trivial
low-edge shift. This conditioning is explicit and is not stationary Poisson.
True zeta uses the existing180digit table through400; no zero beyond its
verified source table is silently invented.

Primary cutoff400. Synthetic cutoff convergence uses the same generated
spectra through800 and1600 on the first4registered replicates of eachworld.
Beyond each cutoff use the same positive continuous RVM density tail,
implemented by positive spectral-bin quadrature and FFT on period16.
Frequencies above the represented maximum are replaced by a positive
independent-point noise remainder of the same total spectral mass. Primary
FFT size2^22, convergence2^20 and2^24 on deterministic controls. This
approximation is itself a control, not an exact continuous tail theorem.

Calibration gate (prior .5): zeta<=400+tail must reproduce the exact arithmetic
zeta primary median margins to absolute.02 on all meshes. If this fails, do
not interpret synthetic ordering as an explanation of the actual zeta margin;
report the model experiment and the unresolved tail debt. Tail-resolution
prior .9: FFT2^22->2^24 primary metrics change by less.001. Stop actual-zeta
interpretation if these fail, without tuning the cutoff/window afterward.

Budget:20replicates per randomworld at cutoff400;4perworld cutoff800/1600;
all fixed-grid scalar prefixes to6 and a1,3,6 finite-future blocks. No PSD
clipping. If float Cholesky/Levinson fails, mark unresolved and do not claim
a negative real-positive spectral world. Kill if source/tail replay does not
meet its registered error gates or runtime exceeds15minutes.

Normalization repair before outcome analysis: the stated beta2 tridiagonal has
semicircle radius2sqrt(size), so bulk x=eigenvalue/(2sqrt(size)). An initial
harness used sqrt(2size), which would give unfolded GUE spacing sqrt2 instead
of1. That incomplete run was stopped before output analysis/publication and
rerun with the correct scale. This corrects the registered same-density
contract, not a fitted hypothesis. Initial progress log is retained externally.

Before equal-count robustness control: first4 registered random replicates,
cut400, samefirstgamma and same202points as zeta. Rescale unfolded offsets
so the next(203rd) position lands exactly on F(400), then retain202positions.
Apply the same rescaling to the picket. This is a density-matched rescaled
control, not an exact finite GUE ensemble. Prior .8 that this count matching
does not reverse the primary Poisson/GUE/picket ordering. No extra seeds.

Reference-index normalization: the model mu at history a uses innovation at
a+Delta. Saved arithmetic CSV time labels the new endpoint instead. The
calibration reference is therefore recomputed at identical old histories
[1,6], appending one MP90 g(6+Delta) value to the old MP100 r vector. This
is an index correction, not a fitted time-window change.

Before zero-tail negative control: zeta's202positive zeros through400 with
no tail have rank at most404 on sampled increments. Prior.99: at least one
fine grid loses a numerically resolved positive prefix before t=6. Treat
this as rank/conditioning failure of a PSD control, never a negative world.
This diagnoses why pure truncation is not a legitimate reference model.

Before quadrature-bin convergence run: fixed high frequency cutoff and
positive density bins, period16/32/64 with FFTpowers22/23/24 respectively.
Registered control worlds zeta surrogate and picket only. Prior.95 that
primary metrics change by less.001. This tests frequency-bin quadrature
separately from the already passed maximum-frequency refinement.
