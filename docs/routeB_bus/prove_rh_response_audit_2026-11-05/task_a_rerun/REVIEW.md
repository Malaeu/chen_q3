# Independent read-only instrument review

Observed native reviewer report; no provider signature or interval certificate
is claimed. Reviewer authored no delivered files.

No preregistration mismatch or blocking mathematical/code defect found.

- The driver imports the unchanged original C/F/g/atoms and checks the pinned
  source blob. Five t values, dps50/70, cutoff floor(exp(t+12)), original H
  quadrature, zero cutoff and quartet polarization match the requested rerun.
- The c_* perturbation has the correct sign: arithmetic changes by -1e-10 C(t).
- The omitted-tail derivation is valid. It uses only Lambda(n)<=log n,
  decreasing-function integral comparison, the explicit C polynomial and a
  Gaussian logarithmic-derivative bound. Both shifted C tails are included.
- Evaluating the analytic bound at50/70 dps, adding0.1% slack and rounding
  upward to8 significant digits gives the same reported values at both dps.
  This is numerical evaluation of an analytic bound, not interval arithmetic.
- Completed results contain20 baselines PASS and20 perturbed cases FAIL in
  both worlds and precisions. Maximum reported tail5.2775635e-20 is below1e-18.
- Baseline residuals remain above the tiny true zeta response; the result is a
  finite absolute normalization check, not a relative response/sign estimate.

DIAG only; no RH or (7.4) conclusion.
