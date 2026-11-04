# Pre-run predictions — corner versus whole matrix

DIAGNOSTIC_NEVER_A_PROOF. Route B: CHALLENGER / NOT_RH. Separate diagnostic lane; no D0 or route-state change.

## Owner predictions (verbatim)

D1: m_matrix < m_corner for every (a, γ) on the grid. P = 0.80

D2: m_corner grows with γ, while m_matrix stays essentially flat once T_m > γ. P = 0.60

D3: the negative eigenvector peaks at frequency ω ≈ γ (within 2π/L). P = 0.75

## Fixed experiment contract

- Literal even physical L2 basis, j=0,...,m (dimension m+1), L=log m, d0=1, dj=sqrt(2), omega_j=2pi*j/L. Unit eigenvectors use this basis.
- Admissibility follows HIGHER_MOMENTS §1 exactly: T_m=(1+(1+log L)/(4L))*2pi*m/L. Require strict T_m>γ. Also record Ω_m=2pi*m/L and whether γ exceeds Ω_m; do not silently replace the cutoff.
- a in {0.05,0.1,1/3}; γ in {14,50,200,800}. a=1/3 is evaluated as an exact rational at high precision.
- Q=4 Re(c c^T), c_j=2*d_j*z*sin(zL/2)/(sqrt(L)*(z²−omega_j²)), z=γ+ia, multiplicity one. Gate at m=80: direct coefficient construction versus independent physical-kernel quadrature must agree entrywise within1e-12. Apparent resonances use their removable values.
- First eligible m is found among integers m>=16. Corner is scanned at every eligible integer through3000. Matrix starts at that first eligible integer and scans consecutive integers until a trigger, so a claimed first threshold has no skipped predecessors. After first detection, use additional validation checkpoints through3000, or an explicitly documented feasible cap.
- Corner trigger: strict negative (A+Q)[0,0]. Matrix trigger: lambda_min(A+Q)<−1e-6. Confirm each first matrix trigger using a freshly assembled source and a Rayleigh witness at >=50 decimal digits; distinguish a witness from a complete high-precision ordering computation. Recheck predecessor when the threshold is later than admissibility.
- At every matrix-grid cell, unplanted lambda_min(A)>=−1e-12 and a=0 must not trigger either detector. Tiny floating negative values are unresolved noise, never planted detections. Any failed control stops scoring until resolved.
- The pinned MPFR source is retained unchanged. A zeta-only vectorized implementation is allowed for scale, only after comparison against that source at m=80 and selected larger cells; all prime powers, full archimedean terms, endpoint tails and pole are retained.
- Report a censored threshold as >M, never as an observed crossing. When matrix is detected before the exhaustive corner scan cap and corner is not, D1 is supported only with that censoring made explicit. Both-censored cases are inconclusive.
- D2 is reported in two parts: ordered corner thresholds/censor bounds against γ, and raw matrix thresholds together with admission-adjusted delay m_matrix−m_admit. Operational conditional flatness means delay<=max(2,0.05*m_admit); this does not turn raw γ-dependent admissibility into a claim of constant raw m_matrix.
- D3 is literal: peak coefficient energy |v_j|² at the first detected matrix cell must satisfy |omega_peak−γ|<=2pi/L. Record the peak, centroid, top modes and boundary-of-band flags. An unavailable frequency is a failure of the stated prediction, not an excuse to widen its tolerance.
- Budget: benchmark actual source/eigensolver work after this file is committed. Escalate precision or lower the documented cap when required; no numerical stabilization occupies a cofinal quantifier. Preserve failures and actual tested cells. No RH claim.

## Source pins

- 2ad7342c: 2ad7342c2d0b236f627aa23ccc955e2190ffcade
- c8ef1314: c8ef1314c1fbc9e8292f3bc92d18d6fc2716eaa0
- 5e61a39d: 5e61a39dc564fe76487146823f0b5d711014f981
- Matrix builder Git blob prefix:27bbaab (verify full blob/SHA256 before execution).

This file is committed before any numerical experiment in this packet. Read-only source inspection and experiment design precede it; no matrix, gate, detector or control has been run.
