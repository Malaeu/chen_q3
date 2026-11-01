Hadamard probe, fixed harmonic dimension and literal diagonal

DPS80_FLOATING_DIAGNOSTIC_NOT_CERTIFICATE
Source: docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py, matrix_K. Only L and mode bound are made independent. Prime atom k is included when log(k)<L. At exact thresholds left/right continuations explicitly freeze the appropriate atom set.

Run: python probe.py 64; python validate.py 80; python finalize.py
The probe uses composite Gauss-Legendre quadrature on eight panels after x=L*y. Trigonometric arrays are cached at common nodes; the literal matrix formula is unchanged. Analytic derivatives include all pole, archimedean, normalization and prime-weight derivatives. HF uses the unit lowest even-block eigenvector. FD uses a five-point fourth-order formula with step1e-7; one-sided at thresholds. No centered FD straddles an atom threshold.

results_gl64.jsonl is the resumable raw output. hadamard_results.jsonl removes any duplicate rows from interrupted/restarted quadrature optimization runs. summary.json holds branch extrema, derivative signs, threshold rows and literal diagonal rows. Exact-threshold lambda0 appears twice for its one-sided derivatives.

The literal diagonal comparison N=floor(exp L) has dimension jumps at every log integer. At an exact threshold k, the left comparison uses N=k-1 and the right comparison N=k. Derivatives and r are branchwise; no derivative across a dimension jump is claimed. Fixed N8/N12 lambda0 are continuous, with rank-one derivative jumps only when Lambda(k) is nonzero.

validate.py compares order80 shared quadrature to the unchanged adaptive source matrix_K at m8 andm16, and checks Kprime_right-Kprime_left=-2Lambda(k)/(L sqrt(k))11^T through HF at every threshold k8..16. Files validation_gl80.json and validation_progress.log contain the actual readbacks.
