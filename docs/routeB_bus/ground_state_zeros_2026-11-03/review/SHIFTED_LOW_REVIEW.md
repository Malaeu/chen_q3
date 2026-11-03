# LOW point-ground refinement review

PASS for the frozen helper and final native-fallback driver identified in
shifted_low_final_review.json. Adoption is limited to LOW zeta ground
validation; preferred HIGH pairs retain their complete native ordering.
This does not certify the source functional or promote mathematical status.

The helper explicitly rounds LOW/HIGH matrices to their actual solver
precisions. Its measured point-matrix perturbation and HIGH error estimate
must be smaller than the preferred HIGH gap. The selected shift lies below
the corresponding LOW ground by a positive margin. The shifted solve must
improve the seed residual and satisfy separate residual/location gates.
The current full finite HIGH gap/order is supplied by the existing native
solver; no positivity or RH premise occurs.

Independent controls rebuilt LOW/HIGH sources and used stored HIGH native
pairs for zeta even/odd at m160 and m300, plus the negative DH odd m300
control. All five pass actual-point rounding, residual, normalization,
shift/correspondence, and stored native LOW vector comparisons. DH correctly
uses actual 512/640 solver bits despite the higher uniform source precision.
No HIGH eigenproblem was repeated. Selected physical-root corrections at
m300 are at most 1.324e-149 even and 1.261e-154 odd; the even maximum
reproduces the existing all-183-root probe's maximum.

LOW lambda1/vector1/residual1 are explicitly null in refinement mode.
Their Weyl range is labeled empirical point-matrix information, not an
independent LOW second-pair computation. The repaired wrapper catches any
ordinary refinement exception and runs the existing native LOW pair,
recording the rejection and the fact that the second pair was then computed.
HIGH ordering and source formulas remain unchanged.

The reviewer exceeded the approximately 60 CPU-second test budget: the five
controls reported 84.92 CPU seconds despite an RLIMIT_CPU(60,63) process
guard. This overrun was disclosed immediately. The final wrapper/schema
review was read-only; no further numerical tests were run.

Exact receipts are in shifted_low_review.json and
shifted_low_final_review.json. Diagnostic residuals and 180-digit output
rendering must not be presented as rigorous source/error enclosures.
