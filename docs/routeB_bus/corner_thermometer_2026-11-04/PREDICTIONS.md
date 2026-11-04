# Pre-registration: corner thermometer through 100,000,000

Route B = CHALLENGER / NOT_RH. Diagnostic, never a proof.
Base: rh_clean@2ad7342c2d0b236f627aa23ccc955e2190ffcade.
The following predictions are copied from the owner brief before any numerical run:

- T1 (P=0.97): Psi(log m)>0 for every integer 2<=m<=100000000.
- T2 (P=0.85): mean of Psi over t=log m, uniform in t, is in 0.0462 +/-0.003; reference 2+EulerGamma-log(4*pi).
- T3 (P=0.60): min Psi(log m) for 1000<=m<=100000000 is at least0.002.
- T4 (P=0.95): max Psi(log m) on the whole range is at most0.0924.

G1 precedes the full run: at m16,80,300 match 0.045942450631,0.044990119994,0.034530659232 within1e-10. G2: at powers of ten, compare compensated streaming values with an independent40dps mpmath prime-power sum within1e-9. G3 is optional and must be labelled conditional if only critical-line zeros are available; no unproved zero-completeness/tail premise may be hidden.

Primary uniform-t mean: integral of the same explicit Psi(t) over [log2,log(100000000)] divided by that interval length, using its analytic antiderivative and compensated prime-power sums. Also report the trapezoidal mean over the log-integer samples and the mean over [0,log(100000000)] as labelled controls. Ordinary uniform-m average is a separate statistic, not a replacement for T2.

Evaluate every integer, retaining global and m>=1000 extrema, the20 smallest values and every strict record minimum. Use compensated extended-precision sums and stable elementary/special-function tails; compare independent40dps checkpoints without source alteration. A measured violation is reported, not repaired away. Numerical observations and checkpoint agreement are not certified positivity or an RH proof.

Registration is an immutable Git commit object created before numerical work, without moving rh_clean; final delivery is one scoped branch commit carrying this identical prediction blob and the registration receipt.
