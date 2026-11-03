# Q4 normalization

Psi is exactly the negative screw sourceg used by our original arithmetic
implementation, with Psi(0)=0. It is not the archimedean-prime Fourier
symbol also denotedPsi in some Weil-form papers. With
alpha=(EulerGamma+log(8pi)+pi/2)/2 and C0=pi²/4+2Catalan-8,
Proposition2.1 gives Psi(logX)=C0-F(X). Separating the k0 term of the
Lerch series cancels4X^(-1/2); the remaining constant is exactlyC0.
No shift or multiplicative factor is fitted. crosswalk.csv compares the
two source expressions at twenty fixed times; crosswalk.json separately
checks alpha against zeta'(1/2)/zeta(1/2).

Checkpoint values are continuous at prime powers because the triangular
weight log(X/n) vanishes at birth. Derivatives have downward jumps forPsi;
there is no halfweight ambiguity in the value of the smoothed form.
