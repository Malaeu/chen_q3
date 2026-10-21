# Post-Q05 own calculation: a uniform one-sided endpoint budget

2026-10-21. Original sparse-band CCM. Root derivation; read-only q06_signed_preflight independently checked E1–E3 and both power substitutions (bounded PAPER PASS).
No full power gain, no actual numerical CCM evaluation, RH OPEN.
This quantifies the remainder in the already known cubic/fifth-order endpoint
sign test; it does not reclassify that indefinite kernel as negative.

Let L=log m, M=floor(m^epsilon), Omega=2pi M/L and f be the original
normalized Fourier synthesis of c in ran P. Thus ||f||_2=||c|| and f(0)=f(L)=0.
Extend the same Fourier polynomial periodically. For 0<=h<=L,

 q(L-h)=c*Q_M(L-h)c=2 Re integral_0^h f(t-h) conjugate(f(t)) dt.

Put a=f'(0), B=||f''||_infinity on one period. Taylor's formula on both
sides of zero gives f(t)=at+r_+(t), f(t-h)=a(t-h)+r_-(t), with
 |r_+|<=Bt^2/2, |r_-|<=B(h-t)^2/2.
Retaining the leading sign before bounding the remainders gives

 q(L-h) <= -|a|^2 h^3/3 + |a| B h^4/6 + B^2 h^5/60
         <= 3 B^2 h^5/80.                                      (E1)

Indeed the first two terms complete the square as
 -h^3/3 (|a|-Bh/4)^2 + B^2 h^5/48;
1/48+1/60=3/80. No lower bound or sign of q is inferred.
Cauchy--Schwarz on the ORIGINAL Fourier coefficients gives
 B^2 <= (2M+1) Omega^4/L ||c||^2.
Therefore, uniformly on the complete original projected space,

 P Q_M(L-h) P <= 3(2M+1)Omega^4 h^5/(80L) P.                    (E2)

No mixed Fourier terms have been deleted: the scalar argument holds for
all c at once. The exponential constraints are retained, though E1 only
needs the original endpoint constraint. There is no new projection.

For 0<h0<=1, the full prime-power upper shell
 E_m(h0)=sum_(m exp(-h0)<n<=m) Lambda(n)/sqrt(n) P Q_M(log n)P
has positive weights, Lambda(n)<=L, at most m h0+1 integers, and
n^(-1/2)<=exp(h0/2)/sqrt(m). Hence

 E_m(h0) <= (3/80)exp(h0/2)(2M+1)Omega^4 h0^5
                        (sqrt(m)h0+m^(-1/2)) P.               (E3)

This is a one-sided bound, not a norm bound. All prime powers and endpoint
n=m (whose atom is zero) are retained. At h0=m^(-kappa), the two power fees
are 1/2+5epsilon-6kappa and -1/2+5epsilon-5kappa, with an additional L^(-4).
Choosing kappa=1/12+epsilon makes them -epsilon and -11/12 respectively.
Thus this narrow shell has an o(1) upper budget for each fixed epsilon>0.
The remaining bulk is NOT estimated. No full exponent improves.

## Why this does not finish the problem

The old Q03 endpoint sign test already exhibits a positive fifth-order
null direction. E1 pays it rather than discarding it. The full raw-block
obstruction at fixed logarithmic distance remains untouched.
One cannot tile the whole source with E3: shifting the window changes the
original frequencies, P and test vector. Nor can one sum a per-step fee
without counting all steps. FULL_CCM_MOMENT_SCHEDULE.md already records
moving-old-block and mode-enlargement costs for the full-space schedule.

A concrete remaining question is whether the sparse projected schedule's
vanishing lower endpoint jets can be used in a ONE-SIDED signed drift,
with all old atoms, P-motion, new modes and positive spectral parts paid
jointly. The local cubic credit alone supplies no such drift. If this only
returns a known full-space moment obstruction, backtrack further; do not
rename that obstruction as a new theorem or assume the missing drift.
