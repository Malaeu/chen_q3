# Polylog band does not make the existing sharp-prefix Perron return cheap

2026-10-25. Root bounded calculation; source Q10 §§5--6, equations (13)--(24).
Original K_m/P and original R=floor(m^epsilon) retained. Auxiliary H0 is the
verified subspace from CCM_POST_Q26_POLYLOG_WITNESS.md, not a replacement
for the all-P goal. This tests one completion, not the truth of CCM.

On H0, Omega=2pi ceil(8L^2)/L=16pi L+O(1/L). Try to use Perron height
T=C L, C>64pi, rather than m^2, because every tested frequency is O(L).
This is a contour-height parameter, not the pair-averaging parameter T in
Q17. The sharp scalar prefixes still range over EVERY 1<=y<=m.

Q10 (16) retains all true Lambda coefficients and all inversion tails:

 |E_Pe| <= 512 sqrt(m)L^2/T.

This supplied upper certificate is independent of omega. It comes from
the discontinuous cutoff and near-integer denominators log(X/n), with
X=floor(y)+1/2. Reducing the test frequencies does not remove these terms.
At T=C L its price is O(sqrt(m)L), not a subpower bound. This is a price of
the available certificate, NOT a lower bound for the actual Perron error.

Under the SAME inherited ZF78 premise, retain a=3/8+1/L and c=1/2+1/L.
With T>=2Omega+2, the Q10 local-pole and horizontal arguments give

 |I_a| <= Ccl m^(3/8) log(T+Omega+8) log(T+3) log(3L),
 |horizontal| <= Ccl sqrt(m)L log(T+Omega+8)/T.

All sides and the exactly cancelled main pole are retained. The residual
constant, y-to-X interval and decaying continuous integral cost O(1).
The Hilbert matrix transfer Q10(21) is already dimension-free and costs
at most four times the full scalar-prefix bound, including both diagonal
and off-diagonal entries. Its compression is legitimate on H0, but brings
no further dimension factor to save. The existing short return is
O_epsilon(m^(epsilon/2)L+L^2), and the negative -2H_H0 credit is retained.
Consequently this low-height trial provides only

 T_>R|H0 <= [C'cl m^(3/8)(log L)^3 + C'cl sqrt(m)L
            +O_epsilon(m^(epsilon/2)L+L^2+1)] I_H0 -2H_H0.

Here C'cl is enlarged to include the factor four from the Hilbert transfer
and the fixed choice C in T=C L; it is independent of m.

The resulting upper certificate is worse than the accepted Q10 envelope.
For T=m^kappa, fixed 0<kappa<=2, eventually T>=2Omega+2, its two leading
power prices are m^(3/8) and m^(1/2-kappa), up to logarithms. Taking
kappa>=1/8 returns exponent3/8; taking larger kappa alone never lowers the
3/8 contour price. Without ZF78 this computation does not supply3/8.

Concrete rollback: BEFORE the scalar-prefix supremum and separate absolute
pole payment. A full smooth matrix pairing might have a different inversion
tail, but it must be derived on the original Q/P with all contacts and mixed
terms. Smoothness cannot simply be assigned to the sharp scalar prefixes.
The actual pair's exponential Fourier tail established the witness return;
it is not a uniform property of every vector in H0 and not an arithmetic
estimate for the prime coefficients. This is a specific no-gain trial,
not three attempts and not a no-go for signed cancellation.
