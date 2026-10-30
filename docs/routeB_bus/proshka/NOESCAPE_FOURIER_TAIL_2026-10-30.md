# Explicit m16 Fourier tail budget (independently checked bounded PAPER)

This bounds the omitted F sum beyond |n|=96 on the original m=N=16 cell.
It does not bound quadrature in the independently evaluated X. Source form
and high-mode kernel are NOESCAPE (4.7)-(4.10), same L=log16, same primes<=16.
Let v be any unit carrier vector; its coefficient l1 norm is <=sqrt33<6.

## Whole-line sample bound without RH

For s=1/2+it, pair successive terms in eta(s):
|(2k-1)^(-s)-(2k)^(-s)|<=|s| int_(2k-1)^(2k) x^(-3/2)dx.
Hence |eta(s)|<=2|s| and
|zeta(s)|<=2|s|/(sqrt2-1)<5|s|. This uses the convergent paired eta
representation for Re s>0 and the exact eta/zeta identity, not RH.

Rotate the defining gamma integral through angle sign(t)*pi/3 to obtain
|Gamma(1/4+it/2)|<=2^(1/4)Gamma(1/4)exp(-pi|t|/6)
<10 exp(-pi|t|/6). The constant follows from
Gamma(1/4)<=int_0^1 u^(-3/4)du+int_1^infinity exp(-u)du<5.
The contour rotation is valid in the open right half-plane.

Therefore H(t)=4xi(1/2-it) satisfies

    |H(t)| <=100(|t|+1)^3 exp(-pi|t|/6).

For t_n=2pi n/L, we have t_n<3n and pi²/(3L)>7/6, so

    |H(t_n)|<=6400 n³ exp(-7n/6), n>=1.

The elementary fixed-constant comparisons can be checked with Arb; no
tail statement is inferred from sampled Xi values.

## A deliberately coarse high-mode kernel bound

For |n|>=97 and |j|<=16, use the off-diagonal entry

    K_L(n,j)=W02(n,j)−(M_j−M_n)/(pi(n−j))
       −sum_{k<=16} Lambda(k)/sqrt(k)
          [sin(2pi j log(k)/L)−sin(2pi n log(k)/L)]/[pi(n−j)],
    M_n=int_0^L j(s)sin(2pi n s/L)ds.

The pole term is bounded by32: both p=sqrt2cosh(x/2) and
q=sqrt2sinh(x/2) have absolute value<2 on the length-L<3 window;
Cauchy-Schwarz bounds the sum of the two rank-one entries by24<32.
For s>0, j(s)<=1+1/(2s). With |sin u|<=min(|u|,1),
|M_n|<=3.5+(1/2)log(2pi|n|)<=5+(1/2)log|n| for n!=0,
and M_0=0. Thus |M_j|<7 and
|(M_j−M_n)/(pi(n−j))|<1 for |n|>=97.
For example log n<=n gives numerator<=12+n/2<=n for n>=24,
while pi(n−16)>2n for n>=48.
The prime contribution is <90/[3(|n|−16)]<1, using at most15 terms,
Lambda(k)<3, 1/sqrt(k)<=1, and the sine difference bound2.
Consequently |K_L(n,j)|<34 and |k(psi_n,v)|<204<256.

## Full signed-sum remainder

Since 1/sqrtL<1, both tails together obey

    |F−F_96| <=3276800 sum_{n>=97} n³ exp(-7n/6)
               <=6553600*97³ exp(-679/6)
               <4.258e−37.

The last geometric step uses successive ratio
((98/97)^3)exp(-7/6)<1/2, which only decreases for later terms.
Root Arb dps40 returned the upper-bound expression
4.25731970301699068329090642392446685634e−37.
This is about1.01e−4 of the measured denominator4.227e−33.
It is a genuine tail bound if the analytic/source arguments above pass review,
not the difference of two truncation orders. Finite F-sum interval arithmetic,
source mapping and the independent direct-X quadrature remain separate checks.

Independent read-only audit checked eta, gamma rotation, every kernel bound,
unit-carrier l1, both tails and geometric factors; no material defect found.
Arb dps60 independently confirmed the displayed constant. Reviewed pre-status
SHA256 bc0a8910a79b1724fdc8b7e7de1e35898b9ad766c71b646fc42b73187f5274f9.
The result is conditional on the inherited literal kernel/source formulas.
It certifies the omitted tail only, not the retained finite sum or X quadrature.
