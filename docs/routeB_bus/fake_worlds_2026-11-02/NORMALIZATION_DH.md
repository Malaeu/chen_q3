# Davenport–Heilbronn normalization audit

Independent formula review, 2026-11-02. No numerical computation or new coercivity theorem. The formulas below use the literal physical even basis of `phase_space_V/v_forms.py`, including its `q_even` signs.

## Primary source and function

Bombieri–Ghosh, *Around the Davenport–Heilbronn function*, Russian Math. Surveys **66** (2011), 221–270, [primary PDF](https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&option_lang=eng&paperid=9410&what=fullteng), §5.1, pp.238–239, (5.1)–(5.2), defines the periodic coefficients and specifies the odd conductor-5 functional equation with root number +1. The same discussion on p.239 states that these functions have zeros with real part greater than 1; Theorem 7, p.241, characterizes their rightmost-zero abscissa. These facts apply to the positive Titchmarsh value below, not the other real conjugate parameter.

Put
\[
 \tau=\tan\theta=\frac{\sqrt{10-2\sqrt5}-2}{\sqrt5-1}
 =-\varphi+\sqrt{1+\varphi^2},\qquad \varphi=(1+\sqrt5)/2,
\]
\[
 F(s)=\sum_{n\ge1}a(n)n^{-s},\qquad
 (a(1),a(2),a(3),a(4),a(5))=(1,\tau,-\tau,-1,0),
 \quad a(n+5)=a(n).
\]
Equivalently, with the odd primitive character \(\chi(2)=i\),
\(F=(\sec\theta/2)(e^{-i\theta}L(s,\chi)+e^{i\theta}L(s,\bar\chi))\).
The completed function
\[
 \Lambda_D(s)=(5/\pi)^{(s+1)/2}\Gamma((s+1)/2)F(s)
\]
is entire and satisfies \(\Lambda_D(s)=\Lambda_D(1-s)\) and reality under conjugation. The source uses the equivalent completion with exponent \(s/2\); the factor \(\sqrt{5/\pi}\) is constant. In particular there is **no pole contribution at 0 or 1**, and no zeta pole rank-one term. Gamma-pole cancellations are built into the completed function: sum its zeros, rather than adding the trivial zeros of the uncompleted function a second time.

## Arithmetic coefficients: all integers, not prime powers

Define \(c(1)=1\),
\[
 c(n)=-\sum_{d\mid n,\ d>1}a(d)c(n/d),\qquad
 \frac1{F(s)}=\sum c(n)n^{-s}
\]
in a sufficiently far right half-plane. Write
\[
 -F'(s)/F(s)=\sum b(n)n^{-s}.
\]
Then exactly
\[
 b(1)=0,\qquad b(n)=\sum_{d\mid n}a(d)\log(d)c(n/d)
 =a(n)\log n-\sum_{d\mid n,\ d>1}a(d)b(n/d).
\]
The recurrence follows by multiplying the last Dirichlet series by \(F\). The notation \(b\) here is for the logarithmic derivative; Bombieri–Ghosh also use a letter \(b\) for reciprocal coefficients, so those must not be confused. Nonmultiplicativity already appears in \(a(4)=-1\ne a(2)^2\). The logarithmic-derivative coefficients are not Mangoldt coefficients and need neither prime-power support nor positivity. For example, the recurrence gives \(b(6)=(1+\tau^2)\log6\), already nonzero away from prime powers. Absolute convergence for \(\Re s>1\) of \(F\) does not imply that of \(1/F\) or \(-F'/F\): zeros occur there. Start an explicit-formula contour sufficiently far right, where the reciprocal series converges, before shifting it.

## Exact archimedean normalization

Use \(\widehat f(t)=\int f(x)e^{-itx}\,dx\), hence Parseval has factor \(1/(2\pi)\). The archimedean Fourier multiplier is
\[
 M_D(t)=\log(5/\pi)+\Re\psi(3/4+it/2).
\]
The digamma integral gives the independent check
\[
 \Re\psi(3/4+it/2)-\psi(3/4)
 =2\int_0^\infty\frac{e^{-3s/2}}{1-e^{-2s}}(1-\cos ts)\,ds.
\]
Thus
\[
 j_D(s)=\frac{e^{-3s/2}}{1-e^{-2s}},\quad
 c_D=\log(5/\pi)+\psi(3/4)
 =-\gamma-\log(8\pi/5)+\pi/2,
\]
\[
 c_D^*=\gamma+\log(8\pi/5)-\pi/2=-c_D.
\]
Both the odd gamma shift and conductor 5 matter. Merely dropping the zeta pole from the old matrix leaves the wrong kernel and constant.

For zero-extended real even functions let
\(Q_{fg}(s)=\langle f,T_sg\rangle+\langle f,T_{-s}g\rangle\).
The exact DH Weil form in this normalization is
\[
 \mathcal K_D(f,g)=c_D\langle f,g\rangle
 +\int_0^\infty j_D(s)(2\langle f,g\rangle-Q_{fg}(s))\,ds
 -\sum_{n\ge2}\frac{b(n)}{\sqrt n}Q_{fg}(\log n).
\]
For the cross form use the corresponding sesquilinear correlation. This is the completed-function explicit formula; it includes **all completed zeros**, not just zeros in the classical strip. No extra \(2\pi\) multiplies either the arithmetic atoms or the zero evaluation sum: the inverse-Fourier factor has already been used in obtaining correlations.

## Finite even matrix

Let \(L=\log m\), \(d_0=1,d_n=\sqrt2\) for \(n>0\), and
\[
 \phi_n(x)=\frac{d_n(-1)^n}{\sqrt L}\cos(2\pi nx/L),\quad |x|\le L/2.
\]
For \(r=s/L\), \(0\le s\le L\), the literal `q_even` is
\[
 Q_{ii}(s)=2(1-r)\cos(2\pi ir)-\frac{\sin(2\pi ir)}{\pi i}\quad(i>0),
 \qquad Q_{00}(s)=2(1-r),
\]
\[
 Q_{ik}(s)=\frac{d_i d_k}{\pi}\,
 \frac{k\sin(2\pi kr)-i\sin(2\pi ir)}{i^2-k^2}\quad(i\ne k).
\]
It is zero for \(s\ge L\). Therefore
\[
 (K_D)_{ik}=c_D\delta_{ik}
 +\int_0^L j_D(s)(2\delta_{ik}-Q_{ik}(s))\,ds
 +2\delta_{ik}\int_L^\infty j_D(s)\,ds
 -\sum_{2\le n\le m}\frac{b(n)}{\sqrt n}Q_{ik}(\log n).
\]
The last endpoint is zero exactly. The tail is explicitly
\[
 \int_L^\infty j_D(s)\,ds
 =\operatorname{artanh}(e^{-L/2})-\arctan(e^{-L/2}).
\]
Equivalently \(K_D=A_D-c_D^*I-B_D\), where \(A_D\) denotes the entire positive jump integral including its tail. There is no pole matrix. The integrand at zero is interpreted after cancellation \(2\delta-Q\), never by separating divergent pieces.

## Complex zeros and the capacity/coercivity distinction

The unconditional zero-side pairing is
\[
 \mathcal K_D(f,g)=\sum_{\Lambda_D(\rho)=0}
 \overline{\widehat f(\overline{z_\rho})}\widehat g(z_\rho),
 \qquad z_\rho=i(\rho-1/2),
\]
with multiplicity. For real even carriers this is the bilinear analytic continuation \(\sum_\rho \widehat f(z_\rho)\widehat g(z_\rho)\), not a sum of absolute squares off the line. The zeros with \(\Re\rho>1\), and their reflected partners with \(\Re\rho<0\), must be included; critical-strip-only contour estimates cannot simply be imported.

For one generic quartet, use the two positive-height spectral nodes \(z=\gamma\pm i\delta\) (the sign convention is immaterial for even transforms). If their evaluation rows are \(v=a+ib\) and \(\bar v=a-ib\), with real rows \(a,b\), then
\[
 G_{\rm quartet,+}=v^*v+\bar v^*\bar v=2(a^Ta+b^Tb),
\]
\[
 K_{\rm quartet}=4(a^Ta-b^Tb),\qquad
 K_{\rm quartet}-2G_{\rm quartet,+}=-8b^Tb.
\]
These factors assume the positive-height table contains **both** reflected zeros. A table with one representative needs the corresponding explicit orbit weights. Multiplicity multiplies these contributions. On-line \(\pm\gamma\) pairs instead give \(2v^Tv\). Hence the old inference of complement coercivity from \(2\sigma_{\min}(E)^2\) fails structurally in this fake world; a small zero gap does not repair the sign.

For real carrier coefficients, quietness at a generic off-line node requires both real equations \(a u=0\), \(b u=0\). Rows \(\sqrt2a,\sqrt2b\) preserve the positive-height Gram above; duplicated conjugate/reflected constraints add no new real rank. On-line nodes give one real equation. Axis degeneracies must use actual real rank. Replacing an off-line zero by its real height loses the imaginary evaluation constraint. This review makes no conditioning, residual, or coercivity claim from interpolation alone.
