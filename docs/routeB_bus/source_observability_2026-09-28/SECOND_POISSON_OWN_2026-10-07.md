# Own bounded attempt: second centered-flux Poisson input

PAPER own algebra, independently checked once by causal_algebra_audit. Same source, no bound or sign claimed.
For a>U, alpha_U(a)=-sum_(h<=U,h|a)mu(h), so as locally finite measures
 d rho_U(a)=-sum_(h<=U)mu(h)[sum_(j>=1)delta_(hj)(da)-da/h].
This is exact including the continuous plus A_U da. For finite nondegenerate
I subset(U,A0), F piecewise C1 with specified one-sided traces, the period-h
Fejer formula gives
 int_I F d rho_U
 =-lim_(H->infty)sum_(h<=U)mu(h)/h sum_(0<|ell|<=H)
   (1-|ell|/(H+1)) int_I F(a)exp(2pi i ell a/h)da
   -sum_(h<=U)mu(h) C_(I,h)[F].
C_(I,h) is +/-half F at each included/excluded endpoint in h*N; internal
jumps need their actual midpoint correction if F has specified values there.
Singletons are separate. Thus the second transform carries a minus sign,
an interior factor1/h, but NO1/h in its endpoint correction.
Fixed-cell passage under a finite first-alias sum follows from finite h and
bounded compact piecewise amplitudes. No uniform double-tail interchange is
asserted; the first Q_K boundary function has jumps, so it must be partitioned
at all of them or transformed with its jump corrections explicitly.

For a first-alias interior term with d,k fixed, the transformed domain is
 D={U<a<A0, u>=1, du>U, Y0<=adu<=y, u<=V or u>V},
with all strict/inclusive traces retained. The phase is
 phi(a,u)=pi k u+2pi ell a/h-t log(adu).
For t>0 simultaneous stationarity requires k>0,ell>0 and
 u*=t/(pi k), a*=th/(2pi ell), x*=t²dh/(2pi²kell).
The original cutoff conditions, not merely this formal saddle, decide whether
it is admitted. The saddle phase is exactly
 t[2-log(t²/(2pi²))+log(kell/(dh))].
Thus equality of product ratios kell/(dh) makes the leading phases coherent.
The clipped two-dimensional domain is hyperbolic, so it is not legitimate
to multiply two independent full Fresnel integrals across its boundaries.

If, only for deriving the formal interior leading amplitude, the saddle is
strictly inside a rectangle whose clipped corrections are kept separately,
the two normal-form factors are1/sqrt(pi k) and sqrt(h/(2pi ell)).
Together with -(-1)^k mu(h)mu(d)d^(-s)/(2h), the leading coefficient is
 -(-1)^k mu(h)mu(d)/(2sqrt(2)pi sqrt(h d k ell)),
multiplied by the short logu* or long -logd and the clipped normal-form factor.
This is only a phase/amplitude bookkeeping identity, not a uniform asymptotic
on the hyperbolic domain. The baseline -2, Theta and first-boundary terms
must still enter the same operation; no source cancellation follows from
this isolated leading coefficient.

Own outcome: centered second transform is available with exact minus sign
and endpoint weights. The unresolved step is the complete product-ratio
coefficient AND moving-boundary aggregate, before taking norms. No prime-pair
conjecture, reciprocal zeta replacement, normJ estimate or Schur sign used.
