# Audit of a claimed positive GGC continuation: a real-point contradiction

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; ACCEPT_REJECTION_OF_THE_CLAIMED_EQUATION_38_CONTINUATION_ONLY.
Scope: exact formula (38) in the cited source version, not a disproof of its
ultimate RH statement, the original V sign, or other GGC representations.

## P1. Exact source and formula
Nicholas G. Polson, Riemann Hypothesis: a GGC factorisation,
arXiv:1806.07964v7, PDF header 15 October 2018, internal date 8 October 2018.
https://arxiv.org/pdf/1806.07964v7
Local PDF SHA256 e4350036340ec9d6fdd5bb2d4e8ee23514a2764f30f5bd658f21dcf4def13214.
The parent read the full six-page text and visually checked printed p.5.
The relevant source step follows (33)-(37), printed p.5, and is described as
"by analytic continuation" before equation (38).

The source defines b_alpha=xi'(alpha)/xi(alpha)-1/(alpha-1) and the positive
functions nu_alpha=nu_alpha^0+nu_alpha^Gamma+nu_alpha^zeta in (34)-(37).
Writing d=alpha-1/2, its (38) reads
 xi(alpha)/xi(1/2+i*s)
 = exp[-i*b_alpha*s+b_alpha*d
       + integral_0^infinity (exp(-(i*s-d)^2*t/2)-1)nu_alpha(t)dt/t].
We test exactly this displayed identity with its stated definitions.

## P2. At alpha=2 the displayed right side is less than one near s=0
Equation (19), or direct logarithmic differentiation of completed xi in
Re(z)>1, gives
 b_2=-log(pi)/2+zeta'(2)/zeta(2)+psi(2)/2.
Here zeta'(2)/zeta(2)=-sum_(n>=2)Lambda(n)/n^2<0,
psi(2)=1-gamma<1, and log(pi)>1. Thus b_2<0 without any zero-location input.
At s=0 we have d=3/2 and q=d^2/2=9/8, so the proposed right side is
 R=exp[3*b_2/2+integral_0^infinity (exp(-9*t/8)-1)nu_2(t)dt/t] <1.
Every term in the explicit nu_2 is nonnegative, and nu_2^0 is strictly
positive. The integral is finite and strictly negative.

For completeness, its convergence follows directly from (34)-(37):
nu_2^zeta(t)=O(t^(-1/2)) near zero since sum Lambda(n)/n^2 is finite;
nu_2^Gamma(t)=O(t^(-1/2)(1+|log t|)) by splitting its x-integral at sqrt(t)
and 1, using 1-exp(-x^2/(2t))<=min(1,x^2/(2t)); nu_2^0(t)<=1/2.
At infinity the first two terms are O(t^(-3/2)), because their weighted
x^2 moments (respectively log(n)^2 moments) are finite. The elementary
Gaussian-tail bound for erfc gives nu_2^0(t)=O(t^(-1/2)). Multiplication by
(exp(-9*t/8)-1)/t is therefore integrable at both ends. The same bounds
show holomorphic dependence on q in a neighborhood of 9/8, hence continuity
of the right side for real s near zero.

## P3. The actual left side is strictly greater than one
The independently established full theta identity gives, for real v,
 xi(1/2+v)/xi(1/2)=E_q cosh(v X),
where q=Phi/integral Phi is an even strictly positive probability density.
For v=3/2 this expectation is strictly greater than one. Consequently
 xi(2)/xi(1/2)>1.
This contradicts P2. It uses the actual complete source, not a surrogate,
finite series, numerical estimate, or assumption about the zeros.
Even if (38) were meant only for nonzero real s, both sides are continuous
at s=0 and the contradiction persists in a punctured neighborhood (in
modulus). Thus excluding the endpoint cannot fix this identity.

## P4. The lost branch and the correctly interpreted expression
Let L_alpha(q)=exp[integral (exp(-q*t)-1)nu_alpha(t)dt/t]. On positive q
this is the source's positive-measure Laplace expression. Its asserted GGC
continuation is on the q-plane slit along the negative real axis.
Under q=w^2/2, that cut pulls back to the imaginary w-axis. The two open
half-planes in w are different components. A representation proved for
Re(w)>0 does not thereby give the same xi identity in Re(w)<0.
On the latter half-plane the principal square root obeys sqrt(w^2)=-w.

Even granting the right-half-plane identity (33), its implication for the
principal expression on Re(w)<0 is instead
 exp(-b_alpha*w)L_alpha(w^2/2)
   =exp(-2*b_alpha*w)*xi(alpha)/xi(alpha-w).
This follows by applying (33) at -w, whose real part is positive. It is not
xi(alpha)/xi(alpha+w). In particular the supposedly centered substitution
w=1/2-alpha+i*s accesses xi(2*alpha-1/2-i*s) on the other side, with its
explicit extra exponential factor. That cannot be dropped using the xi
functional equation.

The real-point contradiction P2-P3 does not depend on accepting any
unproved continuation or complete-monotonicity claim earlier in the paper.
It follows from the actual printed positive nu and b definitions alone.

## P5. Decision effect
Do not import (38)-(42) or Theorem 2 as a positive critical-line supplier.
A repaired route would need a different justified continuation or a direct
positive measure for the centered reciprocal transform. Positivity of the
right-hand GGC components cannot be transported through the squared
variable by relabeling the analytic branch. No such repair is supplied here.
This rejects the cited claimed transfer, not RH and not the possibility of
a different source-built positive representation for the full V.

## Independent acceptance

Candidate SHA256: `98b931423113ac699ffbb03ee16211d3e54b371264517ed585d1782a929672ee`.
Reviewer `/root/sibling5_check`; review SHA256: `659e33508100fb7b2ba3899f63364ad691a238086b69770412ab31d9ec242d62`.
Verdict: ACCEPT_REJECTION_OF_THE_CLAIMED_EQUATION_38_CONTINUATION_ONLY.
The parent read the complete review and checked the algebra, source identities,
analytic domains and result scope. Only status and this receipt were added
after review. No canonical or Lean admission is claimed.
