# MB34: finite short-Mobius expansion and unpaid joint sector

2026-10-09. Own bounded attempt after Q5, baseline8908903d.
Independent read-only q05_moment_audit E1-E3 conditional PASS.
RH/SP/MB34 OPEN; Q6 not sent.

The obstruction is the joint energy of the original Mobius polynomial,
not an algebraic remainder that must vanish. Test whether an exact finite
expansion exposes plain factors to which conditional source P applies.
Consumer: Q5 RF29 and original Q1 MB34, same Omega-lambda comparison,
fixed arithmetic data, all masks and common smooth profile W.

## E1. Exact identity on ideals

All convolutions below are on good integral ideals outside fixed S.
Let 1 be the constant arithmetic function, delta the convolution unit,
X=U^(3/32), A(n)=mu(n) 1_(qn<=X) (POINTWISE truncation), B=delta-A*1.
Then B(n)=0 for qn<=X. By multiplicativity of the norm,
mu*B^(*13) is supported on qn>X^13, including the strict endpoint.
The binomial theorem and mu*1=delta give the global exact identity

 mu = sum_(j=1..13) (-1)^(j-1) binom(13,j) A^(*j)*1^(*(j-1))
      +mu*B^(*13).                                             E1

No convergence argument is used. At qn<=X^13 the last term is zero.
For the actual upper band D U^(-1/100)<=L<=D, D=U^r,
28/25<=r<=113/100, and fixed support [alpha,beta] with alpha>0,
beta L<=X^13 eventually: 39/32-113/100=71/800>0.
Also alpha L>X eventually, so the j=1 term vanishes on the window.
The old Q03 audit extract(5) is the two-step predecessor with a retained
long remainder; this is its finite support extension, not new convolution algebra.

## E2. Exact actual polynomial and masks

For psi_v=nu chi_v in the pointwise sense, including zero extensions,
let M_v=L^(-1/2) sum_n mu(n) psi_v(n) W(qn/L).
Equation E1 replaces M_v by sum_(j=2..13) c_j F_j,v, where

 F_j,v=L^(-1/2) sum_(a1...aj b1...b(j-1)=n; qai<=X)
          mu(a1)...mu(aj) psi_v(n) W(qn/L),
 c_j=(-1)^(j-1) binom(13,j).                         E2

Keep each original fixed coprimality mask on the whole product n.
Repeated prime factors across factors are allowed; their cancellations
across j reconstruct mu. Do not impose pairwise coprimality or squarefree n
inside an individual F_j. The original sparse row v=u a^6, multiplicity,
units and every character zero remain. No new row mask is introduced.
The same identity holds for each common derivative profile; X depends on U,
not on L. Positive-energy Sobolev is applied only after uniform estimates.

## E3. Why freezing all but one plain factor gives no gain

Conditional on P on the same nonprincipal R0 rows, freeze the product d
of all but one plain factor. The remaining polynomial is the source plain
S_v(L/qd), with coefficient psi_v(d)/sqrt(qd). Fixed masks stay fixed
within this application. Late Omega support in R0 is the existing MF35
premise, not a newly proved uniform Hecke assertion.
On nonempty support qd<=beta L, hence L/qd>=1/beta. Scales below1
are bounded and handled by counting, not by a negative-length use of P.
Source locator: pinned paper.tex12531-12586, no-slot case z=0;
same source SHA256 as MF38_SHORT_PLAIN_TRANSFER.md.

For j=2, the outer inverse-square-root coefficient mass is O(X*U^eps).
Minkowski in l4 therefore gives sum_(R0)|F_2|^4 <=H X^4*loss.
Using Omega<=O(1), sum Omega<=O(PU)=O(H/P^5), Cauchy gives

 sum Omega |F_2|² <=H P^(-5/2) X²*loss
                   =H U^(3/16-5p/2)*loss.                       E3

Here p=(r(1+1/10000)-1)/6. The displayed exponent is positive throughout
the band: even at maximal p it equals106629/800000>0.
For j>=3, if D=a1...aj, the remaining frozen j-2 plain factors have
inverse-square-root mass O(sqrt(L/qD) log(2L)^(j-3)). Summing the short
factors then costs sqrt(L) times logarithms, since sum_(qa<=X)1/qa=O(log X).
Thus the analogous fourth moment budget is H L²*loss and energy budget
H P^(-5/2) L*loss. These are insufficient UPPER bounds, not lower bounds
or counterexamples to small actual F_j or M. Finite binomial constants
do not alter exponents. Plain P alone does not estimate the joint sector.

## E4. Retaining two plain factors still has an unpaid coefficient cost

Read-only mobius_short_transfer and root independently checked this extension,
conditional on the same P and its profile uniformity. Fix the ORIGINAL
amplifier a0<=P first: psi_(u a0^6)(b)=psi_u(b)1_((b,a0)=1).
The same mask applies to both remaining plain factors, with no (u,a0)=1
restriction. Dyadic separation of the two factor norms and Mellin inversion
of W(qD qb1 qb2/L) express their sum as products of plain polynomials.
Their common Mellin height is integrated against rapidly decaying transform
coefficients; source polynomial height losses are absorbed by finitely many
fixed W seminorms. Nonempty blocks have qD B1 B2 comparable to L,
so normalization is qD^(-1/2) up to bounded block ratios.

For j=3, summing three short factors has coefficient mass O(X^(3/2)).
P in l2 on base rows u~U, followed by the a0 sum, therefore yields
E_3<=PU X^3*loss=H U^(9/32-5p)*loss. The exponent remains positive.
For j>=4, freeze j-3 plain factors with product C. Their coefficient
mass is O(sqrt(L/qD) log(2L)^(j-4)); summing the short factors gives
sqrt(L) times logarithms, hence E_j<=PU L*loss. Again insufficient.
For j=2 the one remaining plain factor similarly gives PU X²*loss.
These fixed-a0 estimates improve the coarse E3 entrance but do not supply
the desired gain. Using all v<=H instead would not justify the PU base
cost. All are upper budgets, with cross-j cancellation still unestimated.

## Bounded alias return and next test

Three shelf dictionaries: dispersion/bilinear multiplicative characters;
power-residue large sieve/asymptotic off-diagonal; sparse sixth-power
amplifier/inverse Hecke moment. All returned INCOMPLETE (freshness), not absence.
Source-checked partial analogue: Bettin-Chandee, arXiv:1502.00769v1,
https://arxiv.org/abs/1502.00769v1, Theorem1, TeX196-206 and proof outline321.
PDF SHA256439665281e775e8369e222c959f2cad0221aa57dc7d1338efdae1c99029d7f20;
TeX SHA2566df1439b3e777a73d62134b432490b55bb6210cdfecc280fd6c07d09803c039e.
Quote (TeX321): “We then use Weil's bound when $\Delta\neq0$ and a trivial estimation when $\Delta=0$.”
The decisive mechanism
is complementary-divisor switching plus reciprocity, retaining selected
variables jointly under Cauchy, then separating zero/nonzero Delta.
The theorem acts on rational-integer additive inverse phases
e(theta*a*inverse(m)/n), (m,n)=1, with independent coefficient vectors.
RF29 instead has Eisenstein-ideal multiplicative Hecke covariance,
coupled wP(nm), shared primes, all zeros and the Omega-lambda subtraction.
No exact phase/domain map is established. Arbitrary coefficients in that
theorem do not remove these missing hypotheses. Classification: excluded
as a supplier, retained as a partial proof mechanism. Negative control:
arbitrary positive scalar kernels need not give positive convolution (Q5);
neither E1 nor this source supplies such positivity.

Decision: E1 removes the long coefficient without an algebraic remainder,
but triangle after freezing loses the desired cancellation. Next bounded
question must estimate the original joint MB34 or the exact E2 sum jointly,
including cross-j terms, and pay the original inverse return. Stop this
entrance if only E3 or another absolute coefficient budget is obtained.
No full gain, new zero-free boundary, or certification of source P/M/R.
