# Exact hyperbolic source ladder: what its differential equation does and does not pay

STATUS: ANALYTIC_PAPER_CANDIDATE; exact review recorded separately.
Base: 0a0483582d37a6ba8d5cb2f836ecae63d0ecd6c7.
This is an isolated source calculation for the active full-V objective. It is not canonical admission, a proof of V, or a new RH claim.

## Return point and source lock

The previous curvature proof uses only the minimum Gamma rate. The present calculation tests an identity that DOES use the complete square-rate product. The earlier self-decomposable/OU construction is not new: DENSITY DN11-DN21 already gives the stationary law and a positive auxiliary energy without a transfer to V. Merely supplying that auxiliary energy again is excluded.

The fixed source is r_2, the density of T_2=sum_(n>=1) Gamma(2,1)/(pi*n^2), with Phi(x)=exp(5x/2)r_2(exp(2x)), Phi even, f=Phi/||Phi||_2. The full target is

V[c]=2 Re integral_0^infinity conjugate(P_c(X)) Q_c(X) dX,
P_c=sum c_i f(X+x_i), Q_c=sum c_i(X+x_i)f(X+x_i),

for every finite family x_i in I=(-log(2)/2,0) and complex c_i. Neither a moment identity nor an energy identity for the single function Phi establishes this target.

Inputs actually used: REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md G1 and G8; REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md sections 1-4; ADVICE_2026-09-12_DENSITYSD.md I1-I3; REPORT_2026-09-15_SOURCE_ROUTE_COMPARISON.md R1-R3. The external Pitman-Yor paper was listed by the old observer but its body was not then read; external attribution is separate from the direct derivation below.

## L1. A full positive source family, not a finite-mode approximation

For every alpha>0 let T_alpha=sum_(n>=1) Gamma(alpha,1)/(pi*n^2), with independent terms. The positive series is finite almost surely because its expectation is alpha*pi/6. Its Laplace transform is

L_alpha(s)=[sqrt(pi*s)/sinh(sqrt(pi*s))]^alpha, s>=0.

This follows from the Gamma product and the elementary sinh product. Independent addition gives T_(alpha+beta) equal in law to T_alpha+T_beta. Thus r_4=r_2*r_2 exactly, with the entire full source retained in both copies.

Every positive moment is finite: E exp(theta*T_alpha)<infinity for theta<pi, by convergence of the product and sum n^(-2). Every negative moment is finite as well. For k>0,

E T_alpha^(-k) = Gamma(k)^(-1) integral_0^infinity s^(k-1)L_alpha(s) ds < infinity,

by Tonelli; at infinity L_alpha is O(s^(alpha/2)exp(-alpha*sqrt(pi*s))). The function m_alpha(p)=E exp(p log T_alpha) is therefore entire in p. On each compact p-set, powers of |log T_alpha| are dominated using slightly larger positive and negative moments. No zero-location hypothesis is used.

## L2. Exact recurrence, with all terms present

Set w=sqrt(pi*s) and F_alpha(w)=(w/sinh w)^alpha. Direct logarithmic differentiation gives

w^2 F_alpha''-2alpha*w F_alpha'+alpha(alpha+1)F_alpha-alpha^2*w^2 F_alpha
 = alpha(alpha+1) F_(alpha+2).

Equivalently,

4s^2 L_alpha''+(2-4alpha)s L_alpha'+alpha(alpha+1)L_alpha-alpha^2*pi*s L_alpha
 = alpha(alpha+1)L_(alpha+2).                                      (L2)

For Re p<0, multiply by s^(-p-1) and integrate. The zero endpoint terms vanish because L_alpha(0)=1 and its first derivatives are finite; the infinity endpoint terms vanish by the full exponential-in-sqrt(s) bound, also for its derivatives. Twice integrating by parts and using

integral s^(-p-1)L_alpha(s)ds=Gamma(-p)m_alpha(p)

gives

alpha(alpha+1)m_(alpha+2)(p)
 = (2p-alpha)(2p-alpha-1)m_alpha(p)
   + alpha^2*pi*p*m_alpha(p-1).                                  (L3)

Both sides are entire in p, so (L3) holds throughout C. At alpha=2, the fixed-source Mellin identity is m_2(p)=2xi(2p), hence

6m_4(p)=(2p-2)(2p-3)m_2(p)+4pi*p*m_2(p-1).                     (L4)

The moments in (L3) are strictly positive at real p. This does not give their sign or nonvanishing at complex p. In particular dropping m_4, treating it as a nonnegative complex forcing, or dividing by an unproved nonzero m_2 would invalidate a zero argument.

## L3. The source differential equation retains a strictly positive forcing

For alpha=2 inverse Laplace transformation of (L2) yields

6r_4(t)=4t^2 r_2''(t)+(22t-4pi)r_2'(t)+20r_2(t), t>0.          (L5)

There are no zero-endpoint delta terms: r_2 and its derivatives vanish at zero by the already established reciprocal full-theta tail. All terms have exponential decay at infinity; Laplace uniqueness proves the identity. Here r_4=r_2*r_2 is strictly positive on t>0.

Put Phi_4(x)=exp(5x/2)r_4(exp(2x)); its exponent is deliberately the SAME 5/2 as for Phi, not a new normalization or an asserted reciprocity for r_4. Then

6Phi_4=Phi''+(4-2pi*exp(-2x))Phi'
             +(15/4+5pi*exp(-2x))Phi.                         (L6)

Define H_4(x)=(Phi_4(x)+Phi_4(-x))/2>0. Using only evenness of the original Phi and averaging (L6) at x and -x gives

6H_4=Phi''+2pi*sinh(2x)Phi'+(15/4+5pi*cosh(2x))Phi.             (L7)

This is an inhomogeneous identity; H_4 is an actual full convolution of r_2, not a free error term. No homogeneous eigenvalue equation has been proved by writing (L7).

## L4. The direct self-adjoint reading is not a positive energy

The usual real gauge is Psi(x)=exp[(pi/2)cosh(2x)]Phi(x). Equation (L7) becomes

[-d^2/dx^2 + pi^2*sinh(2x)^2 - 3pi*cosh(2x) - 15/4]Psi(x)
 = -6 exp[(pi/2)cosh(2x)]H_4(x).                              (L8)

This identity alone refutes nonnegativity of this particular gauged quadratic energy. Indeed Psi is positive and even, Psi'(0)=0, and the full theta tail Phi(x)=O(exp(9x/2-pi*exp(2x))) at +infinity, with its differentiated versions, implies that Psi, Psi', and the potential-weighted integrands decay superexponentially. The right side has the same integrability by (L8). Integration on [0,infinity), retaining both endpoints, gives

integral_0^infinity [|Psi'|^2+(pi^2*sinh(2x)^2-3pi*cosh(2x)-15/4)|Psi|^2] dx
 = -6 integral_0^infinity Psi exp[(pi/2)cosh(2x)]H_4 dx < 0.     (L9)

At 0 the boundary product is zero because Psi'(0)=0; at infinity it vanishes by the stated tails. This is a negative test function for this explicit auxiliary differential form, with its Neumann endpoint. It is NOT a negative V witness and does not exclude other fields, other boundary conditions, or a coupled positive ladder. A positive-potential Sturm argument cannot simply discard the forcing in (L8).

## L5. Actual finite-row transport before seeking a coupled mechanism

To display the price of extending a single-source ODE to arbitrary rows, use unnormalized columns and set

P(X)=sum c_i Phi(X+x_i),
P_-(X)=sum c_i exp(-2x_i)Phi(X+x_i),
P_4(X)=sum c_i Phi_4(X+x_i).

For EVERY finite list and complex coefficients, (L6) gives exactly

6P_4=P''+4P'+(15/4)P
       -2pi*exp(-2X)P_-' +5pi*exp(-2X)P_-.                    (L10)

For these rows the boundary at X=0 is generally nonzero, and P_4 is not pointwise positive for arbitrary complex coefficients. No term can be removed using the positivity of r_4 alone. The target is still

||Phi||_2^2 V[c]=2 Re integral_0^infinity conjugate(P(X))
                           sum c_i(X+x_i)Phi(X+x_i) dX.

Thus a proposed coupled use of the recurrence must account for P_4, the changed coefficients in P_-, the full X=0 traces, and this exact mixed target. A single-source Sturm identity supplies none of those transfers automatically.

## L6. A constant-coefficient coupled field and its exact target flux

There is a useful further simplification that retains ALL rows. For alpha=2n, n>=1, define r_alpha=r_2 convolved with itself n times, Phi_alpha(x)=exp(5x/2)r_alpha(exp(2x)), and for real k set

U_(alpha,k)(X)=sum_i c_i exp[-2k(X+x_i)]Phi_alpha(X+x_i).

The same inverse-Laplace computation as L5, now for alpha=2n, gives

alpha(alpha+1)Phi_(alpha+2)
 = [D^2+2alpha D+alpha^2-1/4]Phi_alpha
   -(alpha^2*pi/2)exp(-2x)(D-5/2)Phi_alpha.

The finite convolution powers have smooth flat zero endpoints, and exponentially decreasing derivatives at infinity, so the Laplace operations introduce no boundary distributions. Conjugating every column by exp(-2k(X+x_i)) now absorbs the coefficient change in L10 into the k+1 field. Consequently

alpha(alpha+1)U_(alpha+2,k)
 = [(partial_X+alpha+2k)^2-1/4]U_(alpha,k)
   -(alpha^2*pi/2)(partial_X+2k-1/2)U_(alpha,k+1).              (L11)

The coefficients are independent of X and of the node list. This is an exact equation of the whole coupled field, not a positivity theorem for that field.

For the alpha=2 row let E_c(k)=integral_0^infinity |U_(2,k)(X)|^2 dX. It and its k derivative are finite locally uniformly for real k: the original full theta tail controls arbitrary exponential and linear X weights on this half-line for every fixed finite row. Direct differentiation gives the exact boundary-in-parameter identity

||Phi||_2^2 V[c] = - E_c'(0)/2.                              (L12)

Indeed partial_k U_(2,k) at k=0 is -2 sum c_i(X+x_i)Phi(X+x_i); this proves L12 with the complex conjugation and the factor 2 intact. All physical traces U_(alpha,k)(0) remain those of the actual row, and are not generally zero.

Two safeguards distinguish this from a paid compensation law. First, the derivative sign in L12 is still the target, not a proved monotonicity fact. Second, even a ONE-node negative shift x in I gives

E_x(k)=integral_x^infinity exp(-4k u)Phi(u)^2 du
      ~ Phi(x)^2 exp(-4k x)/(4k), k->+infinity.              (L13)

For L13 put v=4k(u-x); boundedness of Phi and dominated convergence against exp(-v) apply. Thus raw E_x(k) diverges, although E_x'(0)<0 by evenness of Phi. Global monotone decay of this raw energy in k, or finiteness of its unweighted accumulated integral over k>=0, is FALSE and cannot be the sought budget. A valid coupled argument would have to justify its actual weights and boundary terms independently. No such choice is supplied by L11 alone.

## L7. A source-specific renewal law with an explicit finite scalar budget

The primary paper supplies more than the previously known deterministic thinning. Pitman-Yor Proposition 12(iv), equations (121)-(122), printed pp.318-319, gives the following law after the exact scaling T=(pi/2)S_2. Let T^* be the size-biased T, with density t r_2(t)/mu, mu=E T=pi/3. Let H have probability density h^(-1/2)-1 on 0<h<1. With T, H and the copy of T^* on the right independent,

T^* =_law T + H T^*.                                         (L14)

This size-biased identity is not the ordinary OU identity for T itself. For q>-1/2, direct integration gives

E H^q=1/[(2q+1)(q+1)], hence E H=1/6 and E H^2=1/15.           (L15)

It gives a full, constructive, positive renewal expansion. Take independent copies H_j, T_j, set W_0=1, W_j=product_(l=1)^j H_l, and define

S_m=sum_(j=1)^m W_(j-1)T_j, S_infinity=sum_(j>=1) W_(j-1)T_j.

The series is finite almost surely and in L1 since E S_infinity=mu/(1-1/6). Iterating L14 shows S_m+W_m Z_m has law T^*, with Z_m an independent copy of T^*. The terminal remainder tends to zero in L1, because E W_m Z_m=6^(-m)E T^*. Thus S_infinity has law T^*. In this series coupling,

R_m=S_infinity-S_m=W_m Z_(tail,m),

where Z_(tail,m) is independent of the first m H-variables and has law T^*. Consequently

E R_m^2=15^(-m) E (T^*)^2.                                  (L16)

The Gamma cumulants give kappa_1(T)=pi/3, kappa_2(T)=pi^2/45 and kappa_3(T)=4pi^3/945. Thus E T^3=4pi^3/63 and

E (T^*)^2=E T^3/E T=4pi^2/21,
sum_(m>=0) E R_m^2=10pi^2/49.                                (L17)

This is a finite source-derived budget controlling ALL levels of this scalar renewal remainder, without postulating convergence of that remainder. No generic constant has been added to V.

The exact limitation matters: R_m is the renewal remainder of the size-biased positive source variable. It has not been identified with E_loss, with the full conditional covariance, or with a field whose boundary flux is V. For a globally L-Lipschitz observable F the same coupling gives E|F(S_infinity)-F(S_m)|^2 <= L^2(4pi^2/21)15^(-m). But the actual translated likelihood

F_x(t)=a^(5/4)r_2(at)/r_2(t), a=exp(2x)<1,

has large-t behavior a^(9/4)exp(pi(1-a)t)(1+o(1)), and is not globally Lipschitz. Nor is the physical measure the unweighted size-biased law: the original conditional decomposition uses a quarter-power tilt of two h variables, the outer theta weight, the X>=0 cutoff and a mixed x_i term. All these differences must be paid in a transfer; applying L17 as the V budget without them is invalid. This statement does not exclude weighted moment estimates or a corrected exact map.

## L8. Exact return of the renewal carrier to the physical measure

The mismatch of measures in L7 can be made explicit without guessing a transfer. Let p_t(s)=t h(ts)h(t(1-s))/r_2(t), 0<s<1, be the original conditional fraction density; here h is the density of the shape-one full source, not the variable H of L14. Put A=||Phi||_2 and

W(t)=1_(t>=1) mu t^(1/2)r_2(t)/(2A^2).

Using the size-biased density r^*(t)=t r_2(t)/mu, the complete physical two-energy measure is EXACTLY

d eta(t,s)=W(t) r^*(t) p_t(s) dt ds
          =1_(t>=1) t^(3/2)r_2(t)^2 p_t(s)dt ds/(2A^2).       (L18)

This is the original w dmu after t=exp(2X), including the cutoff. In particular W is nonnegative and bounded: r_2 is continuous on [1,infinity), and its full exponential tail controls t^(1/2)r_2(t). Let W_max=sup W<infinity, defined independently of the target sign.

The unchanged likelihoods are

g_x(t,s)=a^(9/4) h(ats)h(at(1-s))/(h(ts)h(t(1-s))),
E_(p_t)g_x=a^(5/4)r_2(at)/r_2(t), a=exp(2x).

Thus the full target can be written with the size-biased carrier, conditional expectation C at fixed t, G=sum c_i g_(x_i), B=sum c_i x_i g_(x_i), and X=log(t)/2:

V[c]=2 Re integral conjugate(CG) C(XG+B) d eta.               (L19)

This is the very same form and covariance decomposition, not a different marginal norm. On the coupling of L16, the scalar weighted renewal tail consequently obeys

sum_(m>=0) E[W(S_infinity) R_m^2]
 <= W_max * 10pi^2/49.                                      (L20)

No independence of W(S_infinity) and R_m is needed. This pays the scalar carrier budget even in the physical outer weight. It DOES NOT bound the changes of the actual g_x, the moving conditional law p_t, or their mixed x_i term. Those are the remaining mathematical transfer, and a valid proof must account for the t=1 boundary rather than replacing W by its supremum inside an identity.

## Primary-source reconciliation

Pitman and Yor, Infinitely Divisible Laws Associated with Hyperbolic Functions, Canadian Journal of Mathematics 55(2) (2003), 292-330, DOI 10.4153/CJM-2003-014-x.
Publisher PDF: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D91B384C84FA02C55A332B396BB85385/S0008414X00033484a.pdf/infinitely_divisible_laws_associated_with_hyperbolic_functions.pdf
PDF SHA256: 302f232c65a647b3e8a69bddb18163d12157b0d2b26e499e4c47fdde50ab957b.

Theorem 1(ii), Eq.(24), printed p.298 is precisely L3 after scaling T_alpha=(pi/2)S_alpha. Source quote: "the recurrence continues to hold". Eq.(42), p.301 is the alpha=2 xi combination. These are published identities, not a claimed novel recurrence. Proposition 12(iv), Eqs.(121)-(122), supplies L14; L15-L17 are the elementary full-tail budget derived here from it. Proposition 12(iii),(v) also characterizes the scalar Laplace transform by nonlinear equations; it does not supply a homogeneous spectral eigenproblem or a complex Mellin zero theorem. The exact-scale source card and local text extraction are retained in the evidence directory. No full paper or PDF is republished in the repository.

The negative Gaussian deformation from the original conditional report does not automatically satisfy L14 with its own full source as innovation and this specific H law: Proposition 12 characterizes the original law at its fixed mean. This excludes treating the law as a generic covariance identity, but does not prove its sufficiency for V.

## Decision and exact scope

The full square-rate product supplies the exact ladder L2-L11 and the full-row target flux L12. This differs from the minimum-rate curvature estimate and from merely renaming the old OU law. It does not presently supply a sign-producing transfer to V. The simplest scalar self-adjoint use has the explicit negative energy L9, and raw monotone-in-k dissipation fails by L13, so these stronger shortcuts are rejected before requesting nonexistent positive scalar or raw monotonicity theorems.

The next concrete compensation question is whether the source-specific renewal law L14-L17 can be carried through the original conditional likelihoods and physical weight to control the WHOLE mixed target, with an exact map and all boundaries. L17 is a genuine source-level reservoir with known decay; it has not paid the target energy. The coupled identity L11-L12 is available as an exact field constraint, not a required extra route or a substitute for that transfer. A successful result must give one global budget, not one unpaid positivity assertion per added level, and cannot assume finiteness of the energy it is meant to control. No such target transfer is established here.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The square-rate differential equation has a nonzero full-convolution forcing, and its direct scalar gauge has the negative auxiliary energy L9 rather than the target V.
