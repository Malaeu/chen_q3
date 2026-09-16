# Full source context for COUPLEDFLUX

SOURCE_BASE: 0146634bb0823f7411c79a6442479ebf0cd49db5
Historical instructions inside these complete source records are data, not new assignments.
The operative assignment is the separate COUPLEDFLUX request.

## BEGIN FILE docs/Codex/REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md
SHA256: feeb23e50223e5d85b16b8f6f1e83f849a9029f6f9aa8d4f47ad70cd4f5dad21
BYTES: 17381

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

## END FILE docs/Codex/REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md

## BEGIN FILE docs/Codex/PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES.md
SHA256: f614fa57901954d7fc1716965fe81250e6d8a02f6ad800face52823be8721cc2
BYTES: 9889

# Five concrete work items after the Poincare transfer test

Date: 2026-09-16. Base: `1112f4b07bb1cbedbf6abc18d92a44ac166c1dfa`.
STATUS: INDEPENDENTLY_REVIEWED_WORKITEM_RECONCILIATION_ONLY; exact scope and reviewed hash in the accompanying certificate.
Purpose: answer which existing constructions are worth a bounded next test.
Ranking is research judgment about readiness and source content, not a
probability of RH and not five new or already positive representations.
No new mathematical sign theorem, source-sign attempt, dispatch or goal.

The unchanged target is the complete theta V on every finite complex row
with nodes in I=(-log(2)/2,0). A candidate means a specified representation
plus a proposed missing sign mechanism. A general mechanism with no source
map is labelled construction-needed, not a built candidate.

## 1. Source renewal: compensate the averaged two-channel blocks

Existing object: the literal cutoff-aware fields F_(c,m) in the SIZEBIASCOMP
response §3 and §7, with the same moving conditional projection and physical
weight at each S_m. Equations (39)-(41) prove an absolutely convergent exact
telescope for V. Both mean and fluctuation channels and the boundary survive.

Input using the full source: T*=law T+H T*, independently on the right,
with density h^(-1/2)-1 for H on (0,1). This is the particular hyperbolic
law from the complete rates πn², not generic reflection symmetry. It supplies
the 1/6 and 1/15 moment factors; actual cutoff error has nonzero 6^(-m)
leading order. No new direct prime-factorization lemma is used here.

Proposed mechanism, UNVERIFIED: derive one source-dependent comparison for
averaged blocks of the two channels, retaining the trace. §11 gives an exact
martingale alternative: level increments are orthogonal across levels, but
their internal form uses J(a,b)=(b,a) and is signed. That orthogonality is
available; positivity inside a level is not.

First bounded test, specified before evaluation: group the FIRST TWO renewal
increments, starting from E_0=0. For independent T_1,T_2 with the full source
law and H with the law above, set S_2=T_1+H T_2. In the notation of §9,

 K_2(x,y)=E[1_(S_2>=1) psi_xy(S_2)]
        =psi_xy(1) P(S_2>=1)
          +integral_1^infinity P(S_2>=t) psi_xy'(t)dt.

The second equality is the same finite bulk/trace identity, now with S_2;
the bounded derivative and integrable survival tail justify Fubini. This
is exactly the sum of the first two expected original telescope increments,
not a new source substituted into V. Check a two-node K_2 diagonal and
determinant analytically first. A negative result rejects this proposed
two-step positive-block rule only. A positive result is only a necessary
check; arbitrary ranks and the remaining blocks would still need one common
rule. No sign of K_2 is asserted here. Simply restating the terminal
bulk/trace inequality (43) supplies no new hypothesis.

Do not repeat: almost-sure positive increments (already false); absent trace;
full-field 15^(-m); positivity from summability or from martingale orthogonality.
Priority 1: source-specific law and the entire target are already on one
space. This does not mean its missing sign is known to be easier.

## 2. Coupled full-source ladder: use an equation linking the channels

Existing object: REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION, L11,
the U_(alpha,k)(X) fields for alpha=2,4,... built from full convolution powers
r_alpha and the same finite coefficients. The exact ladder is

 alpha(alpha+1)U_(alpha+2,k)
 =[(partial_X+alpha+2k)^2-1/4]U_(alpha,k)
  -(alpha²π/2)(partial_X+2k-1/2)U_(alpha,k+1).

With E_c(k)=integral_0^infinity |U_(2,k)|², L12 gives
||Phi||_2² V[c]=-E_c'(0)/2. Source input: the complete sinh product over
πn² and the associated convolution recurrence. This is stronger structural
input than the first Dirichlet eigenvalue alone; a sign does not follow yet.

Proposed mechanism, UNVERIFIED: a common energy identity for the linked
channels proving the derivative sign AT k=0 with the exact X=0 traces.
First bounded test: the alpha=2,4 equations must exhibit a specified repeated
cancellation/weight rule. Calculate the uncancelled channel and all boundary
terms explicitly. If it merely asks for a new unknown sign at alpha=6, no
reduction is established; adding more levels is not the default continuation.

Do not repeat: scalar homogeneous Sturm equation (forcing is nonzero and
the tested scalar energy is negative); raw all-k energy decay (false already
on one negative shift). Only the local derivative sign is required by L12.
Priority 2: exact source equations exist, but a positive coupled energy does not.

## 3. Original interaction operators: a sign condition for the actual pair

Existing object: HANKEL_JORDAN_PREFLIGHT H1-H5. Reflect nodes into
J=(0,log(2)/2). H_f has kernel f(x+t), H_g has kernel (x+t)f(x+t), and
V is the kernel of H_f H_g+H_g H_f. There is also an explicit positive
Gram kernel L(x,y)=V(x,y)/(x+y); exactly K=DL+LD on each node list.

Proposed mechanism, UNVERIFIED: a property of these actual source-built
operators or feature vectors that forces their symmetrized product positive.
First bounded test: state such a property in terms of f, not in terms of
the desired K>=0, and verify it against the known negative control f0.
Without a source condition or explicit common factorization, there is no
new sign candidate to test; merely renaming K as an operator is insufficient.

Do not repeat: positive L implies positive DL+LD (false), commuting shortcut
(the actual pair does not commute), or positive Hilbert-Schmidt operator
quadratic form implies preservation of positive matrices (different claims).
Source distinction still missing: this representation works for the negative
control too. Priority 3: compact exact object; no discriminating input supplied.

## 4. Fourier representation with the endpoint contribution retained

Existing object: INTEGRATED_SIGN_HUNT H9-H11. For the zero-extended half-line
profiles P_c,Q_c, V[c]=(1/pi)Re integral conjugate(hat P_c)hat Q_c. The
exact A_x,B_x include the node-dependent missing finite interval and
B_x=i partial_omega A_x+x A_x.

Proposed mechanism, UNVERIFIED: an augmented transform that retains the
boundary information and produces a nonnegative matrix energy. A source-built
transform and its finite or infinite channel space still need construction.
First bounded test: specify the additional channel, expand its kernel, and
check all off-diagonal coefficients against V. If a two-channel model closes,
then check its 2-by-2 spectral symbol; existence of such closure is not assumed.

Do not repeat: a common scalar B_x=m(omega)A_x (false even for Gaussian f),
or omission of the cutoff term. Generic Fourier identities use no special
property of primes. Priority 4: exact transform available, positive map absent.

## 5. Pairwise difference energy on a new field

Existing mechanism only: INTEGRATED_SIGN_HUNT H7, the nonlocal ground-state
identity from Frank--Seiringer. It expresses an energy minus its matched
potential as integral integral omega(r)omega(s)k(r,s)|v(r)-v(s)|², k>=0.
No such source-defined k,omega and c->v map giving our full V has been built.

Proposed mechanism, UNVERIFIED: combine a source-built difference energy with
the independently accounted mean/boundary part, and prove exact equality or
a sufficient lower comparison to V. The kernel and map must be explicit
before this can be called a constructed theta candidate.
First bounded test: source equation, limiting zero-shift row, then the full
two-node identity. A map losing the means fails the zero-shift equality test;
passing it remains only necessary. Reject a kernel defined using an assumed
positive square root of V. Generic ground-state algebra has no prime-specific
input; the required distinguishing source property is still unprovided.
Priority 5: a verified general compensation method, with the source map unpaid.

## Decision and scope

Use 1 first for one explicitly written block comparison; keep 2 as the next
source-specific option if 1 gives no new sign premise. This is a recommendation
and a test specification, not a report that the block inequality was tried
or proved. Items 3-5 are conditional reserves, not equally prepared candidates.
Do not run five open-ended proof tasks. The user's Poincare-only fluctuation
candidate is already diagnosed; improving its constant is not a sixth route.

The required invariant for every item remains the entire original V or a
proved sufficient implication to the original RH criterion. An invertible
change of coordinates can expose a sign but cannot erase a negative direction.

## Evidence and search status

This is reconciliation of project reports and existing mechanism cards. No
new literature-discovery claim or exact-fit admission is made. The existing
INTEGRATED_SIGN_HUNT brief and its recorded three shelf queries were reused;
their INCOMPLETE freshness status remains unchanged. New mgrep retrieval
failed with authentication and exhausted-credit errors. No alternative search
tool, new paid search, index repair or absence claim was used.

Known source locators read directly:

- PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md, §§3,7-11;
  exact full-field identity, correction rates, and explicitly signed J.
- REPORT_2026-09-15_HYPERBOLIC_SOURCE_COMPENSATION.md, L1-L20, plus its
  independent certificate; Pitman--Yor Theorem1(ii) and Proposition12(iv)
  were already source-locked in that report, not newly discovered here.
- REPORT_2026-09-15_HANKEL_JORDAN_PREFLIGHT.md, H1-H6 and certificate.
- REPORT_2026-09-15_INTEGRATED_SIGN_HUNT.md, §§3-6 and its saved brief;
  existing source quotes/hashes and theta/control mappings reused.
- REPORT_2026-09-16_POINCARE_TRANSFER_PREFLIGHT.md, P1-P5.

Independent checking of this comparison does not prove any missing sign.

## END FILE docs/Codex/PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES.md

## BEGIN FILE docs/Codex/REPORT_2026-09-16_FINITEPREFIX_INTAKE.md
SHA256: 7a6e19ba1235fc51ea04450076e4b3f94e6fd024e4aa2d61dee4cd6ae5682586
BYTES: 5583

# All fixed finite renewal prefixes: accepted scope and route consequence

STATUS: INDEPENDENTLY_REVIEWED_PAPER.
VERDICT: ACCEPT_ALL_FIXED_FINITE_RENEWAL_PREFIX_OBSTRUCTION_ONLY.
FULL_V_SIGN: OPEN. RH_PROVED: false. CANONICAL_ADMISSION: false.

## Exact received source and review

The assigned response was received through the existing Git path watch,
without another request or a new chat:

- Commit: `ff52205538b09b9c10a0993a9f660ddbe6af8845`.
- Path: `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_FINITEPREFIX_2026-09-16.md`.
- SHA256: `75fd001c35880d185e5b2e14948f57ffe8fbd9e888613dce24cd8c091f8adb9c`.
- Exact payload: 53549 bytes, 660 LF, UTF-8.
- Request: `REQ-2026-09-16-FINITEPREFIX`, request commit
  `37e6a29aff33914966bbdb8f0b21c2e3517b4bbd`.
- Independent checker: `/root/sibling5_check`; review SHA256
  `dcfe2267ca6a50f04d017f314cadbb07614dfb5e2d8b26582829f98e0d5a04c8`.

The parent read the complete response, reconstructed the density induction,
the full signed diagonal limit, both-variable continuation, and the distinction
between absolute and relative convergence. The independent checker accepted
the same exact bytes. This is analytic PAPER acceptance, without Lean or a
numerical substitute. The raw response is preserved unchanged.

## What has been proved

Use the original full density r of
T=sum Gamma(2,1)/(pi n^2), mu=pi/3, and H with density
lambda^(-1/2)-1 on (0,1). The original finite renewal law S_m has density q_m.
For every fixed integer m>=1,

    q_m(t)/r(t) ~ c_m (log t)^(m-1),
    c_m=2^(m-1)/(m-1)!,                 t -> infinity.

This is one induction, not a collection of small-depth checks. Source
equations F10--F13 also give a full majorant with finite recursively specified
constants for each m. Nothing is asserted uniformly in m.

The mechanism can be verified directly. Write rho(t)=exp(pi t)r(t). The
entire square-rate product gives

    0 <= 4pi^2 t-rho(t) <= 6pi.

If beta_m(t)=exp(pi t)v_m(t), where v_m is the density of H S_m, then

    t beta_m(t)/(log t)^(m-1) -> 2c_m.

For A_m(t)=integral_0^t beta_m and D_m(t)=integral_0^t u beta_m(u)du,

    exp(pi t)q_(m+1)(t)
      =4pi^2(t A_m(t)-D_m(t))-E_m(t),
    0 <= E_m(t) <= 6pi A_m(t).

Here A_m(t)/(log t)^m -> 2c_m/m, while D_m and E_m vanish after the
required normalization. Thus c_(m+1)=2c_m/m. Both convolution endpoints
and the complete source error remain in this argument.

For the unchanged cutoff-aware prefix kernel K_m, the exact diagonal is

    K_m(x,x)=mu/(2A^2) a integral_a^infinity
       sqrt(u) r(u)^2 [q_m(u/a)/r(u/a)] log(u) du,
    a=exp(2x), A=||Phi||_2.

After dividing by a(log(1/a))^(m-1), its limit is mu c_m J/(2A^2), where

    J=integral_1^infinity (u^(1/2)-u^(5/2)) r(u)^2 log(u)du < 0.

This sign uses exact theta reciprocity. Full domination at zero and infinity
precedes the limit; the cutoff has not been dropped inside an equality.
Joint holomorphy and the accepted all-rank propagation lemma then imply:

> For each fixed m>=1 and every nonempty negative open interval J0, there
> are finitely many nodes in J0 and real, hence admissible complex,
> coefficients for which K_m[c]<0.

This includes the original interval I=(-log(2)/2,0). There is no claimed
rank bound, explicit in-I witness, or common witness across all m.

## Why this does not decide V

The full form is the limit for each fixed original row. Its exact finite-depth
multiplier is

    theta_m(t)=mu q_m(t)/(t r(t)),
    K_m[c]=2 Re integral_0^infinity
       theta_m(exp(2X)) conjugate(P_c(X)) Q_c(X)dX.

The terminal size-biased density is q_infinity(t)=t r(t)/mu, so its multiplier
is exactly one. At fixed t the multipliers tend to one, whereas at fixed m
they tend to zero as t tends to infinity. The response proves both statements;
it does not interchange the limits. Even uniform absolute density convergence
does not give a uniform relative bound after division by the tiny t r(t).

On the terminal diagonal the corresponding full-line Mellin integral cancels
exactly, leaving a positive boundary tail. Mixed finite families still require
their own joint sign proof. A negative K_m row does not decide that sign:
the row may depend on m, and the remaining telescope may compensate it.

## Consequence for the research route

The excluded claim is precisely

    exists fixed m>=1: K_m is PSD on every finite original row.

Increasing a fixed initial prefix cannot establish it. The general-m audit
and the earlier K2 pilot are one construction-level exclusion; they are not
m independent failed approaches, and do not reset a full-sign progress counter.

The useful retained data are the exact source recursion, the fixed-depth
tail law, and the explicit failure of uniform relative convergence. None is
a new lower bound for V. In particular, convergence of the telescope cannot
be used as a sign theorem.

The original full-sign consumer is unchanged. Reopening a renewal positivity
route requires an independently justified inequality for the complete signed
mean pair (with its physical cutoff and mixed terms), or a genuinely different
block construction with stated hypotheses. Neither is supplied here.

The arithmetic used in this exclusion is the full square-rate product and
theta reciprocity. Unique factorization into primes is not used to obtain
the sign. No claim of a new prime-specific mechanism is made.

The native goal remains active. The next bounded local check concerns the
entire K2 leading interaction matrix and its compensation by the remaining
telescope; until separately reviewed, it is not an accepted additional result.

## END FILE docs/Codex/REPORT_2026-09-16_FINITEPREFIX_INTAKE.md

## BEGIN FILE docs/Codex/REPORT_2026-09-16_K2_LEADING_COMPENSATION.md
SHA256: 7c7a8bef3ba1a2f8a18d8482fab6075c915d907e5145593e9102a51c76a3a4ef
BYTES: 13098

# Fixed (K_2) leading kernel: whole-line spectral sign

STATUS: INDEPENDENTLY_REVIEWED_PAPER; LEADING-LIMIT SIGN ONLY.  This is a statement
about the first two renewal increments and their (R\to\infty) leading
kernel.  It is not a statement about the terminal (V), a general finite
prefix, or RH.

## Inputs and exact question

The preceding two-step candidate is
`RENEWAL_TWO_STEP_CANDIDATE.md`, SHA256
`8016c6a8a1e449e8a29db56f3421ef6180a7d88cb218f2078e62f151b2d0f848`.
Its source law is the complete theta density (r), with

\[
 \Phi(x)=e^{5x/2}r(e^{2x}),\qquad f=\Phi/A,
 \qquad r(1/t)=t^{5/2}r(t),
\]

and the fixed-offset \(K_2\) asymptotic proved in Section 1 below is

\[
 \frac{K_2(-R+u,-R+v)}{a\log(1/a)}\longrightarrow L(u,v),
 \qquad a=e^{-2R},
\]

where

\[
 L(u,v)=\frac{\mu}{A^2}(b_ub_v)^{5/4}
 \int_0^\infty t^{1/2}r(b_ut)r(b_vt)
       (\log t+u+v)\,dt,
 \qquad b_u=e^{2u}.
 \tag{1}
\]

The question is whether the matrix (L(u_i,u_j)) has a common sign for
every fixed finite family of distinct real offsets.  The answer is strict
negative definiteness when \(\mu>0\), assuming the displayed asymptotic and the standard
Hadamard factorization of completed \(\xi\).

The transform identity used below is source-locked in
`REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`, SHA256
`1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282`,
lines 74--80: with
\(\widehat h(z)=\int_{\mathbb R}h(Y)e^{-izY}\,dY\),

\[
 \widehat f(z)=\frac{\xi(1/2-iz)}{A}.
 \tag{2}
\]

## 1. Entrywise leading limit (the new step)

The preceding candidate established the \(q_2/r\) estimate
\[
 0\leq \frac{q_2(t)}{r(t)}\leq C_0(1+\log t),\qquad t\geq1,
 \tag{A1}
\]
and its pointwise limit \( (q_2(t)/r(t))/\log t\to2\).  It explicitly
evaluated only the diagonal.  The fixed-offset entrywise limit used here is
obtained by the following additional change of variables.

For \(x=-R+u,\ y=-R+v\), \(a=e^{-2R}\), \(b_u=e^{2u}\), and
\(b_v=e^{2v}\), insert the exact density form of \(K_2\) from the preceding
candidate and set \(s=at\).
Since \(x+y=\log a+u+v\), this gives

\[
 \frac{K_2(-R+u,-R+v)}{a}
 =\frac{\mu}{2A^2}(b_ub_v)^{5/4}
   \int_a^\infty \sqrt{s}\,r(b_us)r(b_vs)
      \frac{q_2(s/a)}{r(s/a)}(\log s+u+v)\,ds.
 \tag{A2}
\]

For fixed \(s>0\), (A1) gives
\[
 \frac{1}{\log(1/a)}\frac{q_2(s/a)}{r(s/a)}
 \longrightarrow2.
\]
For \(s\geq a\) and \(\log(1/a)\geq1\), the same bound gives a constant
multiple of \(1+|\log s|\) after division by \(\log(1/a)\).  Thus the
integrand in (A2), divided by \(\log(1/a)\), is dominated by

\[
 C_{u,v}\sqrt{s}\,|r(b_us)r(b_vs)|
       (|\log s|+1)(|\log s|+1).
 \tag{A3}
\]

For fixed positive \(b_u,b_v\), this is integrable at infinity by the
source tail and at zero by reciprocity followed by the same tail estimate.
Dominated convergence therefore proves the entrywise formula (1) for every
fixed real pair \(u,v\).  This is a new finite-row input beyond the preceding
diagonal-only calculation; no uniformity in the offsets is claimed.

## 2. The leading integral is a whole-line mixed energy

Put \(t=e^{2Y}\) in (1).  Since
\(r(e^{2(u+Y)})=e^{-5(u+Y)/2}\Phi(u+Y)\), the exact algebra is

\[
 L(u,v)=2\mu\int_{\mathbb R}e^{-2Y}f(u+Y)f(v+Y)
                     (2Y+u+v)\,dY.
 \tag{B1}
\]

Define the weighted profile and a rescaled row

\[
 g(Y)=e^{-Y}f(Y),\qquad d_i=e^{u_i}c_i,
\]

and set

\[
 P(Y)=\sum_i d_i g(Y+u_i),\qquad
 Q(Y)=\sum_i d_i(Y+u_i)g(Y+u_i).
\]

For any finite row (c), (B1) gives, with no omitted factor,

\[
 \sum_{i,j}\overline{c_i}c_jL(u_i,u_j)
   =4\mu\,\operatorname{Re}\int_{\mathbb R}\overline{P(Y)}Q(Y)\,dY.
 \tag{B2}
\]

The integration variable is all of \(\mathbb R\): the \(t\in(0,\infty)\)
leading limit has removed the finite cutoff.  This is separate from the
original \(V\) integral over the physical half-line \(X\geq0\).

## 3. Exact Fourier normalization and multiplier

Let
\[
 C(\omega)=\sum_i d_i e^{i\omega u_i}.
\]

Translation and multiplication differentiation give

\[
 \widehat P(\omega)=\widehat g(\omega)C(\omega),
 \qquad
 \widehat Q(\omega)=i\widehat g'(\omega)C(\omega),
 \tag{C1}
\]

where the prime on \(\widehat g\) is the real-frequency derivative.
Plancherel, with the convention above, therefore yields

\[
\begin{aligned}
 \sum_{i,j}\overline{c_i}c_jL(u_i,u_j)
  &=\frac{2\mu}{\pi}\int_{\mathbb R}|C(\omega)|^2
       \operatorname{Re}\!\left(i\overline{\widehat g(\omega)}
                                    \widehat g'(\omega)\right)d\omega \\
  &=-\frac{2\mu}{\pi}\int_{\mathbb R}|C(\omega)|^2|\widehat g(\omega)|^2
       \operatorname{Im}\!\left(\frac{\widehat g'(\omega)}
                                      {\widehat g(\omega)}\right)d\omega.
\end{aligned}
\tag{C2}
\]

Thus the multiplier in the energy \(2\operatorname{Re}\int\overline P Q\)
is exactly
\(-2|\widehat g|^2\operatorname{Im}(\widehat g'/\widehat g)\); (C2) also
records the outer factor \(2\mu/\pi\) for the kernel (1).

From (2),
\[
 \widehat g(\omega)=\widehat f(\omega-i)
   =\frac{\xi(-1/2-i\omega)}{A},
 \tag{C3}
\]
so this line contains no zero of \(\widehat g\).

## 4. Hadamard sign below the critical strip

The standard completed \(\xi\) facts used here are: it is entire of order one,
even after the change \(z\mapsto \xi(1/2-iz)\), and its zeros correspond to
the nontrivial zeta zeros \(0<\operatorname{Re}\rho<1\).  Hence every zero
\(\zeta=\alpha+i\beta\) of \(\widehat f\) satisfies
\(|\beta|<1/2\).  The strip and functional-equation conventions are recorded
in NIST DLMF §§25.2.E12, 25.4.3--25.4.4 and §25.10(i):
https://dlmf.nist.gov/25.2.E12, https://dlmf.nist.gov/25.4, and
https://dlmf.nist.gov/25.10.

Evenness and order one permit the paired Hadamard product (the nonconstant
exponential factor is absent after pairing \(\zeta,-\zeta\)):

\[
 \widehat f(z)=\widehat f(0)
       \prod_{\{\zeta,-\zeta\}}
       \left(1-\frac{z^2}{\zeta^2}\right).
 \tag{D1}
\]

The order-one zero count gives
\(\sum_{\zeta}|\zeta|^{-2}<\infty\), so this paired product and its
logarithmic derivative converge normally away from the zeros.  No boundedness
of that logarithmic derivative on the real \(\omega\)-axis is needed for the
Fourier integral: \(g\) is Schwartz, hence \(\widehat g\) and
\(\widehat g'\) are Schwartz, and
\[
 |C(\omega)|^2\,|\widehat g(\omega)\widehat g'(\omega)|
\]
is integrable because \(C\) is bounded.  This directly justifies (C2), after
which the ratio form is valid pointwise by (C3).

At \(z=\omega-i\), one paired logarithmic derivative contributes

\[
 \operatorname{Im}\left(\frac1{z-\zeta}+\frac1{z+\zeta}\right)
 =\frac{1+\beta}{(\omega-\alpha)^2+(1+\beta)^2}
  +\frac{1-\beta}{(\omega+\alpha)^2+(1-\beta)^2}>0.
 \tag{D2}
\]

All terms are positive because \(|\beta|<1/2\).  The paired series is the
logarithmic derivative of (D1), and completed \(\xi\) has infinitely many
zeros in the critical strip, so the sum is strictly positive for every real
\(\omega\):

\[
 \operatorname{Im}\frac{\widehat f'(\omega-i)}{\widehat f(\omega-i)}>0.
 \tag{D3}
\]

Since \(\widehat g'(\omega)=\widehat f'(\omega-i)\), (C3) and (D3) make the
integrand weight in the second line of (C2) strictly positive apart from the
factor \(|C|^2\).

## 5. Strict negative definiteness and finite-\(R\) consequence

For distinct real offsets and a nonzero coefficient row, the exponential
polynomial \(C(\omega)=\sum_i d_i e^{i\omega u_i}\) is not identically zero;
its zero set is discrete.  The profile \(g\) is Schwartz by the full-theta
double-exponential tails, so (C2) is finite.  Equations (C2) and (D3) imply

\[
 c^*[L(u_i,u_j)]c<0\qquad(c\ne0).
 \tag{E1}
\]

For a fixed finite offset family, the entrywise \(K_2\) asymptotic proved in
Section 1 then gives

\[
 \frac{c^*[K_2(-R+u_i,-R+u_j)]c}{a\log(1/a)}
   \longrightarrow c^*[L(u_i,u_j)]c<0,
 \tag{E2}
\]

so the actual (K_2) quadratic is negative for all sufficiently large (R).
Those nodes lie in \(J=(-\infty,0)\), generally outside the original
interval \(I=(-\log2/2,0)\).  If one combines this with the already accepted
holomorphic all-row propagation lemma, it yields existence of some finite
complex negative row in (I) whenever universal (K_2\)-positivity on (I)
is assumed.  It supplies no rank bound or explicit in-(I) nodes.

## 6. What the terminal \(V\) does at the same common shift

For fixed offsets \(u,v\), write the original terminal integral at
\(x=-R+u,\ y=-R+v\) with \(s=t-R\):

\[
 V(-R+u,-R+v)
  =\int_{-R}^{\infty}(2s+u+v)f(s+u)f(s+v)\,ds.
 \tag{F1}
\]

The full-line integral of the same integrand is zero.  Indeed, after
\(h=s+(u+v)/2\), the product
\(f(h+(u-v)/2)f(h-(u-v)/2)\) is even in \(h\), while the remaining factor
is \(2h\).  Hence

\[
 V(-R+u,-R+v)
  =-\int_{-\infty}^{-R}(2s+u+v)f(s+u)f(s+v)\,ds.
 \tag{F2}
\]

The full-source tail and all fixed derivatives are bounded by a
superexponential envelope (FULL_SIGN_TRANSFER_AUDIT, source §2, lines 56--62,
same SHA256 as above).  For every fixed finite offset family, (F2) therefore
gives entrywise

\[
 V(-R+u_i,-R+u_j)=o\!\left(a\log(1/a)\right),\qquad a=e^{-2R}.
 \tag{F3}
\]

The shifts in this section eventually lie outside the original interval
\(I\), so the source telescope needs a small global extension before its
remainder may be called a later-term aggregate.  For arbitrary fixed real
\(x,y\), put \(\alpha=e^{2x}\), \(\gamma=e^{2y}\).  From the complete-theta
tail and its positive first-term lower bound, the exact source integrand
\[
 \psi_{xy}(t)=\frac{\mu}{2A^2}(\alpha\gamma)^{5/4}t^{1/2}
   \frac{r(\alpha t)r(\gamma t)}{r(t)}(\log t+x+y)
\]
satisfies, for \(t\geq1\),
\[
 |\psi_{xy}(t)|\leq C_{xy}t^{3/2}(1+\log t)e^{\delta_{xy}t},
 \qquad \delta_{xy}=\pi(1-\alpha-\gamma)<\pi.
 \tag{F4}
\]
Choose \(\lambda\) with \(\max(0,\delta_{xy})<\lambda<\pi\); after enlarging
the constant, (F4) is bounded by \(C_{xy}e^{\lambda t}\).  The renewal sums
\(S_m\uparrow S_\infty\) and the source law \(S_\infty\) has density
\(r^*(t)=tr(t)/\mu\), so \(\mathbb E e^{\lambda S_\infty}<\infty\) for
\(\lambda<\pi\).  Therefore dominated convergence, with the cutoff
\(\mathbf1_{S_m\geq1}\), gives
\[
 K_m(x,y)=\mathbb E[\mathbf1_{\{S_m\geq1\}}\psi_{xy}(S_m)]
 \longrightarrow
 V(x,y)=\mathbb E[\mathbf1_{\{S_\infty\geq1\}}\psi_{xy}(S_\infty)].
 \tag{F5}
\]
The cutoff causes no boundary atom because \(S_\infty\) has a density.
Thus for the shifted pairs the limit of the finite-prefix telescope is
the exact difference \(V_R-K_{2,R}\).  If \(T_{\geq3,R}\) denotes this
later-term remainder, so that \(V_R=K_{2,R}+T_{\geq3,R}\), then (E2) and (F3)
imply, for every fixed nonzero row,

\[
 \frac{c^*[T_{\geq3,R}(u_i,u_j)]c}{a\log(1/a)}
 \longrightarrow -c^*[L(u_i,u_j)]c>0.
 \tag{F6}
\]

This is an aggregate leading compensation forced by the terminal tail.  It
does not make the individual later blocks positive, and it gives no finite
\(R\) sign theorem for the terminal \(V\).

## 7. Scope and remaining gap

This is a new sign result for the fixed two-step leading block.  The earlier
Hankel/Jordan report (SHA256
`c39016a5ba57aaa9e60f56682d11a9eebde9ee3202e4b2294c4e5beb156bc2c3`)
and integrated-sign report (SHA256
`8560b8c70e35fd76dbb2820471440aa802cefe21f9928e957c9f2e0be7dbe8eb`)
analyze the terminal (V), its positive sibling, or the physical half-line;
they do not establish (E1).  The present calculation uses the whole-line
limit after the (K_2) cutoff and should not be relabeled as a full-(V)
Fourier proof.

No general-\(m\) sign or leading-kernel extension, uniformity in offset
families, or terminal positivity theorem is proved here.  The argument assumes the entrywise
\(K_2\) leading asymptotic derived in Section 1 and the standard completed
\(\xi\) Hadamard factorization; either assumption must be checked separately
before using this card as a formal consumer.  The arithmetic input is only
the unconditional exclusion of completed-\(\xi\) zeros outside the critical
strip, together with its functional equation; no RH or stronger
prime-specific lower bound is used.  The negative leading Gram in (E1) and
the opposite aggregate leading Gram in (F6) cancel at scale
\(a\log(1/a)\), leaving the original terminal sign question open.

## Publication and independent acceptance

The complete candidate with SHA256
`c6138f666fb5e1a33831c21190c56d765b42cf5e89cc3054baf47bd6a3ae50e1`
was independently checked by `/root/sibling5_check`; review SHA256
`01931fa74b3598aedcbfad0ba9548d4416fcd47d7fe84730ed4e1ab27404358f`.
The parent independently reconstructed the entrywise limit, Fourier constants,
paired-product sign, fixed-real-pair convergence, and opposite aggregate limit.
The status line and this receipt are the only publication additions.

The staging K2 candidate cited above is publicly preserved, with only its
acceptance status changed, as
`docs/Codex/REPORT_2026-09-16_RENEWAL_TWO_STEP_OBSTRUCTION.md`, SHA256
`7a3e0972ca8e2306de49f048a7b31c4eb10c4f0217c35837105eb3a9d8c55a90`.
The transform source is
`docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md`.
This result is an analytic compensation diagnostic, not a new lower bound
for the original V and not canonical or Lean admission.

## END FILE docs/Codex/REPORT_2026-09-16_K2_LEADING_COMPENSATION.md

## BEGIN FILE docs/Codex/REPORT_2026-09-16_POINCARECOMP_INTAKE.md
SHA256: 7204afc827b61abfc5683f507724cfa08e5fbd7accdc265474d34f6a7f2dc977
BYTES: 6112

# Poincare comparison closed; complete signed form still open

STATUS: INDEPENDENTLY_REVIEWED_PAPER_SCOPED_RESULT.
No canonical admission, Lean proof, negative original-V witness or RH claim.

## Exact received artifact

Request REQ-2026-09-16-POINCARECOMP was sent once and has now been answered.
Response commit: `2dbd8191cfa515121c3c24c44ca61c2e5bc46acc`.
Path: `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_POINCARECOMP_2026-09-16.md`.
Git blob: `2f2b28ac8f73033e7671d6c5467fcff09bb98fc6`.
SHA256: `1920733be233ad33403c1c482b3db6c0d253db091ca646415fe84fd5b3a0bc6d`.
49478 bytes, 518 LF, no CR, final LF. Parent read all 518 lines.
The independent checker read the same immutable artifact in full; its report
and exact digest are preserved in the accompanying certificate.

## Accepted theorem and its exact limit

For every kappa>0 and every nonempty open interval J contained in (-infinity,0),
there is a finite complex row with nodes in J for which

    M[c] - kappa D_X[c] < 0.

In particular the sufficient lower envelope L_pi=M-(D_X+sqrt(D_G D_B))/(2pi^2)
has a negative finite row on the original interval I. Thus improving the
fixed positive constant in this absolute derivative comparison cannot prove
the required all-row sign. The valid conditional Poincare inequality and
L<=B_pi are unaffected. A negative lower bound is not a negative value of V.

This agrees with the independently published parent obstruction at
345dfea4365498cfdff460e78620f4d717e49147. The two parallel derivations concern
one proposed comparison, not two failed full-sign attempts.

## Parent reproduction of the proof

1. On Omega={Re z<0, |Im z|<pi/6}, a=e^(2z) satisfies Re a>0 and
   Re(1/a)>1/2. The full small-u modular series gives exponential decay for
   h(au)/sqrt(h(u)) and [a h'(au)-(h'/h)(u)h(au)]/sqrt(h(u)). The latter
   expression never divides by complex h(au). The large-u growth allowed
   when Re a<1/2 is canceled by the retained sqrt(r(t)) physical factor.
   The resulting half-density bounds are t^(7/4)e^(-pi delta t) and
   t^(11/4)e^(-pi delta t), locally uniformly in the two complex arguments.
   This establishes one joint holomorphic domain for the actual quadratic
   kernels M and D_X, not for the nonquadratic L_pi.
2. U=ats, W=at(1-s), T=U+W gives dt ds=dU dW/(aT). In M the signed
   coefficient log(t)+2x becomes exactly log(T). The complete transformed
   measure has the integrable majorant (15), so the M diagonal stays bounded
   and converges. On a fixed positive-mass rectangle with T>1, the limiting
   s-score is nonzero and X>=-x; hence D_X>=c_D(-x), c_D>0. No negative
   contribution was discarded from this nonnegative derivative energy.
3. The already accepted all-finite analytic positivity propagation lemma
   applies to K_kappa=M-kappa D_X. Were it PSD on every row in J, it would
   remain PSD along the connected negative real axis, contradicting the
   distant negative diagonal. This gives an actual finite-row existence
   result in J; it supplies neither a numerical rank nor a negative V row.

## Exact reciprocal transport also accepted

Writing w(t)=t^(3/2)r(t)^2/(2A^2), reciprocity gives

    j_t=p_(1/t)/p_t=g_(-log t),  E_t j_t=1,
    j_t g_x(1/t)=g_(x-log t)(t),
    F_x(1/t)=F_(-x)(t),  w(1/t)/t^2=w(t).

These identities have the correct -9/2 likelihood exponent and all Jacobians.
The conditional projection changes: j_t is nonconstant for t!=1, and the
rank-one projection discrepancy (27) is strictly positive. The primitive
potential changes by 2 alpha beta+beta^2-beta'; this is retained, not dropped.

Parent directly substituted t=1/tau into the truncated full expression:

    V_H(x,y)=integral_(1/H)^1 w(tau)(x+y-log tau)
                         F_(-x)(tau)F_(-y)(tau) d tau.

The finite cutoff becomes [1/H,1]. With the transformed conditional measure,
the covariance identity has factor 2 and cancels exactly the same covariance
part of M. Conditional endpoint products vanish by the exponential source
bounds; the physical t=1 trace remains w(1)(x+y)F_x(1)F_y(1). No integration
by parts in t occurred, so that trace is not an omitted additive term.
The H->infinity limit follows from the separately established absolute
integrability of the original signed pieces.

After this change of space the remaining expression is exactly

    V[c]=-2 Re integral_0^1 w(tau) conjugate(m^r)
                           [X m^r+b^r] d tau,
    m^r=sum c_i F_(-x_i), b^r=sum c_i(-x_i)F_(-x_i).

It is the original unknown sign in new coordinates. For two distinct nodes
the pointwise mean-channel determinant equals
-(x_1-x_2)^2 F_(x_1)^2 F_(x_2)^2. Thus neither positivity of a conditional
potential nor positivity at each integration point is the missing mechanism.
This determinant is not a negative integrated V witness.

## What is now excluded and what remains useful

Do not reopen a fixed positive absolute derivative budget, an unchanged
conditional projection under inversion, or positivity from an isometry alone.
The full source product was used to control the complex domain and score;
no property special to primes was used in this new proof.

The earlier reciprocal likelihood covariance diagnostic at
98d00ddda0777c4d19d4de9b83910e8477011ba5 is compatible with this response:
reciprocal means agree while their conditional fluctuations do not admit the
specified forward contraction. That diagnostic and a generic reverse Markov
contraction do not supply the mixed signed comparison.

Next action is a bounded semantic return on the mixed pair, before another
proof request. A useful candidate must supply a source-checkable sufficient
condition, distinguish the known negative control, and account for the whole
integrated mean channel. Merely restating its positivity fails this test.
The source-specific renewal block test already recorded in
PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES remains untried, not a proved supplier.

The current request is complete. The native goal of the complete V sign remains
active. This is one scoped exclusion and one exact reformulation; the sign of
the original V has not been proved or disproved.

## END FILE docs/Codex/REPORT_2026-09-16_POINCARECOMP_INTAKE.md

## BEGIN FILE docs/Codex/certificates/HYPERBOLIC_SOURCE_COMPENSATION_20260915.json
SHA256: a1770f2de7ef6917e396709b86a95538e6c7b6ea3329bc0ac4cf76b9a35c6c5f
BYTES: 5277

{
  "schema": "q3_isolated_analytic_receipt.v1",
  "status": "ACCEPT_SCOPED_PHYSICAL_WEIGHTED_SCALAR_RENEWAL_BUDGET_ONLY",
  "source_base": "0a0483582d37a6ba8d5cb2f836ecae63d0ecd6c7",
  "report_sha256": "feeb23e50223e5d85b16b8f6f1e83f849a9029f6f9aa8d4f47ad70cd4f5dad21",
  "reviewer": "/root/sibling5_check",
  "review": {
    "sha256": "5592d33a8cef4a91258249a1f0ee21f35bdd2a7a4ded8806cc0c1a9b72bd70a9",
    "text": "# Independent review: hyperbolic source ladder\n\nReviewed candidate: `HYPERBOLIC_LADDER_CANDIDATE.md`  \nSHA256: `9f812b4679496023fe9ce65dfb1875bf49d89b606c4fc1695b0e1ef6691aeea7`\n\n## Verdict\n\n**ACCEPT_SCOPED_FULL_GAMMA_LADDER_AND_AUXILIARY_NEGATIVE_ENERGY_ONLY.**\n\nThe Gamma-alpha product and its moment domain are correct.  Direct\ndifferentiation in `w=sqrt(pi s)` gives L2; Mellin integration by parts gives\nL3 with the stated shifted-moment term, and L4 follows at alpha two.  The\nendpoint conditions used for the transforms are sufficient.\n\nInverse Laplace transformation yields L5 with no origin distributions.  The\nlogarithmic-coordinate identities L6--L7 and the gauge calculation L8 have\nthe stated signs.  In particular L9 is valid: the Neumann boundary term\nvanishes and its right-hand side is strictly negative.  This is a genuine\nnegative test for that one forced scalar auxiliary form, not for V.\n\nL10 correctly retains every finite-row correction: `P_4`, the changed\ncoefficient column `P_-`, both endpoint traces, and the mixed target remain\nunpaid.  The report does not overstate the recurrence as a positivity or RH\nmechanism.\n\n## L6 extension readback\n\nReviewed extension in candidate SHA256\n`ee3969620395c35d6b1638368d09ec6c22226c1d55e970737db7d5d576826244`.\n\n**ACCEPT_SCOPED_COUPLED_FIELD_AND_RAW_ENERGY_FAILURE_ONLY.**\n\nConjugating the alpha ladder by `exp(-2k(X+x_i))` gives L11 with the\nstated constant coefficients and the `k+1` column.  The target identity\n`||Phi||_2^2 V[c]=-E_c'(0)/2` has the correct complex polarization and\nfactor.  All endpoint traces remain present.\n\nFor a one-node negative shift, the change `v=4k(u-x)` proves L13 and raw\n`E_x(k)` diverges as stated.  Hence L11--L12 do not justify raw all-k\nmonotonicity or an unweighted accumulated energy.  This does not rule out a\nseparately paid coupled weighted identity.\n\n## L7 source-specific renewal extension\n\nReviewed candidate SHA256:\n`f60fc9969efb3373968ed7028baae55ddbd100fffa19ad48e3bd352421e0ce9c`.\n\n**ACCEPT_SCOPED_SIZE_BIASED_SCALAR_RENEWAL_BUDGET_ONLY.**\n\nPitman--Yor Proposition 12(iv), equations (121)--(122), gives the stated\nlaw for `S_2`; multiplying every variable by `pi/2` gives L14 for `T` with\nthe same independent `H`.  Its density integrates to one and directly gives\n`E H^q=1/((2q+1)(q+1))`, hence `E H^2=1/15`.  Iteration gives the stated\nindependent renewal tail.  The cumulants yield\n`E(T^*)^2=E(T^3)/E(T)=4 pi^2/21`, so L16--L17 and the summed budget\n`10 pi^2/49` are correct.\n\nThe report preserves the necessary limitation: this is a scalar\nsize-biased-source coupling only.  The displayed likelihood has exponential\nlarge-`t` growth for every nonzero negative shift and is not globally\nLipschitz, so L17 neither identifies nor bounds `E_loss` or `V` without a\nseparately proved weighted conditional transfer.\n\n## L8 physical-measure mapping extension\n\nReviewed candidate SHA256:\n`feeb23e50223e5d85b16b8f6f1e83f849a9029f6f9aa8d4f47ad70cd4f5dad21`.\n\n**ACCEPT_SCOPED_PHYSICAL_WEIGHTED_SCALAR_RENEWAL_BUDGET_ONLY.**\n\nThe density calculation is exact:\n`W(t) r^*(t) = 1_(t>=1) t^(3/2) r_2(t)^2/(2 A^2)`, so L18 is precisely\nthe earlier physical outer measure after the conditional `s` coordinate is\nintroduced.  The conditional likelihood normalization is also correct: the\nJacobian in the conditional convolution supplies the extra factor `a^(-1)`,\nso the `a^(9/4)` in `g_x` yields the stated `a^(5/4) r_2(at)/r_2(t)` mean.\nThus L19 retains the original target and its complex conditional projection.\n\nSince `W` is bounded, L20 follows pointwise from `W<=W_max` and L17; it uses\nno invalid independence.  It remains only a scalar carrier-tail estimate.\nThe explicit retained differences in `g_x`, `p_t`, the mixed-node term, and\nthe cutoff boundary correctly prevent promotion to an `E_loss` or `V` bound.\n"
  },
  "primary_source": {
    "doi": "10.4153/CJM-2003-014-x",
    "pdf_sha256": "302f232c65a647b3e8a69bddb18163d12157b0d2b26e499e4c47fdde50ab957b",
    "locators": [
      "Theorem 1(ii), Eq24, p298",
      "Eq42, p301",
      "Proposition12(iv), Eqs121-122, pp318-319"
    ]
  },
  "scope": [
    "Exact hyperbolic moment and coupled-field identities",
    "Explicit negative scalar auxiliary energy and raw-k energy growth",
    "Source-specific size-biased renewal law, squared tail factor 1/15 and sum 10pi^2/49",
    "Exact original physical measure on size-biased carrier and bounded weighted scalar budget"
  ],
  "limits": {
    "E_loss_controlled": false,
    "V_sign_proved": false,
    "C6_all_R_proved": false,
    "RH_proved": false,
    "canonical_admission": false,
    "Lean_verified": false
  },
  "evidence_directory": "/Users/emalam/.codex/visualizations/2026/09/12/01a092ef-bf89-7693-aca8-42c3b691138a/hyperbolic-source-20260915"
}

## END FILE docs/Codex/certificates/HYPERBOLIC_SOURCE_COMPENSATION_20260915.json
