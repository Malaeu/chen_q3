# Post-Q32: direct order transport fails its original-test hypothesis

2026-10-26. Bounded own preflight; independent q32_annulus_audit bounded PAPER PASS.
Original full CCM, same sparse P, N=m,L=log m,M=R=floor(m^epsilon).
Goal/RH OPEN. No new arithmetic estimate or Q33.

## Fork and shelf

After Q32 rollback to C0=A_prime+H_decay, test whether ordered positive
mass coupling can keep the sign before taking separate arithmetic/test norms.
The 8 October CCM_DENSITY_PAIRING_TEST.md already gives exact quantile pairing
and the optimal scalar derivative-distance bill. Repeating that W1 certificate
would be duplicate. The distinct preflight here checks the test-shape hypothesis
for direct monotone or convex-order comparison, without using a distance norm.
Literal search in CCM*.md found no same test-shape argument; not a global
novelty or literature-absence claim.

## Exact source and permitted endpoint balancing

Write h(x)=x^(-1/2)P Q_M(log x)P and fix a unit c=Pc.
Let g_c(x)=c* h(x)c, real on [1,m]. All temporal/mode cross terms stay inside g.
Inherited inputs: Q_M(0)=2I; h(m)=h'(m)=0 (Q02 original b contact);
integral_1^m h(x)dx=-H_decay, with H_decay positive semidefinite.
Consequently

 g_c(1)=2, g_c(m)=g_c'(m)=0, integral_1^m g_c(x)dx<=0.   (O1)

For alpha=sum_(1<=n<=m)Lambda(n)delta_n and beta=1_[1,m]dx,
Delta=alpha([1,m])-beta([1,m]), balance at m:
alpha'=alpha+max(-Delta,0)delta_m,
beta'=beta+max(Delta,0)delta_m.
These positive measures have equal mass and the same exact h-integral difference,
because h(m)=0. A quantile coupling therefore represents c*C0 c as the integral
of g_c(a)-g_c(b). All prime powers remain; endpoint balance is free for THIS h.
No sign follows from equal masses or positivity of the coupling alone.

## Test-shape obstruction, before any arithmetic estimate

For every nonzero original-P direction normalized as above:
1. Continuity and g_c(1)=2 make its integral strictly positive on some initial
   subinterval. By (O1), g_c must be strictly negative somewhere in (1,m).
2. It cannot be nondecreasing (the endpoint values decrease) or nonincreasing
   (then g_c(x)>=g_c(m)=0, contradicting the integral).
3. It cannot be concave: it would lie above the chord 2(m-x)/(m-1), whose
   integral is m-1>0.
4. It cannot be convex: its supporting tangent at m, with slope zero, would
   imply g_c(x)>=g_c(m)+g_c'(m)(x-m)=0, again contradicting the integral.
The inherited finite smooth matrix has the one-sided derivatives needed here.
The mean value theorem also gives both signs of g_c' within (1,m).
Adding an affine function does not repair convexity/concavity, since its
second differences vanish. Changing monotonicity with a linear term requires
returning the corresponding first arithmetic moment; equal total masses alone
do not cancel it.

Thus direct first-order stochastic dominance or convex/concave-order comparison
cannot be applied uniformly by asserting these shape properties for the raw
original tests. This excludes that proposed hypothesis map only. It does NOT
exclude a special signed coupling, a paid decomposition into shape pieces,
other transforms, or the actual CCM estimate. It does not determine the sign
of c*C0 c, and does not assert that the prime/continuous measures possess any
of those orders in the first place.

## Complete budget and decision

This preflight produces no new s. Retain A_prime<=12sqrt(m)P, hence
T_>R <=[12sqrt(m)+(56+32Omega)sqrt(R)+12(1+log R)^2]P,
P K_m P >=-[12sqrt(m)+50log m+8]P.
Conditional prior sharper estimates keep their own hypotheses; none is assumed.
No projection, omitted mixed term, proper-power truncation or additional
archimedean charge was introduced. Primary-consumer exponent unchanged.

Reject raw monotone/convex-order import before any costly coupling computation.
The remaining usable possibility must exploit the actual signed source together
with its nonmonotone test, not positivity of the matching alone. This is one
bounded hypothesis preflight, not three new attempts and not an automatic Q33.

## Independent audit limits

Read-only nonauthor q32_annulus_audit checked the complete elementary proof,
original b-contact endpoint, primitive sign, endpoint balancing and scope.
The claim holds for nonzero P, eventually M>=2 on the fixed-epsilon schedule.
The inherited primitive and source identities were not re-proved from scratch.
Nonlinear contact subtraction can change curvature and these data; it is not
covered by this obstruction and needs a separate full-source return.

## Endpoint-preserving convex repair: full cost and duplicate recognition

Own follow-up; q32_annulus_audit independently bounded PAPER PASS, including the duplication warning. Set K=1+Omega and use the inherited
||h''(x)||<=C_h K^2 x^(-5/2). Define

 r_m(x)=x^(-1/2)-m^(-1/2)+(x-m)/(2m^(3/2)),
 kappa=(4/3) C_h K^2.

Then r(m)=rprime(m)=0, rsecond(x)=(3/4)x^(-5/2), and
0<=r(x)<=x^(-1/2) on [1,m]. Both matrix functions kappa r P+h
and kappa r P-h have nonnegative second derivative on ran P and zero
terminal value/tangent. Integrating twice from m proves exactly

 -kappa r(x)P <= h(x) <= kappa r(x)P.

This retains the entire original h, including its mixed entries. Positivity
of the actual Lambda weights gives A_prime<=kappa sum_(n<=m)Lambda(n)r(n)P
<=6 kappa sqrt(m)P. Thus the complete proposed return is
T_>R <=[6 kappa sqrt(m)+b_div]P and
P K_m P >=-[6 kappa sqrt(m)+50log(m)+8]P.
Its price O_epsilon(m^(1/2+2epsilon)/log^2(m)) is worse than12sqrt(m).
Use the old fallback; do not promote this convexification to a better bound.

For the centered source, returning the correction preserves the actual scalar
discrepancy D_r=sum Lambda(n)r(n)-integral_1^m r(x)dx. The integral is exactly

 integral_1^m r=(3/4)sqrt(m)-2+3/(2sqrt(m))-1/(4m^(3/2)).

Consequently the certificate that pays the TWO correction terms separately
is at least kappa integral r~(3/4)kappa sqrt(m). This is a lower price for
that positive allowance only, NOT a lower bound for |D_r| or actual CCM.
Endpoint mass balancing is still free for r, but does not assign D_r a sign.

Keeping D_r signed brings us back to the existing Q04 primitive. With
Delta1(t)=psi(t)-(t-1), Delta2(t)=integral_1^t Delta1(u)du, exact Stieltjes
integration gives D_r=(3/4)integral_1^m Delta2(t)t^(-5/2)dt and, for the
full source, C0=integral_1^m Delta2(t)h''(t)dt. Both upper jets vanish;
Delta1(1)=Delta2(1)=0; all prime powers remain.
See CCM_Q04_CENTERED_SECOND_PRIMITIVE.md: that latter representation and its
failed absolute budget were already audited on20October. This follow-up
is NOT counted as another independent arithmetic attempt.

Concrete limit: shape repair is constructible, but its cheap signed return
is precisely unpaid arithmetic. Contact-generated matrices CX*+XC* vanish
after P compression and cannot change this pointwise scalar test; the earlier
CCM_POST_Q29_CONTACT_CERTIFICATE_TEST.md already records that freedom.
Nonlinear source-dependent repairs are not ruled out, but must supply an
independent joint bound instead of assigning it as a favorable premise.
