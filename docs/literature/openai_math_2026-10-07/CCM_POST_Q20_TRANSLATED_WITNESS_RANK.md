# Post-Q20 test: translated actual witnesses do not multiply the large negative direction

2026-10-25. Bounded own mechanism test, conditional on the inherited actual
zero-selective receiver. Original N=m,L=log m,M=floor(m^epsilon), same P.
Question: can one hypothetical off-line zero generate many robust negative
directions by translation, so that a trace/negative-mass estimate would be
a cheaper consumer than the single-direction estimate? No actual zero is
asserted; no prime bound or RH conclusion follows from this test.

## Exact joint form, before projection

Let w=delta+i gamma, v=-conj(w), multiplicity r, and use the actual separately
normalized contact-filtered g,k in CCM_RESTRICTED_PRIME_RECEIVER.md. For
f_a=exp(-i gamma a)tau_a g-exp(i gamma a)tau_-a k, the only nonzero evaluations
at distinct zeta zeros are

 M_fa(w)=exp(delta a),   M_fa(v)=-exp(delta a).

The inherited FULL polarized Weil formula, including multiplicity r, gives

 W(f_a,f_b)=-2r exp(delta(a+b)).                         (1)

In particular for any finite coefficients c_j, with v_j=exp(delta a_j),

 W(sum_j c_j f_aj)=-2r |sum_j c_j v_j|².                (2)

All mixed products are in (2). The matrix is -2r vv*, rank ONE regardless
of the number of distinct translations. Functions may be L2-independent
without being independent negative directions for this indefinite form.
Replacing (2) by the sum of its negative diagonal entries would change the
form. Neither distinct packets nor multiple copies of the same zero produce
multiple independent spectral residues. This calculation uses the inherited
source evaluations; it is not an independent favorable arithmetic estimate.

## A well-conditioned translated family on the original P

Fix epsilon=1/64 and derivative order q=67. Put h=L/2-log L,T=L/8.
Choose a fixed spacing D>0 sufficiently large depending on the two fixed
profiles, and a_j=h-jD with 0<=j<=floor(T/D). Let k_m be this number of points.
Then k_m=O(L). The source profiles and their derivatives have double-exponential
tails. Their same-side autocorrelations decay summably with |i-j|D; choose D
so that their off-diagonal row sum is less than one quarter of
G0=||g||²+||k||²>0. Opposite-side overlaps have shifts a_i+a_j>=2(h-T)->infinity;
their complete row sum tends to zero, even with k_m=O(L). The diagonal
opposite-side overlaps tend to zero as well. Thus the actual L2 Gram matrix
of f_aj lies between fixed positive multiples of I, uniformly in m eventually.
This uses signed/complex overlaps only for norm conditioning, not prime sign.

Use ONE common linear centered cutoff/Fourier truncation/original-P map U_m
for the entire family, and set z_j=U_m f_aj. The common cutoff is admissible
because every translation has the same minimum endpoint clearance. Their uniform L2 errors tend to zero faster than any
fixed inverse power of L by the inherited q=67 estimates. Entrywise Gram
errors are bounded by a constant times that L2 error; multiplying by k_m
still tends to zero. Hence the returned Gram G_m=(<z_i,z_j>) has the same
fixed positive lower and upper bounds. The returned vectors lie in the
same original sparse band; no packet projection has replaced P.

Polarize the return on f_i+f_j, f_i-f_j, f_i+i f_j and f_i-i f_j. Each
contains at most four fixed translated source profiles with uniform seminorms.
Polarization/continuity of the inherited full form return applies uniformly
to every mixed pair, since all a_j belong to [h-T,h] with the same boundary
clearance and fixed derivative bounds. It gives

 A_m=(z_i* K_m z_j)=-2r vv*+R_m,
 max_ij |R_m,ij|<=C_w rho_K,   ||R_m||<=C_w k_m rho_K=o(1). (3)

Here rho_K is Q17(4), including cutoff, Fourier, endpoint and BOTH contact
corrections. Its slowest power for this schedule is m^(-5/128) times fixed
log powers; k_m=O(L) does not destroy convergence. This is a bound on the
FULL form, so no additional arch or short-divisor fee is charged.

The restriction of K_m to the span of these returned vectors is represented
in orthonormal coordinates by G_m^(-1/2) A_m G_m^(-1/2). Thus it is a rank-one
negative matrix plus an o(1) perturbation. By min-max, all except at most
one eigenvalue are >=-o(1). This says nothing about other directions of P;
small perturbations may also create small negative eigenvalues here.

The one possible large negative eigenvalue has size comparable to ||v||²,
since G_m is uniformly conditioned. But

 exp(2delta h)<=||v||²
 <=exp(2delta h)/(1-exp(-2delta D)).                    (4)

Consequently translation packing supplies only the original signal scale
m^delta/L^(2delta), not an extra factor polynomial in m or even k_m. Constants
may depend on fixed delta,D and profiles. No uniform delta->0 assertion.

Moreover ||G_m^(-1/2)R_m G_m^(-1/2)||_1<=C k_m^2 rho_K=o(1).
Thus total negative spectral mass on this returned span differs from
2r v*G_m^(-1)v by o(1), and also has only the original signal scale.

## Disposition

This particular amplification mechanism fails with its mixed terms retained:
the true zero evaluations are collinear, and separated translations preserve
only one large negative direction after the fully paid original-P return.
Do not infer impossibility for families selecting DIFFERENT zeros, new source
constraints, or full CCM. Do not infer a favorable prime estimate from (1).
A trace/negative-mass route would need independent information about many
actual distinct off-line zeros or another source of rank; it cannot obtain
that rank by repeatedly translating this one phase-locked separator pair.
No numerical CCM spectra, Lean or Arb runs. No new arithmetic exponent.
Independent translated_witness_rank bounded PAPER audit: PASS after making
the common linear return map explicit. Reviewer checked polarization,
conditioning, all mixed returns, multiplicity versus rank, and trace bound.
Upstream source/receiver assumptions inherited, not independently re-certified.
This is one bounded failed amplification test, not a global novelty claim.
No new question dispatched.


## Conditioning boundary and a coalescing pair

Rank one by itself does NOT exclude amplification of the single negative
value. For any independent returned family with Gram G_m>0 and the entrywise
return in (3), its ideal negative magnitude is exactly

  2r v*G_m^(-1)v,

and the operator error in orthonormal coordinates is at most
C k_m rho_K/lambda_min(G_m). Its trace-norm bound is at most
C k_m² rho_K/lambda_min(G_m). Thus the separated-family conclusion above
uses its uniform Gram bound essentially. It cannot be extended to arbitrary
ill-conditioned growing families by rank alone. Even these error bounds
may be wasteful if cancellations can be estimated before dividing by a
small Gram eigenvalue.

A fixed close PAIR can be checked without such waste. Fix s0>0, take
0<s<=s0, h-T<=a<a+s<=h, and use the basis

  F0=f_a, F1=(f_(a+s)-f_a)/s
            =integral_0^1 partial_a f_(a+ts) dt.

At s=0 define F1=partial_a f_a. This identity holds before the COMMON
linear cutoff/Fourier/original-P map U_m. Its two zero-evaluation vectors
are opposite, with positive-side vector

  u=exp(delta a)(1,(exp(delta s)-1)/s),

where the quotient at zero is delta. Hence the full Weil matrix remains
-2r uu*, including both complex mixed products.

The parameter derivative changes the fixed profiles to combinations of
ordinary derivatives and fixed gamma multiples. All their fixed seminorms,
both vanishing exponential contacts, and double-exponential tails persist.
The integral expression for F1 gives uniform bounds for s in [0,s0]; there
is no 1/s loss. Apply the inherited E-norm return and its polarization to
F0,F1 directly. For epsilon=1/64,q=67 the full matrix error is O_w,s0(rho_K)
=o(1), with the same powers as (3). One additional fixed profile derivative
changes constants only. No estimate of two separate errors divided by s
is used. Both endpoint strips and all contact corrections remain included.

As a tends to infinity the two temporal lobes separate. The L2 Gram of
(F0,F1) converges uniformly on [0,s0] to the Gram of the corresponding two
vectors in L2(R) direct-sum L2(R). This limiting Gram is positive definite:
for s>0 a dependence would force a nonzero L2 profile to be an eigenvector
of a nonzero translation, impossible (its Fourier transform would be
supported on a measure-zero level set). For s=0 it would force that profile
to solve g'=c g, also impossible for a nonzero whole-line L2 function.
The phases only alter the scalar eigenvalue/c. Continuity on compact
[0,s0] gives a uniform positive lower eigenvalue and finite upper one.
The L2 return under U_m tends uniformly to zero, so the returned Gram
retains these bounds.

Consequently 2r u*G_m^(-1)u is bounded above and below by fixed positive
multiples of exp(2delta a). In particular even s=s(m)->0 cannot produce
an additional power of m from this two-vector span. The full returned form
is its rank-one matrix plus O(rho_K); on this span A_prime=-K+(A_arch-c_A I) after compression, so
||A_prime+K||<=50 log(m)+8 in orthonormal coordinates.
This is an adverse conditional witness calculation, not a favorable prime
estimate. No short-divisor fee or discarded mixed term is involved.

Growing numbers of close translates or growing derivative order remain
UNRESOLVED: they need uniform Gram/derivative constants and a paid return.
Do not count this scope refinement as another independent no-gain attempt,
or infer a prohibition for all dense translation families.

Independent dense_translation_return bounded read-only audit: PASS on the
appended conditioning and close-pair section, with inherited source/return
assumptions unchanged. No numerical experiment or new arithmetic exponent.
