# TWOCHANNEL intake: necessary Fourier condition, no full relative bound

STATUS: ACCEPTED_LIMITED_PAPER
OPERATIVE_ACCEPTANCE: ACCEPT_NECESSARY_RF_FOURIER_AND_SIMPLICITY_CONDITION_ONLY
PX_RH_CLAIM: NOT_MADE
SCOPE: ISOLATED_PAPER; no canonical admission and no Lean certification

## 1. Result and exact boundary

The unchanged global carrier T12/T13 is positive and passes both source-end
limits. Its uniform relative bound RF is neither proved nor refuted. The
full response identifies the unpaid comparison and derives an additional
necessary condition: RF would imply RH and simplicity of all nontrivial xi
zeros. No multiple zero, negative source witness, or full RF failure is given.

This is the third completed source-construction analysis since the owner's
resumption: Villain, Brownian, Twochannel. The historical source-sign no-delta
count advances once, 5 -> 6, on acceptance of this intake. Conditional lemmas,
transport recovery and finalization do not reset it or add attempts. The next
construction requires the agreed owner brainstorming; none is opened here.
Global IC, global ODD2, all-order source sign and RH remain open.

Original mathematical request: REQ-2026-09-13-TWOCHANNEL, commit
`de2271bebae87c24ca0dfd3d02ae885de8db1b11`, blob
`eea7ebf0bd637925d065bd443100d11e83ad83ad`, SHA-256
`4d2193b53ba35111a7bf07f54541c6d2edc21815d2b3760d284fcbf17eb7d4d0`.
Boundary: GOAL058_ACTUAL_THETA_TWOCHANNEL_RELATIVE_FORM.
One candidate: GLOBAL_TWOCHANNEL_J_RELATIVE_DOMINATION.

Raw response, preserved unchanged:
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_TWOCHANNEL_2026-09-13.md`,
commit `755f7e10e3144abf1c72566645d781ea75247ec1`, blob
`a450fd955683afaf7025621e55b1ef54d6cc8fe2`, 56428 bytes / 765 LF / final LF /
CR 0, SHA-256
`133781768fa70c0e261de2a1f30e64dcca7d858bdaca3b98a5b8200bf1aff711`.
The fetched commit adds only that expected file. Parent and the sole read-only
checker read the entire raw response, including all three appendices.

## 2. Source and quantifiers

Retain Z=int Phi=xi(1/2), A=||Phi||_2, f=Phi/A, the full infinite theta source,

    V(x,y) = int_0^infinity (x+y+2t) f(x+t) f(y+t) dt,
    D(x) = V(x,x) > 0,
    W(x,y) = sqrt(D(x)D(y)) <J_x,J_y>.

RF asks for ONE delta>0 such that V[z]>=delta W[z] for every finite collection
of real nodes and every complex coefficient vector. W is the independently
constructed T12/T13 carrier, not an assumed Gram representation of V.
The original request and its five inputs remain unchanged; neither technical
follow-up supplies a new source, J, sign assumption or construction attempt.

Parent independently recomputed all six committed byte sets R,S1--S5,
including S2/S3, their bytes/LF/final-LF/CR, SHA-256 and Git blobs. Every pin
matches. The raw report carefully distinguishes producer-inherited S2/S3
SHA-256 values from locally recomputed source frames; that distinction is
retained. Parent byte verification does not establish unobserved producer
reading history or the time at which predictions were first written.

## 3. Accepted carrier and coalescing-node checks

For mu(zeta)=pi sech(pi zeta/2), the exact norm of the four fixed channels is

    W[z] = (1/(2pi)) int mu [
      (1+mu/4)|P_s|^2 + (1-mu/4)|P_a|^2 + |R_+|^2 + |R_-|^2 ].

P_s,P_a,R_+,R_- are exactly raw (10), all formed from the SAME physical z.
The cross coefficient is mu^2 Re(conj(P_+)P_-)/2 before diagonalization.
The factors 1+-mu/4 compare W to the four-channel norm N_0, not to sum|z_i|^2
or to the original signed form V. No coefficient floor follows.

The two independent Laplace components prove strict finite W positivity at
distinct nodes: group nodes with the same r_x=sqrt(x^2+4); the remaining
{a,-a} coefficient matrix has determinant tanh(a)>0. Exponential functions
with distinct rates are linearly independent. Repeated nodes are combined.

Every finite jet Gram matrix of Gamma=<J_x,J_y> at zero is also positive
definite. Even/odd channel combinations give triangular polynomial families
in s times exp(-e^4 s), with nonzero highest-degree coefficient at each
successive even or odd derivative. Fixed-order Hilbert differentiation is
justified by a polynomial times an exponential majorant. No bound uniform in
order is inferred.

The m-th finite difference at nodes j epsilon, divided by epsilon^(2m),
converges to K_(m,m)(0,0) for K=rho or Gamma by repeated fundamental theorem
of calculus. Both numerator and denominator cancel at the same order;
small carrier eigenvalues alone do not refute a positive relative bound.

Exact calibration, independently reproduced:
Gamma_11=3/20, Gamma_20=-3/20, Gamma_22=61/240; even Schur complement139/600.
For the full source, with d_0=D(0), q_0=f(0)^2 and
I_k=2 int_0^infinity t (f^(k)(t))^2 dt,

    kappa = (I_1-q_0)/d_0 > 0,
    sigma = I_2/d_0 + (q_0^2-2q_0 I_1)/d_0^2,
    sigma-kappa^2 = (d_0 I_2-I_1^2)/d_0^2.

Integration by parts and the accepted pointwise S5 curvature inequality
justify these equalities and kappa>0. The first relative jet quotient is
20 kappa/3>0. The full even-jet comparison, and then all orders, remain unpaid.

## 4. Full-source Fourier test and finite witnesses

The source identity is paid on the WHOLE real plane:

    V(x,y) = int_|m|^infinity 2u f(u+d)f(u-d) du,
    m=(x+y)/2, d=(x-y)/2.

With M_j=int |x|^j f(x)dx and T_j(R)=int_|x|>R |x|^j f(x)dx,

    int int |V| = M_0 M_2,
    int int_{max(|x|,|y|)>R} |V| <= M_0 T_2(R)+M_2 T_0(R).

The Jacobian and factor check is explicit: integrate m first to get8u^2,
then a=u+d,b=u-d to get (a+b)^2 on a+b>0. Evenness halves the full-plane
integral. The same substitution and symmetric tail union prove the bound.
No mixed/central or opposite-end contribution is omitted. Also |W|<=sqrt(DD),
int sqrt(D)<infinity, and the corresponding full W tails vanish.

The exact shift derivative is

    (partial_x+partial_y)V = -(x+y) f(x)f(y).

For F(z)=int f(x) exp(-izx)dx=xi(1/2-iz)/A, this gives

    Vhat(lambda,mu)
      = [F(lambda)F'(mu)-F'(lambda)F(mu)]/(lambda-mu),
    Vhat(tau,tau) = F'(tau)^2-F(tau)F''(tau).

The Fourier convention is antilinear in the first variable. The derivative
factor is i(lambda-mu); the diagonal limit has the displayed sign. At zero
it equals M_0 M_2, independently checking normalization. Distributional
Fourier transformation is justified by the L1 bounds; no unsupported boundary
integration or target positivity assumption is used.

For each fixed real tau, the carrier plane-wave energy S_W(tau) is STRICTLY
positive. Its independent w_+ component A_tau(s) satisfies

    sqrt(s) exp(e^4 s) A_tau(s) -> 2 sqrt(pi D(0)/5) > 0.

Parent checked a(0)=sqrt(2D(0)/5)e^2, the global inequality
exp(2sqrt(x^2+4))-e^4 >= e^4 x^2/2 and the resulting Gaussian majorant after
x=z/sqrt(s). This proves nonzero L2 energy without a tau-uniform floor.
Indeed S_W(tau)->0 as |tau|->infinity; strictness is pointwise in tau.

One explicit admissible finite sequence, with 2N^4 distinct real nodes, is

    x_(k,N)=k/N^3, c_(k,N)=N^-3 exp(i tau k/N^3),
    -N^4 <= k < N^4.

Full tails vanish as above. Global first derivative bounds for both kernels
make the expanding-square Riemann error O(N^-1); no compact-dependent unknown
constant is hidden. Consequently

    V[c_N]/W[c_N] -> [F'(tau)^2-F(tau)F''(tau)]/S_W(tau).

Each finite denominator is positive, and its limit is positive. All statements
are for each fixed tau; no high-frequency uniformity is supplied.

## 5. What this condition does and does not imply

RF would force F'^2-F F'' >= delta S_W >0 at every real tau. Thus it forbids
F(tau)=F'(tau)=0. Separately, RF plus W>=0 and accepted S4 Theorem T imply RH,
so all F zeros are real. Together these yield the conditional implication

    RF => RH and simplicity of all nontrivial xi zeros.

No multiple xi zero is provided. A hypothetical real multiple zero would
produce ratios tending to zero along the displayed finite sequence, killing
EVERY delta>0, while permitting V[c_N]>=0. It is a conditional RF obstruction,
not an actual V negative witness and not an actual refutation of RF or RH.

The actual consumer requires all-finite V>=0. It does not require this
particular strict relative domination. Necessity of RF for the actual source
sign is unproved; one must not make the extra simplicity requirement a newly
mandatory obstacle for the whole route. Even proving every scalar Fourier
diagonal positive would not establish all mixed Fourier matrix signs.

The already accepted parent report
`REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md` at24d0acc8 remains valid:
all-rank PSD on any nonempty open interval propagates to all real nodes, and
the SAME assumed delta for this analytic W propagates too. This response does
not supply the positive local premise, so that paid bridge creates no closure.

## 6. First unpaid comparison and independent verification

For P_z(t)=sum z_i f(t+x_i), Q_z(t)=sum z_i(t+x_i)f(t+x_i),

    V[z] = 2 Re <P_z,Q_z>.

Both functions are in L2. Their lower comparison with the EXACT four-channel
norm in section3, uniformly for every finite row, remains unpaid. Restating
that comparison as a new lemma is not source-sign progress. The raw RUN verdict
is correct; KILL or a full positive budget would exceed the evidence.

Independent raw-response review: sole sibling5_check, read-only and converged,
receipt SHA-256
`320bb222f7fa56dfff9e369a56504157e905ca7659652fb2608b1f920362f650`.
Parent separately checked the derivations and all six source pins.

Appendix A ran unchanged: script SHA-256
`2e6d034f9401cf7b241e23a60584a9ea889ff31c885cb715deee2d74a1078fdb`;
byte-identical stdout SHA-256
`bca0d4dbbbdfa4fa81b0b40a0cd471545e493fd2f123e12e896adb182b181345`.
Appendix B's1519 bytes and first1026-byte prefix match the declared hashes;
this verifies content, not an independently witnessed preregistration time.
Appendix C was replayed with ONLY its documented ROOT path adapted; stdout
matches byte-for-byte, SHA-256
`8552498f13209b7bdc0b02a6670d3b988c1e09492ad4712765334e80a7669676`.
Parent additionally verified S2/S3 directly from pinned Git objects.
No theta evaluation, quadrature, zero computation, Lean run or source-node
sweep was performed. Exact carrier algebra is not a certificate of RF.

## 7. Delivery and next decision

The original Pro turn ended after27m17s with a technical publication failure.
A same-chat recovery after3m15s found GitHub.create_file but no saved report.
The independently reviewed FINALIZE instruction at e4b859ee allowed a
standalone result of the SAME attempt to be created directly through that API.
The full mathematical response is now committed at755f7e10 and independently
checked. The technical steps do not constitute additional mathematical trials.

On acceptance, record SOURCE_SIGN_NO_DELTA6 and three completed constructions
since owner resumption, preserve all accepted partial results, and ask the
owner for the agreed brainstorming before a fourth construction. No new
candidate, Pro request, canonical writer acquisition or RH claim is authorized
by this intake itself. The full RH goal remains unachieved.

Exact intake review: parent draft SHA-256
`d99e4f7f317740cb24d83dfb6d3f3c7a9078c3e758c7cce2923e14dde677110d`,
independently CLEAN; receipt SHA-256
`7cc1bfacdd44fb305f0ab904037963205bbba85dd69e75f05dd035a1235c9a78`.
Only this status line and review receipt were added after that review.
