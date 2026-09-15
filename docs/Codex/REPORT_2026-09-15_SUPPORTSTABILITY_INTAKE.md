# Full source resolvent accepted; the critical response energy remains open

STATUS: PAPER_INTAKE; exact independent acceptance recorded below.
GOAL: FULL_V_NONNEGATIVITY_2026_09_15, active and unproved.
FULL_V / W2 / SUPPORT / IC / ODD2 / RH: OPEN.
ACTUAL_NEGATIVE_THETA_V_WITNESS: NONE. PX_RH_CLAIM: NOT_MADE.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated owner-authorized work.

## 1. Receipt and independent verdict

Proshka's single SUPPORTSTABILITY run completed at
2026-09-15T08:30:31.072789+00:00 after starting at
2026-09-15T08:00:31.226000+00:00: 1799.846789 seconds.
Live app readback found the same chat idle with the assigned SHA/path/verdict.
The remote branch independently contained only the assigned new response:

    docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_SUPPORTSTABILITY_2026-09-15.md
    commit 8d0a2e64dab913895e7385ff4d7bf6f5195e0028
    SHA256 60d603af4b1babf2618bc531bbd5365e770a1d608b0ddca63cdbbe4fd4b36be6
    60072 bytes; 649 LF; preserved unchanged.

The parent read all 649 lines in four bounded sections. Source R/H/G blobs
and SHA256 values were independently recomputed at the request commit and
matched the report. The sole independent read-only checker,
`/root/sibling5_check`, accepted these exact raw bytes as

    ACCEPT_FULL_SOURCE_RESOLVENT_AND_ONE_PROBE_CRITICAL_TAIL_INTERFACE_ONLY.

No proof of W2 or theta V positivity is included in that verdict. The local
branch was clean before a fast-forward containing only the new response.
No canonical writer, selector or RH-goal status was changed; no duplicate
request or premature interruption was made during the verified wait.

## 2. The full time-domain operator is now explicit

Retain the full source, A, I and all finite complex rows of the working goal.
The accepted normalization is F(z)=xi(1/2-iz)/A and
S=(xi-xi')/(xi+xi'), with s=1/2-iz. On Re s>1 the denominator is exactly

    1+xi'/xi(s)=a_gamma(s)+1/s+1/(s-1)-sum_(n>=2) Lambda(n)n^(-s),
    a_gamma(s)=1-(log pi)/2+psi(s/2)/2.

Raw (5)-(6) constructs a positive, absolutely continuous measure eta_8
using the full infinite compound-Poisson sum, with Laplace transform
1/a_gamma(8+p), Re p>=0, and mass <3/2. This uses gamma data only and
does not assume positivity of V. The remaining signed measure is

    M_8=sum_(n>=2) Lambda(n)n^(-8) delta_(log n)
          -(exp(-8u)+exp(-7u))du.

Both continuous terms are retained. Raw (8)-(10) proves convergence in
total variation of the complete signed resolvent

    Q_8=sum_(j>=0) eta_8*(M_8*eta_8)^{*j}=ell_8(u)du,
    ||M_8*eta_8||_TV<27/64,  ||Q_8||_TV<96/37,
    Laplace Q_8(p)=1/(1+xi'/xi(8+p)).

The parent independently checked the rational budgets and the absolute
continuity argument. No sign of ell_8 is assumed. With L(u)=exp(15u/2)ell_8(u),
the exact compact-test action is

    T_v h(t)=-h(t)+2 integral_0^infinity L(u)h(t+u)du.      (A)

Raw (11)-(14) proves this identity for the already specified T_v, initially
v=15/2, and then equality for every v>1/2 by a contour argument confined to
that controlled region. Its distribution includes -delta_0. It is defined
in D'; temperedness on the unweighted line is not silently assumed.
On compact t-intervals (A) is smooth; the only possible L2 failure is the
tail t->-infinity. This is an analytic domain statement, not a sign estimate.

## 3. What the failed absolute estimate actually excludes

The positive termwise majorant

    Q_8_abs=sum_(j>=0) eta_8*(|M_8|*eta_8)^{*j}

has infinite exp(15u/2)-weighted mass, rigorously, already because its first
term eta_8 has that infinite moment. The moment computation follows from
the positive Poisson construction and a_gamma(1/2)<0. This proves failure
of that termwise absolute estimate, not nonintegrability of the signed Q_8
or failure of W2. Even finite critical absolute L1 mass of the full Q_8
would be a stronger sufficient condition; it is not required by the goal.

There is one verified cancellation: the real pole of 1/a_gamma at its
zero sigma_gamma in (1,8) is absent from the complete 1/(1+xi'/xi).
Lagarias's unconditional positivity in Re s>1 ensures the full denominator
does not vanish there. This meromorphic cancellation does not assert that
the original Neumann series converges at sigma_gamma, and does not control
every critical tail contribution.

## 4. The exact one-response criterion

Take h_*(t)=exp(t)1_(t<=0), and define p(r)=(T_v h_*)(-r). Raw (18) gives

    p(r)=-exp(-r)+2 integral_0^r exp(-(r-u))L(u)du,
    p'+p=2L a.e.,  p(0)=-1.

The same p serves all v>1/2. It is locally absolutely continuous and square
integrable on every finite interval. The known weighted bound is

    integral_0^infinity exp(-r)p(r)^2 dr <= 1/3.

The decisive theorem, raw (22), is the equivalence

    p in L2(0,infinity)  iff  W2  iff  P+ U P-=0
                          iff  all finite complex theta rows have V>=0.

The implication from one response does not assert that one arbitrary test
determines an operator. This particular test has the exact distributional
inverse (1-partial_t)h_*=delta_0. If g_*=T_vh_* also belongs to unweighted H,
the full-source convolution identity a*g_*=b*h_* identifies g_*=Uh_*.
Its derivative then reconstructs the full tempered impulse with negative
support. That yields SUPPORT on every negative compact test, hence on H-.
The assumption g_* in H is essential before using its unweighted Fourier
transform. The converse uses half-line contractions and Tonelli's layer
representation of the exponential weight, with no new source sign assumed.

If the equivalent conditions hold, the norm is automatically exact:
||T_vh||_2=||h||_2 and integral_0^infinity p^2=1/2. Neither conclusion is
unconditional. The remaining target is solely

    sup_(R>0) integral_0^R p(r)^2 dr < infinity.            (J)

In particular, we do not need p to be positive. The positive Gaussian
control has p_g(r)=3exp(-r)-4exp(-2r), which changes sign and has energy 1/2.

## 5. The boundary ledger and controls

For each finite R, raw (34) is exactly

    integral_0^R p^2 = 1/2 - p(R)^2/2 + 2 integral_0^R pL. (B)

The first constant is p(0)^2/2, coming from -delta_0. The other boundary
must remain at finite R. No limiting trace at infinity has been established.
A uniform upper bound on the last two terms would prove J, but (B) itself
does not provide that bound. Those terms must be estimated jointly.

The rational plant in raw (30) has a shifted Schur half-plane and a growing
unweighted response. It is a logical operator control, not a theta source
or a counterexample to theta V. It does not satisfy the whole theta range
v>1/2, and is not claimed to do so. The old f0 control fails every fixed
shifted Schur half-plane, as explicitly proved in raw (32)-(33). Thus f0
does not share W1. None of these controls supplies theta J or its negation.

The conditional pole obstruction keeps multiplicities and common zeros:
xi(s)+xi'(s)=0 with xi(s)!=0 and Re s>1/2 would obstruct J. Common zeros
of xi and xi' are removable in the quotient and are not counted as poles.
No actual theta obstruction point is supplied; absence is not proved.

## 6. Verified external inputs and next return point

The parent checked the primary formula pages directly:
[DLMF 5.9.12](https://dlmf.nist.gov/5.9#E12), Re z>0 digamma integral;
[5.4.12-14](https://dlmf.nist.gov/5.4#E12), required special values;
[25.2.1 and 25.2.6](https://dlmf.nist.gov/25.2#E1), the absolutely convergent
zeta and derivative series only in Re s>1. The Lambda series is derived
by the divisor identity. Lagarias (1.4) is the already checked, pinned
primary input in the source-support hunt; no RH-conditional theorem is used.

The owner's next instruction returns BEFORE another expansion of the critical
response: locate the first residual and seek one source-derived bound for the
whole coupled contribution. The unweighted criterion J is retained as a test
of success, not advertised as a weaker problem or another sign budget.

The historical return point is explicit:
`REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md`, sections 3--4,
with its original physical weight w=1_(X>=0)Z Phi(X)/A^2 and conditional
projection C. For G=sum c_i G_xi, B=sum c_i x_i G_xi, D=XG+B,

    V[c]=2 Re <CG,CD>_(w mu)=E_micro[c]-E_loss[c],
    E_loss=2 E_mu[w X |(1-C)G|^2]
              +2 Re E_mu[w conjugate((1-C)G)(1-C)B].

This loss appears when comparing the two linked profiles before and after
conditional averaging. E_micro has no independently established sign; it
cannot be assumed to be a positive reserve that absorbs the loss. Both the
mixed term and the actual weight/cutoff remain part of any proposed law.
The full law with rates pi*n^2, not generic projection alone, must supply a
new discriminating hypothesis; the known deformations retain the generic
conditional identities without the target sign.

There was already a completed whole-half-line sibling:
`REPORT_2026-09-14_ANCHORED_CONTRACTION_HUNT.md`, H2--H6. Its Hardy map is
an isometry on centered inputs. It gives the prescribed output B exactly for
the Gaussian, but not for theta: the exact e_x/r_x tends to -tanh(x-a).
Thus its general energy identity is proved, while its literal theta fit is
false. The joint error contribution, not a forgotten half-line limit in the
Hardy proof, remained unproved. This does not exclude other common maps.

A candidate for the owner's single-budget law would be an explicitly
source-built nonnegative storage H(R), finite at R=0, with

    integral_0^R p(r)^2 dr + H(R) <= H(0)  for every R>=0.    (PROPOSAL)

This immediately implies J; no exponential decay is necessary. It is an
UNPROVED sufficient mechanism. Constructing H from the full linked source
and proving both properties independently is the actual task. Defining
H(R)=C-integral_0^R p^2 and assuming H>=0 would merely assume J. This
proposal neither supplies H nor equates arbitrary microscopic energy with V.
The already refuted positive fraction V>=C E_k is not required.

A geometric law for energies in disjoint blocks, E_(n+1)<=q E_n with fixed
0<=q<1, would instead give total energy <=E_0/(1-q). Such a law must measure
the FULL combined signal, with its interference already included, and q
cannot depend on the number of blocks. It is only a sufficient example.
Our proved 27/64 is a contraction in the convolution-series index j for
Q_8 in total variation, not such a physical-time law for p. Its estimate
does not survive the required exp(15u/2) reweighting; the positive termwise
critical majorant has infinite mass, while the actual signed tail stays open.

The next candidate must therefore account for the entire original coupled
remainder before taking separate absolute values, preserve all boundaries,
and yield a bound uniform in R. If it acts on arbitrary source rows, the
same construction and estimate must handle every finite complex mixture.
Local conservation/storage/dissipation and corrected-energy source cards
already exist in the residual and compensation hunts; reread their unpaid
hypotheses before repeating a search. A new name for J or the original
comparison is not a mathematical result. No new Pro request is sent by this
receipt; the completed response is recorded and the living chat is idle.

One coauthor construction and its attempted absolute estimate were completed;
reading, source checks, boundary audits and review are not separate attempts.
This is representation progress with proved analytic domains. It is not new
source-sign budget; no historical counter is reset or reconstructed. The
full RH goal remains active. No Lean or numerical theta test was run.
