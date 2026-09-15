# FULLVPOS intake: exact source-phase criterion, theta SUPPORT still open

STATUS: ANALYTIC_INTAKE; independent raw acceptance recorded below.
SOURCE_BASE: 66c0da89b5d5da291df694e7cfa1d319df1d2691.
GOAL: FULL_V_NONNEGATIVITY_2026_09_15; ACTIVE_RESEARCH_OBJECTIVE_NOT_PROVED.
FULL_V / IC / ODD2 / RH: OPEN. ACTUAL_NEGATIVE_THETA_V_WITNESS: NONE.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated research only.
PX_RH_CLAIM: NOT_MADE.

## 1. Exact receipt and scope

The owner asked why Codex and Proshka appeared idle. Live app readback found
the FULLVPOS response completed, and GitHub independently contained the
assigned file. The native turn ran from 2026-09-15T06:58:24.926000+00:00 to
2026-09-15T07:24:20.180461+00:00, about 1555.254461 seconds. Thus the run
finished after the 07:21 UTC observation, which had still reported active.
The apparent lack of activity was not a missing request. No repeat was sent.

Raw response:

    docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_FULLVPOS_2026-09-15.md
    commit 66c0da89b5d5da291df694e7cfa1d319df1d2691
    SHA256 3e51c432683640422e2052680e4c592fd39a8078f213b70ee5f1bb4c72d4a508
    63433 bytes; 655 LF; preserved unchanged.

The parent read the full response, including the middle sections omitted
by the first truncated display. The sole independent reader
`/root/sibling5_check` returned on these exact raw bytes:

    ACCEPT_FULL_SOURCE_PHASE_CUTOFF_IDENTITY_AND_SUPPORT_EQUIVALENCE_ONLY

The response's R/G/I/C Git blobs were independently recomputed and matched;
the goal and prior intake SHA256 pins also matched. The update from the
previous published head adds only the assigned response. No canonical
writer, selector, control or native RH-goal state was changed.

## 2. Accepted construction and exact remaining obligation

Keep the full normalized theta source f and I=(-log(2)/2,0) from the goal.
Let F(z)=integral_R f(t)exp(-izt)dt, E=F+iF', E#=F-iF'. On the real line
S=E#/E has modulus one, with removable real common zeros treated explicitly.
Using the unitary Fourier transform, define

    H=L2(R), U=Fourier_inverse M_S Fourier,
    a(t)=(1+t)f(t)/sqrt(2), b(t)=(1-t)f(t)/sqrt(2),
    a_x(t)=a(t+x), b_x(t)=b(t+x).

Then U is a source-defined unitary and Ua_x=b_x, before any sign assumption.
Write P+ and P- for the two half-line projections, and A,B,C,D for the four
blocks of U in H+ direct-sum H-. For p_x=P+a_x and n_x=P-a_x put

    T_x=Cp_x, L_x=Bn_x, R_x=Ap_x.

The accepted exact kernel and all-complex-row identities are

    V(x,y)=<T_x,T_y>-<L_x,L_y>-<R_x,L_y>-<L_x,R_y>,
    V[c]=||T_c||^2-||L_c||^2-2 Re<R_c,L_c>.

These formulas retain the mixed terms. The original boundary is checked by
(partial_x+partial_y)V=-(x+y)f(x)f(y); it is not discarded in L2 notation.
The new positive diagonal obeys the full-source bound

    0 <= ||T_-R||^2 <= 2 integral_R^infinity (1+u^2)f(u)^2 du -> 0.

This verifies the required decay geometry, not domination of V by this
energy. Analytic vector-valued continuation is supplied on the full strip
|Im z|<pi/4 and the corresponding product domain.

The substantial exact strength check is density:

    closure span{a_x : x in I} = H.

Orthogonality on I extends analytically to every real shift. Fourier
uniqueness, with the nonzero entire E having only isolated real zeros,
then annihilates the orthogonal vector. No bounded inverse synthesis is
asserted. For the bounded self-adjoint difference of projections

    Q=P+ - U* P+ U,
    V[c]=<a_c,Q a_c>,

density therefore gives the equivalence

    all finite complex rows in I have V[c]>=0
          iff B=P+ U P-=0.                              (SUPPORT)

Necessity tests Q on H-: <n,Qn>=-||Bn||^2. Sufficiency deletes L in the
exact identity and yields V(x,y)=<T_x,T_y>. This is a necessary and
sufficient criterion in this representation, not the stronger and excluded
uniform bound V>=C E_NULLFIELD. It neither asserts nor proves SUPPORT.

A future actual n in H- with ||n||=1 and beta=||Bn||>0 would yield a finite
negative theta row by density, with approximation error <beta^2/8 and
V[c]<=-47 beta^2/64. No such n or beta is supplied for theta; no effective
node count follows from density alone.

## 3. Controls and verified classical inputs

For g(t)=c exp(-b t^2), the same construction gives

    U_g v(t)=-v(t)+4b integral_t^infinity exp(2b(t-s))v(s)ds,
    T_x(t)=sqrt(2)g(x)exp(2bt) 1_(t<0),
    V_g(x,y)=g(x)g(y)/(2b).

Negative support is preserved and all Gaussian null directions are kept.
For the previously accepted f0=exp(-t^2)-(1/4)exp(-2t^2), the fixed
negative jet -25/162 instead produces a strictly nonzero B0 output.
This uses the accepted non-theta control; it is not a theta counterexample.

The parent checked the cited classical interfaces directly:

- [DLMF 20.7.32](https://dlmf.nist.gov/20.7#E32), Jacobi reciprocity.
- [Tao, Fourier Notes 2](https://terrytao.wordpress.com/2009/04/06/the-fourier-transform/), Exercise 29 and Theorem 43, differentiation and Plancherel with the explicit frequency conversion.
- [Liu, Li and Kou, arXiv:2310.10040v2](https://arxiv.org/html/2310.10040v2), section 1.2 and the beginning of section 3: the exp(+itz) convention identifies positive support with upper-half-plane H2. Reflecting t converts it to this report's negative-support convention.

These inputs justify the stated conditional Hardy mechanism, not a theta
SUPPORT theorem. No unrelated claims in those sources are used.

## 4. Remaining joint and continuation

The same S defines the tempered distribution k=Fourier_inverse_nonunitary S.
The source equation k*a=b is established. What is missing is

    supp k subset (-infinity,0].

This is equivalent to SUPPORT, including the reverse implication through
a smooth approximate identity supported in (-epsilon,0). A bounded
holomorphic upper-half-plane realization of S would suffice by Hardy
invariance. The report proves neither that realization nor its failure.
Modulus one on the real axis and the imaginary-axis moment bound do not
settle interior poles, growth or support; f0 satisfies those weak checks too.

Before another proof model, the owner's semantic-return rule applies to
this exact remaining object: one-sided convolution/support, the off-diagonal
half-line block, and the equivalent Hardy multiplier condition. Any source
transfer must supply a missing hypothesis, not rename SUPPORT or assume
the desired zero location. No new request or sign experiment is dispatched
by this intake. One bounded construction has been received; parent reading,
source checks and independent review are not further attempts, and no
historical counter is reset or reconstructed.

The completed FULLVPOS request is no longer pending. The full mathematical
goal remains active and unproved. This is accepted representation progress
with an exact criterion, not new positive source-sign budget or RH closure.
No numerical theta evaluations, quadratures, rank sweeps or Lean runs were
performed for this intake.
