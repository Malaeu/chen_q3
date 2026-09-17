# Boundary energy versus causal reconstruction: analytic audit

Historical reconciliation: this is the SAME open FULLVPOS SUPPORT problem from September 15. R=(I+U_old*)/2 and P_-RP_+=B_old*/2. The source equation is unchanged. The generic source-support hunt was already registered; this audit and its extra control do not establish a new source mechanism. See the independently checked addendum below.

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete. No original V sign result. Root-owned
private candidate after the Fourth return in the assigned global Pick hunt.
Base 72a536a26517860edfb29ae5dfee941c4e18c811. No new Pro proof request.

## A0. Exact source, old consumer, and conventions

Keep X(z)=xi(1/2-iz), F(p)=xi(1/2+p),
M(p)=F(p)/(F(p)+F'(p)), initially meromorphic, and
omega(y)=X(y)^2/(X(y)^2+X'(y)^2),
eta(y)=X(y)X'(y)/(X(y)^2+X'(y)^2).
Real common zeros give removable multiplier values; they do not affect L2.
Fourier transform is uhat(y)=int exp(-iyt)u(t)dt; inverse has 1/(2pi).
Inner products conjugate the first argument. Then

 m(y)=M(iy)=X(y)/(X(y)-iX'(y))=omega(y)+i eta(y),
 |m(y)|^2=Re m(y)=omega(y), 0<=omega<=1,
 m(-y)=conjugate(m(y)).

Define the bounded whole-line L2 operator R by (Ru)hat=m uhat and the
real tempered distribution Y=Fourier^{-1}(m). R is convolution with Y,
translation invariant, and ||R||<=1 without RH.
This R is NOT the full signed Suzuki field transform and ||Ru||^2 is NOT
asserted to equal the original Q or V.

Old OPENSGN Lemma 7, equations (27)-(29), already establishes that

 (P) M(p)=Omega(p)=(1/pi)int_R p omega(y)/(p^2+y^2)dy, all real p>1/2,

would supply the full signed-field norm identity and original Weil positivity.
P is OPEN. Its recovery below in control language is not a new RH estimate.
The translated-radical tests passed for that signed field, not a claim that
R annihilates the same radical.

Pins:
- docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_OPEN_SIGNED_TIME_KERNEL_IDENTITY_2026-09-06.md: ffe6d8e38be778f0622eebd7654a55c5312114a49335e6af30a3587e8eadd840.
- docs/routeB_bus/OPENSGN_INDEPENDENT_CHECK_2026-09-06.md: 74d9410a3aad3c985025e7595a53b0d0192571cb1c76fdf78972348bfd7faa73.

## A1. An unconditional total-energy identity

Plancherel and |m|^2=Re m give, for every complex u in L2(R),

 Re <u,Ru> = (1/(2pi))int omega(y)|uhat(y)|^2dy = ||Ru||_2^2 >=0. (1)

All integrals exist by boundedness. Equivalently, U=2R-I is unitary because
|2m-1|=1 a.e. These identities use only the real-axis multiplier algebra;
they do not distinguish the theta source from the control below.

## A2. Exact cutoff identity and what passivity additionally requires

Let P_T be multiplication by 1_{(-infinity,T]} and
W_T(u)=Re <P_T u, P_T Ru>. For every u in L2, expand u=P_Tu+(I-P_T)u
and use (1) on P_Tu:

 W_T(u)=||R P_Tu||_2^2
        +Re <P_Tu, P_T R(I-P_T)u>.                         (2)

The first norm is over the WHOLE output line. No cutoff commutes with R.
For this particular R, the following are equivalent:

 (a) W_T(u)>=0 for every T and u in complex C_c^infinity(R);
 (b) W_T(u)>=0 for every T and u in complex L2(R);
 (c) P_T R(I-P_T)=0 for every T.                            (3)

(a) implies (b) by density and bounded quadratic-form continuity. If (c)
holds, (2) proves (b). Conversely, if the cross block at a fixed T is
nonzero, choose a in ran P_T and b in ran(I-P_T) such that <a,Rb> !=0.
For u=a+lambda b the right side of (2) is ||Ra||^2+Re(lambda<a,Rb>).
A complex lambda makes it negative. Thus (b) implies (c).
For a translation-invariant convolution operator (c) is precisely causality,
equivalently supp Y subset [0,infinity). Hence the all-cutoff condition
is an exact missing SUPPORT property, not a further norm-smallness estimate.
It remains OPEN for the actual Y. A nonzero small cross block is insufficient
for (3), because the later input amplitude can be arbitrary.

## A3. What the two source-verified mechanisms actually supply

Source H: Sanjay Lall, Linear analysis and systems, lecture 6, version
2001.10.17.01, slide 6-24. Author-hosted university notes:
https://lall.stanford.edu/engr210a/lectures/lecture6_2001_10_17_01.pdf
PDF SHA256 d8c54ddd3f62b2c1263c8598e5da2dc407e80f440e6c20d4b2d198415eb531ce.
Short quote (11 words): "Every Ĝ ∈ H∞ defines a causal, time-invariant operator".
The slide states both directions of the bounded causal LTI/H-infinity
correspondence, for L2[0,infinity). This is a theorem statement in lecture
notes, not a newly published source-specific result or a proof reproduced here.

Map: if (3) is paid, restrict R to inputs supported in [0,infinity).
Their outputs stay in the same half-line; the restriction is bounded, linear,
and commutes with the right-shift semigroup. The cited theorem supplies a
bounded analytic G on Re p>0 with boundary G(iy)=m(y) a.e. The norm bound
is inherited from the multiplier norm. Bounded harmonic uniqueness yields
Re G equal to the Poisson extension of omega, hence Re G=Re Omega.
Thus G-Omega is an imaginary constant. The real symmetry of the operator
makes both G and Omega real on positive p, so this constant is zero.

This also identifies G with the ORIGINAL meromorphic M, not an arbitrary
positive replacement: around any point of the imaginary axis where M is
analytic choose a small half-disk. There G-M is bounded analytic with zero
boundary values on its straight edge. Local Hardy boundary uniqueness
makes it identically zero. The identity theorem then gives
(F+F')G=F throughout Re p>0, without dividing by unknown interior zeros.
Consequently (3) would imply (P), and the old consumer would apply.
No implication is accepted here from mere boundary positivity to (3).

Source P: A. Luger and M.-J. Y. Ou, On Applications of Herglotz-Nevanlinna
Functions in Material Sciences, I (2022), section 2.6, Definition 4 and
Theorem 8, printed p.444 (PDF p.12), DOI 10.1007/978-3-031-04496-0_19.
https://bpb-us-w2.wpmucdn.com/sites.udel.edu/dist/f/12544/files/2023/11/OU_Pub_7.pdf
PDF SHA256 d212f1eac97bd17992bedbc86c562cd2f910e583934593f43ee105f81e094763.
Short quote (13 words): "It can be shown that every passive operator R is causal".
The definition requires nonnegative cumulative work for every compact smooth
input and EVERY cutoff, not only the complete-line integral. Its theorem
identifies real passive convolution operators with positive-real responses
(after the displayed rotation of variables). Here convolution, reality,
temperedness and local L2 integrability are PROVED; the cumulative-work
hypothesis is OPEN and exactly (3) by A2. Thus this source supplies a correct
conditional bridge but no independent source hypothesis closing it.

## A4. Exact analytic negative control, not the theta source

Use X0(z)=2+cos(4z), F0(p)=2+cosh(4p). This elementary factor occurs in the
old smooth H2 plant B(z)(2+cos(4z)); here we deliberately omit B. We do NOT
assert this new control has the smooth theta density, reciprocity or additive
PF-infinity property. Its inverse Fourier source is the positive atomic measure
2 delta_0+(delta_4+delta_{-4})/2 of total mass 3. Dividing the source by 3
would normalize it without changing M0.
It is even and real, has nonreal zeros, and F0,F0'>0 for real p>0. Its
multipliers obey all of A0-A2, in particular the positive total work (1).

Write z=exp(4p), s=sqrt(19), a=(-2+s)/5, b=(-2-s)/5. Then 0<a<1 and b<-1,

 M0(p)=(z^2+4z+1)/(5z^2+4z-3)
       =1/5 + A/(z-a) + B/(z-b),
 A=4(2s+1)/(25s)>0, B=4(2s-1)/(25s)>0.                (4)

For |z|=1 the Laurent series converges absolutely:

 M0(iy)=d0 + sum_{n>=1} A a^(n-1) exp(-4iny)
               -sum_{n>=1} B b^(-n-1) exp(4iny),
 d0=1/5-B/b>0, d1=-B/b^2<0.                         (5)

Therefore Y0 is a finite signed measure with atoms at 4n and -4n;
its atom at -4 has coefficient d1 !=0. It is NOT causal. The poles
p=(log|b|+(2k+1)pi i)/4 have positive real part and are not cancelled,
as B!=0. This pole observation alone is not an original V witness.

There is also an exact smooth-input cumulative-work witness. Take any
nonzero real v in C_c^infinity(0,epsilon), 0<epsilon<1, and
u(t)=v(t)+lambda v(t-4), with lambda=-2d0/d1>0. At cutoff T=2,
P_Tu=v. On the support of v the only contributing output atoms are 0 and
-4, so (5) gives

 W_2(u)=(d0+lambda d1)||v||_2^2=-d0||v||_2^2<0.       (6)

Nevertheless W_infinity(u)=||R0u||^2>=0 exactly. This disproves the generic
rule that boundary positivity, bounded multiplier, even positive real-axis
source values and complete-line nonnegative work suffice for passivity or
Poisson reconstruction. It neither refutes the theta-source condition (3)
nor establishes its negation, and is not a Q/V counterexample.

## A5. The unchanged full-source equation for the missing support

This is a source-level description of the same unresolved condition, not an
extra assumption paid by naming a renewal equation. Set
q(t)=Phi(t)/xi(1/2), so qhat(y)=X(y)/xi(1/2), and a_q(t)=(1-t)q(t).
Then ahat_q=(X-iX')/xi(1/2), and therefore exactly in tempered distributions

 a_q * Y = q.                                        (7)

q and a_q are Schwartz; convolution with tempered Y is defined. Multiplying
the smooth Fourier multipliers proves (7), with the same full theta source.
Because X and X' cannot vanish together on a set of positive measure, m is
the unique bounded measurable solution of ahat_q m=qhat, up to null sets.
Equation (7) has been solved on the whole line by A0. Its solution's one-sided
support is OPEN. Positivity and evenness of a source measure alone do not
provide that support: A4 tests these measure-level conditions only. It does
not test smooth strict positivity or the full theta/PF hypotheses. No
additive PF property of r is silently transferred to q.
A proposed source mechanism must force the missing support in this exact
convolution equation. Calling an arbitrary causal positive replacement a
solution would change the boundary response and fail the consumer.

## A6. Search receipts and stopping boundary

The three registered shelf queries in Fourth return ran once. Each returned
INCOMPLETE, with q3_docs freshness validation failure; candidate metadata did
not provide this supplier. Failed semantic indexing is not proof of absence.
A bounded primary web pass and one adaptive pass yielded Sources H and P.
Primary PDF bytes and relevant rendered pages were inspected. A failed web
PDF screenshot and a PMC recaptcha are not used as mathematical evidence.
No index rebuild, new installation, new agent, numerical RH scan or Pro
proof request was made.

What is useful here: the exact cutoff-block criterion and an analytic
control with a negative finite-cutoff work value make the missing premise
checkable. What is NOT new: OPENSGN's Poisson reduction, the signed field,
or the need for source-specific structure. The literature's missing
hypothesis remains OPEN for the full source; therefore this is a method
boundary/conditional mapping, not a newly found positive source supplier.
Stop this generic passivity/Hardy hunt at that condition. Do not dispatch
"prove causality" as though it were a weaker paid request. If work continues,
first reconcile any existing source-level one-sided inversion attempt for
(7), and proceed only with a specific new property and a discriminating test.
Canonical admission INCOMPLETE_NO_CONSUMABLE_TARGET; production HOLD and
original sign counters unchanged. Independent checking of A0-A5 is complete; actual source causality remains OPEN.

## Independent acceptance

Verdict: ACCEPT_BOUNDARY_ENERGY_CAUSALITY_MAP_ONLY.
Final candidate SHA256: d203e0437b1125b1603156c3dc3e3e8ccd59a2028513ca9869c175cbf2a38a09.
Complete review SHA256: 3587d9bbe39bc589023f487193f0958a1496065cbfb65461c71880cc97f5770d.
Complete parent check SHA256: ca4d7adfba62a9848c47e8ec07a877dfc66c433f28da29ea6317a89a1e2aed6d.
The parent read the complete review. The atomic control is explicitly limited to positive/even source measures and does not test smooth strict positivity or theta/PF structure. The exact cutoff criterion and the conditional Hardy transfer are accepted; no original V sign or original negative witness was obtained. Full source normalization is also bound to REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, section 2, SHA256 1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282. The certificate embeds the independent and parent checks and source-search provenance.

## Historical addendum: exact FULLVPOS crosswalk

Independently accepted: ACCEPT_SAME_FULLVPOS_SUPPORT_CROSSWALK_ONLY. No new support proof.
Base 3f3a5b496a01d10a3399313a27916a43f0f70183. Existing audit remains
mathematically valid; this addendum corrects incomplete historical reconciliation.

Pinned old inputs:
- docs/Codex/REPORT_2026-09-15_FULLVPOS_INTAKE.md, SHA256 8f9abe3e60ce3188709ad5b6e91022980a78bc33f70635fcb4f3fe6abb77aad6, sections 2-4, full intake read.
- docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_FULLVPOS_2026-09-15.md, SHA256 3e51c432683640422e2052680e4c592fd39a8078f213b70ee5f1bb4c72d4a508, formulas (9)-(13), (30), (37)-(39); complete raw acceptance is inherited from the pinned intake, not claimed re-audited here.
- Current audit candidate d203e0437b1125b1603156c3dc3e3e8ccd59a2028513ca9869c175cbf2a38a09 and accepted report 6e6cb67d218498b5da275d87e527daf28acbbbaa0e8969fa9adba83b323e9339.

In OLD FULLVPOS let S=(X-iX')/(X+iX') on the real line, with normalization
of X cancelling from the quotient, U_old=Fourier_inverse M_S Fourier,
B_old=P_+ U_old P_-, and k=Fourier^{-1}_nonunitary S. The old intake already
accepts all finite original V>=0 iff B_old=0, and B_old=0 iff supp k lies
in (-infinity,0]. Its actual source support condition remains OPEN.

In CURRENT A0, m=X/(X-iX'), R=Fourier_inverse M_m Fourier,
Y=Fourier^{-1}_nonunitary m. Since |S|=1 a.e., exactly

 2m-1=conjugate(S), R=(I+U_old^*)/2,
 P_- R P_+ = (1/2)(P_+ U_old P_-)^*=(1/2)B_old^*.       (C1)

Hence current causality at T=0 is exactly the OLD SUPPORT condition; all
other cutoffs follow by translation invariance. Current all-cutoff work
positivity is therefore equivalent to the old full V positivity, by the
already accepted A2 and FULLVPOS equivalence. This is a crosswalk, not a
new independent source-sign input.

For k^sharp(t)=conjugate(k(-t)) in distributions, we also have

 Y=(delta_0+k^sharp)/2.                                (C2)

Thus support Y in [0,infinity) is equivalent to support k in (-infinity,0];
the delta at zero cannot cancel a contribution on either open half-line.
The reversal of support is explained by the ADJOINT, not a convention error.

To compare full-source equations without square-root normalization clutter,
put a0=(1+t)q, b0=(1-t)q. The old identity U_old a0=b0 gives
U_old^* b0=a0. Therefore R b0=(b0+a0)/2=q, precisely the CURRENT
((1-t)q)*Y=q. Scalar normalization from f to q and the old 1/sqrt(2)
factor cancel; this is the same inversion question.

Historical consequence: SOURCE_SUPPORT_HUNT from September 15 already
registered Hardy/Wiener-Hopf, passive scattering and positive storage for
this exact source-support problem. Current Fourth return should have
reconciled that brief before its new generic primary searches. No current
source-specific advance is claimed. The new elementary cumulative-work
control is a bounded diagnostic only; even stronger smooth non-theta
controls were already retained by FULLVPOS. Preserve both.

Stop the generic support/passivity loop. Do not reissue this source inversion
as a new research joint merely because the adjoint or Cayley average changes
its name. Any further attempt needs a genuinely new verified property of the
full source and must pass the already accepted smooth controls. No canonical
admission, source-sign counter change, original negative V witness or RH claim.

Crosswalk candidate SHA256: cd918cf965e9cba1205e7edb44fbc0a63b3caba20cfca10ed637645492187eac.
Complete independent crosswalk review SHA256: 5bd8e1d79dcb4c5f5eb37aa113b6be0b4241cd3a2a7f801b6743aa7215d51de4.
Parent crosswalk check SHA256: b574320cfb22b1f25448945e3592dfce8361f831b9193eaa2043b8accbfcf3f6.
