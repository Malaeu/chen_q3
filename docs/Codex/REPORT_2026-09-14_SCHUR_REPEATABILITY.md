# Repeatable compensation: the invariant is a proved Gram representation

STATUS: ACCEPTED_PAPER_CONDITIONAL_BRIDGE_AND_PRESERVATION_COUNTEREXAMPLE.
SOURCE_BASE: 8ec0ed1cfaf2de5e394ebd94679fe300c3e24015.
OWNER_REQUEST: repeat positive-square extraction while preserving the residual property.
SCOPE: isolated paper; INCOMPLETE_NO_CONSUMABLE_TARGET (canonical edge unbound).
ACTUAL_THETA_NEW_SIGN_RESULT: NONE. ACTUAL_THETA_NEGATIVE_WITNESS: NONE.
FULL_V / IC / ODD2 / RH: OPEN. PX_RH_CLAIM: NOT_MADE.

## 1. Pinned input and the exact obligation

Input: REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md, SHA256
51168fb802d7facfb74291d0a3fc0009b121f540711df2fe10ae01cd84c1d14f,
R1--R7 (all raw pairs), R9--R13 (non-theta control), R15 (Schur residual).
Discovery brief: BRIEF_2026-09-14_SCHUR_REPEATABILITY.md, SHA256
d0716c67a6afe646ca7abe8ff2f007ed55cff2e5e962629fba3aa8266f9c7253.

Keep f=Phi/||Phi||_2, the FULL theta source, and I=(-log(2)/2,0).

    V(x,y)=int_0^infinity (2t+x+y) f(t+x)f(t+y) dt,
    S_a(x,y)=V(x,y)-V(x,a)V(a,y)/V(a,a).                    (S1)

All finite complex rows are required. R7 pays positive pivots of size one
and positive diagonal S_a(x,x) for x!=a; it does not pay PSD of S_a.
The first three-node obligation is

    S_a(x,x) S_a(y,y)-|S_a(x,y)|^2 >= 0.                   (S2)

The determinant of the original three-node matrix is V(a,a) times S2.
No new proof of S2 for theta is claimed here.

## 2. Literal repetition of the old source formula is not the invariant

S_a(a,y)=S_a(x,a)=0 exactly. Every kernel made by the original V formula
from a strictly positive even rapidly decreasing source is strictly positive
at EVERY real pair by the exact cancellation R2 in the pinned report.
Thus S_a on the whole interval cannot literally be another kernel of that
same positive-source form. This excludes only literal preservation, not a
gauge factor, division by anchor zeros, a different feature space, or PSD.

For any C2 kernel S with S(a,y)=S(x,a)=0, the fundamental theorem of calculus
with oriented integrals gives

    S(x,y)=(x-a)(y-a) T_a(x,y),
    T_a(x,y)=int_0^1 int_0^1 S_xy(a+s(x-a),a+t(y-a)) ds dt. (S3)

T_a extends continuously over the anchor. S is PSD iff T_a is PSD on I:
away from a use diagonal congruence by x-a; include a by continuity and
limits of nodes. This is a useful exact division but supplies no sign by
itself. It is the divided-kernel/Christoffel dictionary, not a claim of an
orthogonal-polynomial realization for our source.

The useful repeatable invariant is instead a PROVED common Hilbert-space
Gram representation. Once it is constructed independently, finite orthogonal
projection preserves it. Sections 3--5 give one precise sufficient entrance.

## 3. A source-readable logarithmic entrance (conditional theorem)

Let J be a real open interval and K:JxJ->(0,infinity) be symmetric and C2.
Define, WITHOUT assuming K is PSD,

    C_K(x,y)=partial_x partial_y log K(x,y),
    H_a(x,y)=log[K(x,y)K(a,a)/(K(x,a)K(a,y))],
    w_a(x)=K(x,a)/sqrt(K(a,a)).                             (S4)

Theorem: if C_K is a PSD kernel for all finite complex rows on J, then K
is PSD, its Schur residuals have explicit Gram representations, and every
finite family admits repeated square extraction, including zero pivots.

Proof. The double fundamental theorem gives

    H_a(x,y)=int_a^x int_a^y C_K(u,v) du dv.                (S5)

Build the real pre-Hilbert space from formal symbols e_u with bilinear
form <e_u,e_v>=C_K(u,v), quotient its zero-norm subspace, and complete.
This construction uses the assumed PSD of C_K, NEVER an assumed PSD of K.
Continuity of C_K implies u -> e_u is norm-continuous, so h_x=int_a^x e_u du
exists on each compact segment. Oriented integrals cover both sides of a.
Then H_a(x,y)=<h_x,h_y>, hence H_a is PSD.

In the Hilbert direct sum of tensor powers, set

    E(h)=(1,h,h^(tensor 2)/sqrt(2!),h^(tensor 3)/sqrt(3!),...),
    Psi_a(x)=w_a(x) E(h_x).                                (S6)

The norm series is sum ||h||^(2n)/n!=exp(||h||^2), hence converges.
The inner product series is exp(<h_x,h_y>). Consequently

    <Psi_a(x),Psi_a(y)>=w_a(x)w_a(y) exp H_a(x,y)=K(x,y).   (S7)

At the anchor h_a=0 and Psi_a(a)=sqrt(K(a,a))(1,0,0,...).
Removing precisely that constant component gives

    S_a(x,y)=w_a(x)w_a(y) [exp H_a(x,y)-1]
            =<w_a(x) E_+(h_x),w_a(y) E_+(h_y)>,            (S8)

where E_+ omits degree zero. This is an exact compensation of the whole
mixed contribution, not a deletion of a signed term. Complexify the real
Hilbert space for arbitrary complex coefficients. QED for the first step.

## 4. Why the rest of the finite family is then paid

More generally suppose an independently constructed map Psi already satisfies
K(x,y)=<Psi(x),Psi(y)>. After anchors A, let P_A be the orthogonal projection
onto the span of their feature vectors and R_A(x)=(1-P_A)Psi(x). Then

    K_A(x,y)=<R_A(x),R_A(y)>.                              (S9)

For the next node b put p=||R_A(b)||^2. If p>0, subtract its orthogonal
component from each R_A(x). For coefficients z at b and c_i at the other nodes,

    ||z R_A(b)+sum_i c_i R_A(x_i)||^2
      =p |z+sum_i c_i K_A(b,x_i)/p|^2
        +||sum_i c_i [R_A(x_i)-R_A(b)K_A(b,x_i)/p]||^2.    (S10)

The inner product is conjugate-linear in its first argument. The new kernel
is exactly K_A(x,y)-K_A(x,b)K_A(b,y)/p. If p=0 then R_A(b)=0, so the entire
row and column vanish and that node contributes nothing; skip it. After at
most N positive-pivot eliminations a family of N nodes is exhausted.

For a pre-existing UNKNOWN-sign kernel, a zero diagonal alone does NOT allow
this skip. It is legal here only because S9 has already been proved.
The post-projection vectors need not retain the exponential form S6.
What survives is their common positive Hilbert inner product.

## 5. The logarithmic entrance is stronger than the original target

For positive C2 K, the following are equivalent on J:

    C_K PSD;
    log K conditionally PSD (rows whose coefficients sum to zero);
    K(x,y)^tau PSD for EVERY real tau>0.                   (S11)

Proof of the needed equivalences is independent of complex-domain analytic
continuation: C_K PSD implies H_a PSD by S5, and exp(tau H_a) is Gram by S6
with sqrt(tau)h, so K^tau is PSD after positive rank-one scaling.
Conversely K^tau PSD implies log K conditionally PSD by tau->0 on each
fixed finite zero-sum row. Conditional PSD implies H_a PSD by adjoining a
with coefficient minus the sum of the other coefficients. Applying paired
finite differences to the PSD kernel H_a and taking their C2 limit gives
partial_x partial_y H_a=C_K PSD.

S11 is called infinite divisibility of a KERNEL. It is not the previously
known infinite divisibility of the positive-variable source law, and is not
transported through its logarithm, tilt, convolution or truncation for free.
It implies PSD of K, but PSD of K alone does not imply S11. Therefore a
failure of this entrance would not refute positivity of V or the user's
broader compensation idea.

A fully worked sibling: K(x,y)=exp(xy), a=0. Then C_K=1, h_x=x, and S6 is
(explicitly) (1,x,x^2/sqrt(2!),...). All finite families and all their projected
remainders are PSD. This is a KERNEL sibling, not the V produced by a Gaussian
source f (that different V has rank one in the prior report).

But even for this sibling, demanding the logarithmic entrance after every
step is too strong. Its divided residual is

    R(x,y)=(exp(xy)-1)/(xy), with R=1 at xy=0,
    R(x,y)=int_0^1 exp(txy) dt.                             (S12)

It is a positive-valued PSD kernel. Put z=xy. Elementary series division,
or exp(z/2)*sinh(z/2)/(z/2), gives

    log R=z/2+z^2/24-z^4/2880+O(z^6),
    C_R=1/2+xy/6-(xy)^3/180+O((xy)^5).                    (S13)

Hence partial_x^3 partial_y^3 C_R(0,0)=-1/5<0. A PSD smooth kernel has
nonnegative diagonal derivative forms, obtained as limits of finite
quadratic forms of third differences. Thus C_R is not PSD on ANY neighborhood
of 0, and R is not infinitely divisible there. K is infinitely divisible,
yet its divided Schur residual need not be. The point 0 can be translated
into I for this kernel-only control. No actual theta counterexample is used.

## 6. Exact preflight on the unchanged theta source

All values V(x,y)>0 by pinned R2, so log V is well-defined. On compact
node intervals, the pinned full-source bounds justify differentiation under
the integral. With u=t+x, v=t+y, w=2t+x+y, the proposed supplier is exactly

    V_x=int_0^infinity [f(u)f(v)+w f'(u)f(v)] dt,
    V_y=int_0^infinity [f(u)f(v)+w f(u)f'(v)] dt,
    V_xy=int_0^infinity [f'(u)f(v)+f(u)f'(v)+w f'(u)f'(v)] dt,
    C_V=(V V_xy-V_x V_y)/V^2.                              (S14)

Normalization f->c f scales V by c^2 but leaves C_V and H_a unchanged;
the weights w_a in S4 retain the correct normalization in the Gram formula.
There is no discarded endpoint or infinite-tail term in S14.

What is already paid? For y=x+h, the RAW2 result gives

    log[V(x,x)V(y,y)/V(x,y)^2]=C_V(x,x)h^2+o(h^2)>=0,
    hence C_V(x,x)>=0.                                    (S15)

Strict RAW2 does not by itself make this limit strictly positive. Nor does
S15 imply PSD of C_V. The first unproved necessary comparison for the new
entrance is

    C_V(x,x)C_V(y,y)-C_V(x,y)^2>=0  for all x,y in I.        (S16)

Even S16 for all pairs would not pay the all-rank supplier C_V PSD.
No new numerical sign search or symbolic evaluation of the full theta
series is claimed in this report.

The existing f0/f_delta controls in pinned R9--R13 explicitly discriminate
the needed hypothesis: because their V has a negative finite row in I,
S11 and the proved implication force C_(V0), respectively C_(Vdelta), NOT
to be PSD on I. These controls nevertheless satisfy squared-coordinate
strict log-concavity and have all RAW2 forms positive. Thus the new supplier
cannot be inferred from those generic hypotheses. This is a logical
consequence of an already proved control, not a located negative row of C_V.

## 7. Semantic return: what the source literature actually supplies

The three dictionaries were (i) innovations/conditional covariance/Schur,
(ii) divided residual/Christoffel, (iii) logarithmic curvature/infinite
divisibility. Read local SL20_ALIAS_HUNT_USAGE_CARDS.md and the Toeplitz
CARD 6 in CF_TOEPLITZ_FORMULA_CARDS.md first. The latter starts from an
already positive measure/Toeplitz form; it supplies no such representation
for V. The former distinguishes infinite divisibility of the source law
from kernels, and reciprocal-xi PF statements from the actual theta source.
No previously rejected source-PF route is reopened.

Registered ask.sh query, once:
"Schur complement innovations Christoffel divided kernel Schoenberg infinite divisibility".
Query SHA256 1dbbd9b138bfe7910a6fdd4b822bd093847d2fe85321e372b6bc5365d1a37e77.
Exit 2: ASK_STATUS INCOMPLETE, q3_docs semantic-index freshness validation
failed. Local Schur hits are generic algebra/other consumers. Tool display
was truncated; no byte-exact full raw-output receipt is claimed. No rerun,
index repair or absence inference. mgrep's previously observed expired-token
failure was not retried. Available web search was used for primary sources.
External stopping condition: verify this exact mechanism and its hypotheses;
no claim of exhaustive search. Source bytes/hashes/read locators are in the
companion receipt JSON; cited PDF pages were also rendered and read.

A. Roger A. Horn, Schlicht mappings and infinitely divisible kernels,
Pacific J. Math. 38 (1971), 423--430.
https://msp.org/pjm/1971/38-2/pjm-v38-n2-p13-p.pdf
Read printed p423 and Lemmas 8--9, pp426--427.
Short quote, Lemma 8: "conditionally positive definite".
Mapping: Horn's centered kernel is H_a of S4 after replacing his H by
log K. His integral-test convention matches finite-row PSD for continuous
kernels: Riemann sums give one direction and compactly supported bump
approximations to finitely many point masses give the other. His logarithm
criterion on p423 matches S11; only positive real K is used here, so there
is no branch choice. Lemma 9 is the divided-kernel mechanism behind S3.
FIT: source-verified conditional mechanism, not a theta sign supplier.
The f0 control fails conditional PSD of log V0, as explained above.

B. Shibananda Biswas, Dinesh Kumar Keshari, Gadadhar Misra,
Infinitely divisible metrics and curvature inequalities for operators in the
Cowen-Douglas class, author-hosted manuscript, Theorem 3.3, PDF pp10--12.
https://math.iisc.ac.in/~gm/gmhomefiles/papers/cuin.pdf
Read statement and proof on pp10--11; p12 not used as a premise.
Short quote, p10: "positive definiteness of the curvature function".
Mapping: their polarized complex curvature corresponds to the role of C_K;
their theorem is LOCAL and uses analytic/polarization hypotheses. It is not
quoted as a global theorem for our real interval. S5--S11 prove the needed
real-interval statement directly instead. FIT: partial analogue with an
explicit domain distinction. Their curvature hypothesis, not scalar
curvature sign, is exactly the missing strength revealed by the control.

C. C. E. Rasmussen and C. K. I. Williams, Gaussian Processes for Machine
Learning, MIT Press (2006), chapter 2, printed p16, eq(2.19); see also p12.
https://gaussianprocess.org/gpml/chapters/RW2.pdf
Short quote, p16: "conditioning the joint Gaussian prior distribution".
Mapping: one noiseless training node a; prior covariance K, posterior S_a.
This requires a genuine prior covariance (PSD). Our V has not been shown
to be such a covariance, so the formula cannot establish its initial sign.
FIT: conditional repeatability/interpretation, not initial positivity.
The negative V0 control cannot be a prior covariance on all of I.

## 8. Decision and next bounded mathematical test

The user's loop is mathematically valid once its invariant is a proved Gram
representation; its full induction, complex coefficients and zero pivots
are now explicitly specified. Requiring the old positive-source formula or
infinite divisibility of every residual would be an unjustified extra demand.

Selected entrance for a further test: S14, the mixed logarithmic interaction
kernel C_V. The cheapest necessary test is S16 on the exact full source;
a rigorous negative row stops only this stronger entrance. A positive finite
check does not pay it. A successful supplier must derive a positive measure,
feature representation or another full-quantifier inequality directly from
the actual theta source, then use S5--S10. It may not define a square root
of V or C_V before proving its positivity.

This report establishes a conditional route and a concrete preservation
counterexample, NOT an actual-source sign advance beyond RAW2. The universal
sign obligation has not been discharged by writing it in logarithmic form.
No all-rank V or RH result, Lean certificate, canonical node close, supplier
admission, or new Proshka delivery is claimed.

AUTOPSY: dropped=COUPLING; note=Conditional log-curvature Gram entrance still requires full PSD of C_V; only its diagonal follows from RAW2.

## 9. Review

Independent read-only checker /root/sibling5_check returned CLEAN on exact
full draft SHA256
5f64bbbe4030d134eeabb9ca79f1212f348cbddc8c5c9d7900d2fd986ae4f78e.
The checker confirmed S1--S16, integral orientations, tensor convergence,
complex projection convention, zero-pivot handling, S11's stronger scope,
S13's exact -1/5 and the unpaid theta S16. Parent independently checked the
same mathematics and the quoted primary-source statements. Only acceptance
metadata and the AUTOPSY taxonomy label changed after that mathematical review.
This is accepted isolated paper, not a Lean or canonical acceptance receipt.
