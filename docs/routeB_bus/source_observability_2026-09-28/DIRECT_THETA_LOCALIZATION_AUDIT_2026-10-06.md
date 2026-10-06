# Direct theta localization: audited stall, 2026-10-06

Source: `PROSHKA_DIRECT_THETA_LOCALIZATION_INLINE_2026-10-06.md`, complete
question9 and inline answer9 in the existing Missing T7 Lemma chat. The linked
supplement was not needed for the claims below and was not retrieved.

## Accepted mathematical content and exact scope

On the original m=N schedule, write I=[-L/2,L/2], L=log m,
psi_n=(-1)^n L^(-1/2) exp(2 pi i n t/L), g=c_m(G)/sigma,
sigma=||c_m(G)||, and P for the carrier projector (NOT the bottom projector).
For any unit bottom vector v with synthesis f and eigenvalue lambda:

- y=P(Gf) is nonzero since <f,y>=integral G|f|^2<0; its center coefficient
  is sigma/sqrt(L) <g,v>. The multiplication matrix is c_(n-ell)/sqrt(L).
- With B(s)=integral_(I intersect (I-s)) (G(t+s)-G(t))^2
  Re(conj(f(t)) f(t+s)) dt and J(s)=exp(-s/2)/(1-exp(-2s)),
  S=W(Gf,Gf)-Re W(G^2 f,f)
  =integral_0^L [J(s)-2 cosh(s/2)]B(s)ds
  +sum_(2<=q<=m) Lambda(q)/sqrt(q) B(log q).
  All prime powers and the full pole term remain. B(s)=O(s^2) pays the
  archimedean singularity. The q=m overlap has measure zero.
- Set e=(1-P)Gf and d=(1-P)G^2 f. Then EXACTLY
  W(y,y)-lambda||y||^2=S-2 Re W(e,y)-W(e,e)
  +lambda||e||^2+Re W(d,f)>=0.
  Source-null exclusion would require an independently proved negative
  bound on this same signed expression. No such bound was obtained.

The explicit even source-null CARRIER vectors
u=(e_m+e_-m)/sqrt(2), a=<g,u>, x=(u-a g)/sqrt(1-|a|^2)
satisfy, along the original eventual sequence,

  L ||(1-P)(G f_x)||^2 -> ||G||_2^2/2,
  ||(1-P)(G f_x)||^2 / ||G f_x||^2 -> 1/2.

Here |a|=O(L^(3/2)/m^2); sigma->||G||_2, and the normalized correction
changes the scaled leakage by o(1). Thus an absolute O(m^(-1/4)L^A)
leakage bound uniformly over even source-null carrier vectors is FALSE
for every fixed A. These x are NOT proved bottom vectors. This kills
only the carrier-uniform projection repair, not OS or bottom exclusion.
For arbitrary carrier v the valid remaining bound (m>=4) is

  ||(1-P)G f_v|| <= ||G||_infinity ||v_edge|| + 6 A_G L/m ||v||,
  edge={|n|>floor(m/2)},
  A_G=(||G''||_1+2||G'||_infinity)/(4 pi^2).

No actual-bottom edge bound is supplied; even one would not alone fix S.

## Independent checks

One bounded read-only pass per distinct claim: Luna researcher
`/root/answer9_variation_audit` checked the phases, nonzero variation, full
signed Weil identity, four correction terms, and finite jump-domain
handling against CCM equations(3.8)-(3.11). No sign/factor error found.
Luna researcher `/root/answer9_edge_audit` checked the coefficient estimate,
Parseval tail identity, half-leakage asymptotic, source-null normalization,
and the constant6 in the edge split. No error found. Neither audit asserts
a bottom-space estimate. No Lean build was relevant or run.

## Root attempt: Gaussian damping pays only the prime cross term

The established |G(t)|<=D0 exp[-(pi/2)exp(2|t|)] implies, for a=log n,

  exp(2|t|)+exp(2|t+a|)>=2 exp(a)=2n,
  sup_t |G(t)G(t+log n)|<=D0^2 exp(-pi n).

For zero-extended translations and the full positive-weight prime operator
P_I=sum_(2<=n<=m) Lambda(n)/sqrt(n) (T_log(n)+T_log(n)^*), this gives

  ||M_G P_I M_G|| <= 2D0^2 sum_(n>=2) Lambda(n)n^(-1/2) exp(-pi n)
  <=2D0^2 r^2(2-r)/(1-r)^2, r=exp(-pi),

using Lambda(n)/sqrt(n)<=n. This uniform estimate pays precisely the
-2G(t)G(t+log n) cross term in B. It pays neither endpoint-G^2 term,
the projection correction, nor the sign of the full defect. The variation
auditor independently checked this normalization and limitation.

## Decision

Direct multiplication/localization is STALLED at the full signed defect.
Do not ask again for an unsigned uniform projection-error repair. OS,
source-null bottom exclusion, G1/G3 and RH remain OPEN. The bounded primary
literature update in `LITERATURE_GROUND_OVERLAP_UPDATE_2026-10-06.md` found
no supplier in the checked CCM, Andrade and Groskin sources.

The cheaper conditional consumer checked below motivates the final question:
if P0 is the full bottom projector, eps=||K g|| and rho=||P0 g||, then
|lambda_min| rho=||P0 K g||<=eps. Hence rho>0 and eps/rho->0 would give
lambda_min>=-o(1), without simple-evenness or vector tracking. The existing
floor-kill audit already proves eps->0 for this same source. The full-form convergence argument has now been checked below. An actual-source
LOWER bound on rho remains a separate OPEN obligation. This is a checked
conditional consumer, not a supplied overlap bound; it does not close G1/G3.

## Cheaper conditional consumer: paper check

Read-only Luna `/root/weak_observability_consumer` first found the exact
source residual supplier and the existing odd-test density argument, then
completed one bounded mathematical check of their full-carrier extension.
This accepts a CONDITIONAL reduction, not a new source inequality or RH.

1. For g=G and G'', repeated integration by parts retains every endpoint
jet Delta_k=g^(k)(L/2)-g^(k)(-L/2). Each fixed jet is polynomial(m)e^(-pi m).
The exact coefficient recurrence is c_n(g')=i omega_n c_n(g)+Delta_0/sqrt(L).
For e=P_m g-g|I its interior derivative therefore includes the term
-(Delta_0/sqrt(L)) sum_(|n|<=m)psi_n. It vanishes for even g; it must not
be dropped for a general derivative. The remaining Fourier tails and
endpoint errors obey ||e||2+||e'||2+D_e=O_R(m^(-R)) for each FIXED R.
All factors in the Sept25 full mixed-form estimate are at most polynomial;
the exterior envelope pays ALL prime powers beyond m. Thus

  ||K_m c_m(G)||=O_R(m^(-R)),
  sigma_m=||c_m(G)|| -> ||G||2>0,
  epsilon_m=||K_m g_m||=O_R(m^(-R)).

The actual derivation is `ODD_TRIAL_SIGN_2026-10-06.md:289-341`, using
`../proshka/PROSHKA_ATTACHMENT_GOAL058_INDEPENDENT_COMPLEMENT_FLOOR_2026-09-25.md`
(C), (I), (T), and the independently audited global radical identity.
No constant is claimed uniform as R or derivative order grows with m.
This is an operator residual, obtained by supremum over all unit tests.

2. Fix arbitrary COMPLEX f in C_c^infinity, with support eventually inside
I. All its periodic endpoint jets vanish. Its coefficients are exactly
(-1)^n L^(-1/2) fhat(2 pi n/L). With p_m=P_m f, e=f-p_m and Omega=2 pi m/L,
Schwartz coefficient decay, tail summation and Parseval give

  ||e||2=O_q(Omega^(1/2-q)),
  ||e'||_L2(I)=O_q(Omega^(3/2-q)),
  ||e||_infinity,I=O_q(Omega^(1-q)).

For the zero extension and 0<h<=1, interior pairs plus two edge strips give
||e(.+h)-e||2<=h||e'||2+sqrt(2h)||e||infinity. Therefore in the Sept26 norm

  A(e)=||exp(|t|)e||2<=sqrt(m)||e||2 ->0,
  D(e)=sup_(0<h<=1) h^(-1/4)||e(.+h)-e||2
      <=||e'||2+sqrt(2)||e||infinity ->0.

Choose fixed q sufficiently large. The full Weil-form continuity in
X=A+D from `../proshka/PROSHKA_VERDICT_GOAL058_FIRST_OMITTED_COMPRESSION_2026-09-26.md`
(10)-(15) yields W(p_m,p_m)->W(f,f). The reviewer checked those continuity
bounds as part of this pass. This X is NOT the different Sept12 integrated
translation-energy Hilbert norm. No whole-line H1 derivative is asserted.
The full Sept25 crosswalk (C) gives W(p_m,p_m)=x_m* K_m x_m and
||x_m||2=||p_m||2->||f||2; its basis exp(2 pi i n(t+L/2)/L)/sqrt(L)
is exactly our phased basis. No odd-sector or pole-removed matrix is used.

3. If lambda_min(K_m)>=-delta_m, delta_m->0 on the original cofinal
schedule, then W(p_m,p_m)>=-delta_m||p_m||2^2; passing to the limit gives
W(f,f)>=0 for every complex compact smooth test. The classical full Weil
criterion gives RH, as recorded in `../../Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md:37-45`.
That reference supplies only the terminal criterion here, not the X norm.

Finally let P0 be the ENTIRE bottom projector and rho=||P0 g_m||. The exact
spectral identity |lambda_min|rho=||P0 K_m g_m||<=epsilon proves the proposed
conditional chain. It suffices that on every sufficiently late NEGATIVE
bottom cell rho>0 and epsilon/rho->0 (define delta=0 on other cells).
Any fixed c>0,A<infinity with rho>=c m^(-A) on negative cells is sufficient
by item1. If negative cells are eventually absent, positivity is immediate.
No simplicity, evenness of bottom, gap, or near-unit overlap is required.
A wholly odd negative bottom has rho=0 and remains a possible obstruction;
evenness of g is NOT permission to exclude it. The lower-overlap theorem
is OPEN. Neither the old G1/G3 chain nor any terminal RH goal is closed.

## Exact next question (10/10)

Sent 2026-10-06 about20:10 Europe/Berlin in the same chat. Full question
visible in the destination with Stop control and active server status;
browser stream disconnected while awaiting the answer. Do not resend.
This is a bounded exploration of a cheaper consumer, not silent admission
of a new terminal chain. The negative-bottom qualification avoids imposing
overlap where the matrix is already nonnegative.

Continuation 10/10. Answer9 is fully processed. This is the final bounded exploration of the SAME actual CCM source family after the recorded direct-theta localization stall; do not silently switch matrices, drop prime powers, or claim the old G1/G3 chain closed.

Independent checks accepted your exact variation, all signs in (3)-(5),(12), and the half-leakage counterexample (6)-(11). The latter kills ONLY uniform carrier-wide projection repair: x_m is not a bottom vector. The constant6 edge split is valid. Direct P_m(Gf) localization is STALLED at its full signed defect.

Our own additional attempt pays only one term: from |G(t)|<=D0 exp[-(pi/2)e^(2|t|)], sup_t |G(t)G(t+log n)|<=D0^2 e^(-pi n). Thus for the full prime shift operator P_I=sum Lambda(n)/sqrt(n)(T_log n+T_log n*), ||M_G P_I M_G||<=2D0^2 sum Lambda(n)n^-1/2 e^-pi n, uniformly in m. This controls the cross term in (G(t+s)-G(t))^2 only, not its endpoint-G^2 terms or projection correction. It gives no sign.

A possibly much cheaper terminal obligation emerged. Please test and ATTACK IT rather than continue the failed multiplication variation or the almost-unit overlap OS. Keep the literal full Hermitian K_m on |n|<=m, L=log m, N=m, original m_j=preAnchorTailStart(P)+j+2, and the exact normalized WINDOW row g_m=c_m(G)/sigma_m. Let P0,m be the orthogonal projector onto the ENTIRE bottom eigenspace (no simplicity/parity assumption), epsilon_m=||K_m g_m|| and rho_m=||P0,m g_m||.

Exact algebra, needing no gap:
  |lambda_min(K_m)| rho_m=||P0,m K_m g_m||<=epsilon_m.
Therefore a lower bound on rho may suffice even if it tends to zero. The minimal proposed target is:
  whenever lambda_min(K_m)<0, rho_m>0 and epsilon_m/rho_m ->0
on the original eventual family. A fixed-polynomial lower bound rho_m>=c m^-A, c>0 and fixed finite A, only on those negative-bottom cells, would suffice using the residual below. This requires neither rho->1 nor simplicity nor exclusion of every source-null vector within a degenerate bottom space. It cannot assume away a purely odd negative bottom, since then rho=0 exactly.

Available actual-source residual proof, already on our shelf (not a spectral assumption):
For each fixed derivative order, G is smooth, even and has Gaussian log tails; its endpoint derivative jumps are polynomial(m)e^-pi m. Repeated integration by parts retaining these jumps gives for the WINDOW projection p_m of G:
  ||p_m-G||_L2(I)+||(p_m-G)'||_L2(I)+sum_edge |p_m-G|=O_R(m^-R)
for each fixed R, with derivative order chosen large enough, no uniformity in growing R. The full mixed-form estimate against ANY unit finite synthesis f is
 |W(e-t,f)| <= (2+4L)sqrt(m)||e||2 +26||e'||2
    +26 D_e sqrt(3m/L)+tau_G(m),
 e=p_m-G|I, t=G 1_(I^c),
 tau_G=2m^(1/4)A_G+2sqrt(m)S_Lambda T_G
       +26||G'1_(I^c)||2+26(|G(-L/2)|+|G(L/2)|)sqrt(3m/L),
 A_G=int_(I^c)e^(|t|/2)|G(t)|dt,
 T_G=||e^|t| G 1_(I^c)||2,
 S_Lambda=sum_(n>=2)log(n)n^-3/2.
All terms of tau_G are polynomial(m)e^-c m. The global radical W(G,f)=0 and sigma_m->||G||2>0 thus give epsilon_m=O_R(m^-R). Our Sept25 independently checked proof already gives epsilon->0; this fixed-order strengthening is explicitly derived in ODD_TRIAL_SIGN on our shelf and is being checked separately, not assumed from small Rayleigh values.

Own proposed consumer check:
For arbitrary fixed complex f in C_c^infinity(R), eventually support(f) lies inside I. Its projection f_m on these same modes, zero-extended, satisfies for Omega=2pi m/L
 ||f-f_m||2=O_q(Omega^(1/2-q)),
 ||(f-f_m)'||_L2(I)=O_q(Omega^(3/2-q)),
 ||f-f_m||_infinity,I=O_q(Omega^(1-q)).
Weighted A(e)=||e^|t|e||2<=sqrt(m)||e||2, and the zero-extension jump estimate ||e(.+h)-e||2<=h||e'||2+C sqrt(h)||e||infinity imply convergence in X with norm A(e)+sup_(0<h<=1)h^-1/4||e(.+h)-e||2. Our already checked full-Weil continuity on X retains both poles and ALL prime powers. Consequently W(f_m,f_m)->W(f,f), with W(f_m,f_m)=coeff(f_m)* K_m coeff(f_m). If lambda_min>=-o(1), every compact smooth complex test has nonnegative full Weil form, and Weil's criterion would give RH. This short full-carrier extension is under independent check; identify any real normalization/domain error, but do not spend the whole answer merely repackaging this conditional algebra. We have NOT declared a new proved terminal consumer or changed the source family.

MAIN TASK: find an actual-source proof of the weaker lower-overlap condition (polynomial lower norming weight would be enough) on negative-bottom cells, or a rigorous obstruction to it. Use our exact theta source, full matrix equations, spectral measure/norming-constant aliases or another concrete source-specific mechanism, with literature checked where relevant. Small residual alone does not lower-bound rho; abstract cyclicity without a quantitative bound does not suffice; real-space sign of G does not authorize PF for a signed Weil matrix; a global inverse-gap/complement floor or all-profile positivity PREMISE would be circular. A proof of the lower overlap would be a new substantive theorem, not bookkeeping.

The bounded current literature check found CCM §8 still leaves G1/tracking open; Andrade's scalar Herglotz criterion retains its uniform scalar inequality; Groskin v4 2605.20224 has finite-matrix identification and numerical cross-cutoff overlaps, not this theorem. They are not suppliers.

If the weaker attack stalls, state the precise actual-source signed/norming quantity left uncontrolled and whether this weaker consumer is genuinely usable; distinguish a proved obstruction from lack of proof. Do not invent a new sufficient wrapper as a result. No Lean or repository edits; RH remains OPEN.
