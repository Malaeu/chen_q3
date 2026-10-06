# Boundary-return stall and direct source stability

Source: complete answer 7/10 in
`PROSHKA_BOUNDARY_SIGN_STRIP_RESPONSE_INLINE_2026-10-06.md`.
This note accepts only the bounded results below. OS, G1, G3 and RH remain OPEN.

## Checked scope of the pointwise obstruction

Independent read-only researcher `/root/answer7_boundary_audit` checked
the full inline argument against the inherited mass and projection estimates.
For EACH FIXED shift 0<s<=L, its real symmetric two-column density is
`D_s(t)=-(a(t)b(t+s-L)^T+b(t+s-L)a(t)^T)`.
Its determinant is minus the square of the two-column determinant.
The latter is a nonzero real analytic function: otherwise continuation,
periodicity of the projected trigonometric polynomials, Gaussian decay,
and G''/G -> +infinity contradict each other along t=t0+nL.
The full theta-source derivative polynomial and rational division were checked.
Nonzero p0 follows explicitly from ||rho0||>=sqrt(mu)/2 and
||rho0-p0||<=D=o(sqrt(mu)); it is not inferred from a finite numerical cell.

Therefore each fixed-shift density is indefinite except at isolated points.
This kills TERMWISE pointwise positivity for nonzero real weights only.
It does NOT prove that the summed signed arithmetic density is indefinite:
indefinite matrices may sum to a positive semidefinite matrix.
It does not decide the integrated inequality or prescribed U.
At s=L the indefinite density integrates to zero by projection orthogonality.

## Exact cancellation and error accounting

For X=1_I g_z, p=PX and T=V-B, the full symmetric Fourier projector
commutes with V. Thus with F_mu=T X+e_mu,

    F_p-C_p = 2 Re<p,Tp> + 2 Re<p,e_mu>.

The complementary-source terms cancel exactly. No signed gain has appeared.
The forcing error costs at most 8 C_X Jmath/mu relative to Ehat.
Independently, replacing rho by p in the ORIGINAL self-correlation costs
8 A D(2 C_X+D)/mu=o(1/m), as in answer (7). This direct replacement needs
no extra forcing error; a derivation via F_p-C_p must keep its forcing error.
Low-range and endpoint terms remain unchanged. The integrated bound (8)
and U>B_m on an unbounded original subsequence remain OPEN.

## Recorded stall and next single obligation

The Mobius-forcing/boundary-return rewrite is STALLED: restoring the
complement reproduces the original unknown band self-correlation.
This is not a kill of source transfer or of U. Suspend these rewrites until
a new signed joint-correlation input is available.
Continue within SOURCE_TRANSFER with the original reference qhat=zhat/Z,
zhat=z(c0,c4), same full K_m and same fixed-port eventual schedule.
The proposed target for EVERY v in ker(K_m-lambda_min(K_m)I) is

    ||v-qhat<qhat,v>|| <= C m^(-1/4)(log m)^A |<qhat,v>|.   (OS)

OS is an UNPROVED target, not a new supplier or a reason to write a Lean receiver.
Its all-vector quantifier is essential; controlling one chosen bottom vector
does not exclude a source-null degenerate bottom direction.
Independent read-only explorer `/root/answer7_os_crosswalk` checked the
conditional chain against SOURCE_TRANSFER (T1)-(T6), with no algebraic finding:
Z>0 is inherited eventually from T5; OS makes the source functional injective,
hence the nonempty bottom space is one-dimensional. For its unit vector,
alpha<=epsilon/sqrt(1+epsilon^2), epsilon=C m^(-1/4)L^A.
The SAME K is used to transfer to the selected row:
beta_sel<=alpha+4E/Z. Its center floor L|qsel_0|^2>=cCenter and
sqrt(L) beta_sel->0 exclude an odd ground line, without assuming qhat even.
Reflection commutation is `CCMFiniteWeilParity.lean:67-117`.
The subsequent realification and eta nonvanishing are in
`G6N1SelectedFerrersGroundParityRealification.lean:213-285` and
`CCMFiniteWeilEtaNonzero.lean:82-188`; eta normalization is a CONSEQUENCE
after simple even ground, never a premise of the OS proof.

The unchanged trial-centered multiplier Xi(0)/T(qsel,0) is nonzero.
With fixed H<1/2, the tracking error is bounded by a constant times
m^(H/2)sqrt(L)(alpha+4E/Z)->0. The ground transform need not equal Xi(0)
exactly at zero: the same nonzero scalar preserves its zeros, and the error
tends to zero. Accepted HMODE/chi/G4 remain explicit matched inputs.

Formalization caveat: current tracked-ground Lean constructors consume hfloor,
not OS. A proved OS would need a new adapter for this same literal source row,
ground projector, parity/realification, zero-set crosswalk and T3 tracking.
No current Lean theorem or full assembly is promoted by this conditional audit.

## Root attempt on the literal bottom eigen-equations

The source identity is already in
`q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean:374`:
with D=diag(n), eta_n=1 and beta_n=n K_(n,0),

    [D,K]=beta eta* - eta beta*.

Let Kv=lambda0 v for ANY bottom vector; no simplicity or parity assumed.
Write s=eta*v, b=beta*v, t=(D eta)*v, u=(D beta)*v. Then exactly

    (K-lambda0)Dv = eta b-beta s,
    <Dv,(K-lambda0)Dv> = Re(conj(t)b-conj(u)s) >= 0.

The second identity follows by expanding [D,[D,K]] and using Kv=lambda0 v.
Its nonnegativity uses only that lambda0 is the lowest eigenvalue of the
same finite Hermitian K. If s=b=0, Dv is again a bottom vector.
This preserves the full prime-power source through beta and K.
The literal K entries are W02-WR-Prime in
`CCMFiniteWeilSourceMatrixN1.lean:40-60,89-104`; the diagonal Q branch is
separate and Mangoldt is summed over all integers 2..mProject.
Here mProject=N=m_j=preAnchorTailStart(P)+j+2.
The existing stronger identity T Dxi=-beta in
`CCMFiniteWeilShiftedRankOne.lean:127-154` assumes evenness and eta
normalization, so it cannot be used upstream to prove OS.

This attempt gives necessary signed moment relations, not OS: the source
coordinate qhat*v is neither s nor b, and no uniform estimate of the
remaining component has been obtained. Reflection and displacement rank
alone cannot fill the gap. A nontrivial existing exact control is
`CCMProposition59ComplexTrialComplementFloor.lean:181-246`:
D=diag(-1,0,1), K=all-ones, eta=(1,1,1), beta=(-1,0,1).
It has the same nonzero rank-two commutator and reflection but a two-dimensional
bottom space. Its displayed unit Q and nonzero Y obey Q*Y=0 and KY=0.
Root read the definitions and identities; no fresh Lean run was needed or claimed.
Do not turn this into a global inverse bound on qhat-perp or replace the
original bottom space by a convenient numerical branch. The next attack
must use additional structure of the actual beta and matched Robin source.

## Bounded alias return

Researcher `/root/os_source_alias` found no verified OS supplier in its bounded
search. Three shelf queries had q3_docs freshness INCOMPLETE, not absence.
CCM arXiv:2511.22755v1 Lemmas 5.2/5.4 provide the exact displacement mechanism,
but 5.4 assumes the simple-even ground OS is supposed to establish.
Beckermann--Townsend, https://arxiv.org/abs/1609.09494, controls matrix singular
values via displacement structure under separated spectral-set hypotheses.
For this commutator A=B=D, the spectral sets coincide; additionally such singular
values are not bottom-source overlap. Rejected as a supplier, not a theorem refutation.
Fetched Beckermann--Townsend PDF SHA-256:
33fe4f97417ba4afe8a9c42c0589708c232687f4905e36694560ecdc663606c0.

## Exact question 8/10

Sent once via send_message_to_thread to the same chat at 18:43 Berlin.
The tool returned success; subsequent chat status is active. The browser
readback after reload displayed the full distinct question8 and Proshka's
active response directly addressing the Robin/Ferrers source coordinate.
Initial API readback still showed the preceding turn; no new message ID is
asserted here. Do not resend because of that observation lag.

Continuation 8/10. Answer7 has been processed; continue ONE source-transfer attack, now the all-bottom-space OS obligation at the quarter-power rate, on the original matched family.

Audit disposition: your fixed-shift density determinant/analyticity argument and forcing-return cancellation checked out. Scope correction: indefiniteness is proved for EACH INDIVIDUAL shift density with nonzero real weight; it does not imply indefiniteness of the summed arithmetic density. The integrated sign and prescribed U remain OPEN. We recorded the Mobius/boundary-return rewrite as mathematically STALLED, not source transfer killed. Do not continue that sequence of rewrites absent a new signed joint estimate.

The OS implications were independently checked: for every bottom vector, injectivity of qhat* gives simplicity; T1-T6 transfer to the same selected qsel; nonzero selected center and reflection give evenness without assuming qhat even; the unchanged trial-center multiplier and m^(-1/4)(log m)^A suffice on every fixed H<1/2. Z>0, matched HMODE/chi, center floor and all T1-T6 remain explicit. Current Lean ground constructors still take hfloor, so a future proved OS needs a new adapter; no proof supplier exists yet.

Own attempt on the LITERAL source equations:
mProject=N=m_j=preAnchorTailStart(P)+j+2; K entries are W02-WR-Prime, keeping the separate diagonal branch and Mangoldt at all integers 2..m (all prime powers).
D=diag(n), eta_n=1, beta_n=n K_(n,0), so
[D,K]=beta eta* - eta beta*,
K_nm=(beta_n-beta_m)/(n-m) for n!=m.
For ANY v in ker(K-lambda0 I), with no parity or simplicity,
s=eta*v, b=beta*v, t=(D eta)*v, u=(D beta)*v,
(K-lambda0 I)Dv=eta b-beta s,
<Dv,(K-lambda0 I)Dv>=Re(conj(t)b-conj(u)s)>=0.
If s=b=0, Dv is again bottom. These retain the true full source. They still do not control qhat*v: qhat=z(c0,c4)/Z is neither eta nor beta.

We checked the existing nontrivial negative control: D=diag(-1,0,1), K=all-ones, eta=(1,1,1), beta=(-1,0,1) obey exactly the same rank-two commutator and reflection, but bottom has dimension2. Thus neither structural commutation nor reflection alone can prove OS. The stronger source identity T Dxi=-beta (CCM Lemma5.4) assumes simple-even ground and eta normalization; using it upstream would be circular. Use the unspecialized equation above instead.

Bounded alias return: three shelf queries INCOMPLETE, not absence. CCM's own displacement formulas are the closest exact partial mechanism. Beckermann-Townsend arXiv:1609.09494 singular-value bounds for displacement matrices are not a supplier: their separated spectral sets fail for A=B=D, and matrix singular-value decay is not bottom-source overlap. Do not import it.

Please perform the next concrete mathematical attack on:
for ALL v in ker(K_m-lambda_min(K_m)I),
||v-qhat_m<qhat_m,v>|| <= C m^(-1/4)(log m)^A |<qhat_m,v>|,
with fixed C,A for the matched port and all sufficiently late original j.
Derive an ACTUAL source estimate from the literal bottom eigen-equations together with the exact Robin/Ferrers definition of qhat. A discrete Green/boundary or displacement formula is useful only if the link to this source coordinate is proved before using any simplicity/parity-normalized identity. Source-null bottom exclusion is a meaningful component if it is genuinely proved, but one convenient eigenvector or a chosen numerical branch is insufficient.

Do not spend the answer restating OS consequences, inventing another spectral-projector/heat-trace/resolvent sufficient wrapper, or proving a generic norm identity. We need new signed/oscillation control for the actual source, with all constants/error scales paid. If a concrete attempt fails, identify the first explicit actual-source inequality it cannot prove and any rigorous obstruction, without declaring OS or B false from finite cells. No global positive floor on qhat-perp or RH-equivalent positivity may be smuggled in. No Lean or repository writes.
