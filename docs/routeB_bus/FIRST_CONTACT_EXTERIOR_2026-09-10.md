# First-contact triage after SATURATION: the exact exterior defect

Status: PAPER derivation, independently checked. This is not a lower-sign supplier or RH proof.
Base: 5ba4ea72a19fea87b881d919e3fe5f03ac065ec8, branch rh_clean.
Scope: derive the exact exterior equation for a compact-window null vector and test whether the SATURATION radical family adds an independent constraint. No Lean, numerical computation, production admission, or Proshka dispatch.

## Source and convention lock

1. docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.md: (Q), (RAD), (GS), (NEG-MEASURE), (DOM).
2. docs/routeB_bus/AGENT_REPORT_2026-09-05_GOAL058_XIDEV_INDEPENDENT_AUDIT.md, section 2: independent signed-ground-state audit.
3. docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCREW_HYPERBOLICITY_HODGE_2026-09-08.md: H16-H17 and the local/global radical warning.
4. docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SATURATION_2026-09-10.md: A1-A5, A24-A28, A31-A40.
5. docs/routeB_bus/SATURATION_INDEPENDENT_CHECK_2026-09-10.md.

The historical raw Phi in source 1 is twice the raw Phi in source 4. The unit positive profile f0 is invariant under that factor; the formulas below use the literal form Q, not a silently rescaled raw source.

Write alpha(t)=exp(-t/2)/(1-exp(-2t)), cA=gamma+log(8*pi)+pi/2, wn=Lambda(n)/sqrt(n), Mplus(v)=integral v(y)exp(y/2)dy, Mminus(v)=integral v(y)exp(-y/2)dy. The Hermitian pairing B is antilinear in its first argument and Q(v)=B(v,v):

Q(v)= integral_0^infty alpha(t)||v(.+t)-v||_2^2 dt -cA||v||_2^2
      +2 Re(Mplus(v) conjugate(Mminus(v)))
      -2 sum_(n>=2) wn Re integral conjugate(v(x))v(x+log n)dx.

Let a>0 and let v be in the compact-window form domain, supported in [-a,a]. Its zero extension is the same v. No H1_0 endpoint assumption is imposed. A local null vector means B(h,v)=0 for every h in that window form domain, equivalently kernel of its Friedrichs operator at eigenvalue zero. No global null assertion follows by definition.

## E1. Distributional equation tested strictly outside the window

For x>a define, almost everywhere,

R_a[v](x)= exp(x/2) Mminus(v) + exp(-x/2) Mplus(v)
           - integral_(-a)^a alpha(x-y)v(y)dy
           - sum_(n>=2) wn v(x-log n).                         (E1)

For every h in C_c^infty((a,infinity)),

B(h,v)=integral conjugate(h(x)) R_a[v](x)dx.                   (E2)

This statement holds for every compact-window form-domain v, not just a null vector. On each compact subset of (a,infinity), alpha(x-y) and its derivatives are uniformly bounded for y in [-a,a]; v is L1 there by Cauchy-Schwarz. The prime sum has only finitely many contributing n on such a compact set: exp(x-a)<=n<=exp(x+a). It is a locally L2 function; equality is an almost-everywhere statement, not point evaluation of an L2 representative.

Derivation: expand the translation-energy pairing. Its off-diagonal terms on disjoint supports are -integral alpha(|x-y|) conjugate(h(x))v(y) dxdy. The diagonal terms vanish. Polarizing the prime correlation yields both shifts, with coefficient -wn each; v(x+log n)=0 for x>a. Polarizing the pole term gives exp(x/2)Mminus(v)+exp(-x/2)Mplus(v). All pairings are absolutely justified for these separated supports; the remaining count of primes is finite. No extra factor 2 multiplies the kernel in (E1).

## E3. The zeroth geometric term cancels exactly with one pole

Put M_j(v)=integral_(-a)^a exp((2j+1/2)y)v(y)dy, j>=1. Since

alpha(x-y)=sum_(j>=0) exp(-(2j+1/2)(x-y)),

(E1) becomes

R_a[v](x)= exp(x/2)Mminus(v)
           -sum_(j>=1) exp(-(2j+1/2)x) M_j(v)
           -sum_(n>=2) wn v(x-log n), x>a.                    (E3)

The j=0 term is exactly exp(-x/2)Mplus(v), with opposite sign to that pole. The geometric series and all of its x derivatives converge uniformly for x>=a+delta, delta>0, using |M_j|<=||v||_1 exp((2j+1/2)a). Thus the nonarithmetic part is analytic strictly outside the window. The shifted prime part need not be analytic. No prime-number theorem or RH estimate is being used. The other pole Mminus(v) remains, unless a separate moment-null hypothesis is supplied.

For even v the left exterior defect is the reflection of the right one; general v requires both sides. SATURATION's V_lambda are even, so even-family tests do not certify the odd sector.

## E4. Radical-tail tests are automatic consequences of the local null equation

Let r be a global B-radical in E such that r_in=1_[-a,a]r belongs to the window form domain V_a. Then r_out=r-r_in belongs to the global space E by linearity; it is not an element of V_a. SATURATION's r=V_lambda meet the cut hypothesis by A5, for each fixed lambda>=1. If v is a local null vector, then

B(r_out,v)=B(r,v)-B(r_in,v)=0-0=0.                           (E4)

Thus every such Bessel-radical exterior orthogonality relation is already implied by the local null equation and the established global radical property. No positivity, asymptotic estimate, or a->infinity limit enters E4. Small E-norm of selected r_out is an upper bound and cannot turn E4 into a lower bound for a fixed nonzero v.

This does not prove that a future completeness/unique-continuation argument is impossible. It identifies the additional theorem it would need: enough exterior tests, with a proved domain/topology transfer, to deduce R_a[v]=0 on both exterior half-lines from these automatic relations. Local interior shell density from SATURATION A5/A6 does not assert this exterior statement. No such completeness claim is made here.

## E5. A one-window algebraic falsifier, not a theta counterexample

For 0<epsilon<=1 on complex C^3 set

Q_epsilon(x,y,z)=2 Re((epsilon*x-y) conjugate(z)),
A_epsilon=[[0,0,epsilon],[0,0,-1],[epsilon,-1,0]].

The eigenvalues are 0 and +/-sqrt(1+epsilon^2), so ||A_epsilon||<=sqrt(2). Its radical is span{(1,epsilon,0)}. Let X=span{e1} be the window subspace and Y=X-perp. The compression to X is the zero nonnegative form and its local kernel is all of X. Projection of the global radical onto X is surjective, although the global radical has zero intersection with X. For r=(1,epsilon,0), r_in=e1 has unit physical normalization and zero energy, whereas ||r_out||=epsilon and B(r_out,e1)=0. Nevertheless B(e3,e1)=epsilon is nonzero, and Q_epsilon(0,1,1)=-2.

Every identity follows by direct multiplication; the characteristic polynomial is t*(t^2-1-epsilon^2). Thus a small radical tail, full interior projection, bounded form norm, nonnegative local compression and exact cut energy zero do not by themselves imply local-to-global nullity or global lower sign. This is a family of one-window algebraic counterexamples. The form changes with epsilon; this is NOT a single source form with a cofinal nested family, not a first-contact source counterexample, and not a refutation of a future theorem using the actual arithmetic kernel. It lacks the prime shifts, the theta source and the true window evolution. Its role is only to reject a general one-window argument that spends none of those additional facts.

## Decision and remaining concrete object

- Do not repeat the positive-Phi transform as a new sign mechanism: source 1 already proves its exact signed form, negative-measure interval, and remaining DOM.
- Do not dispatch 'SATURATION tails annihilate a first-contact mode' as a new sign result: E4 is automatic. A claimed quantitative completeness theorem would be new and must be proved separately.
- The explicit object for a next bounded source investigation is E3, coupled to the original window equation and nonnegativity of the exact window form. The missing implication is from that local equation to a usable restriction on the exterior defect. Merely renaming this implication as unique continuation does not solve it.
- No endpoint regularity, global E-density, exterior density, even-to-odd reduction, or production node admission is asserted.

Prediction frozen before independent audit: p=0.90 that E1-E4 survive with at most normalization/domain corrections; p=0.85 that the SATURATION-tail relations alone add no independent sign condition. Outcome not yet recorded.

## Independent audit and parent check — 2026-09-10

One native terra/xhigh checker read the definitions and E1-E5. Initial pass: no incorrect assertion; one WORDING fix made explicit that r_in belongs to V_a while r_out belongs to global E. Final exact draft SHA25626f3ee6716e87249751f6519f36c470763153f7cfd454b34bb4a6d843bb54f17 (8125bytes,85lines) received two consecutive clean full-text passes F1/F2; FIRST_INCORRECT_ASSERTION NONE_FOUND. No unresolved substantive findings. The accepted source/formula scope is exactly the draft above; this receipt and status change add no mathematical assertion.

Parent separately checked the pole cancellation and E5 symbolic matrix identities; /tmp/q3_first_contact_parent_exact.log reports exact characteristic polynomial t*(t^2-1-epsilon^2), exterior coupling epsilon and negative witness -2. This algebra is also written out in E5; it does not certify the theta source's sign. No numerical experiment, kernel proof, outside-density theorem, or first-contact exclusion was performed.

Both frozen audit predictions are CONFIRMED at their stated scope. The first p=.90 prediction concerns E1-E4, including the domain wording repair; the second p=.85 concerns the automatic relation E4 only. RH remains unproved; PX_RH_CLAIM NOT_MADE and the production HOLD remain unchanged.
