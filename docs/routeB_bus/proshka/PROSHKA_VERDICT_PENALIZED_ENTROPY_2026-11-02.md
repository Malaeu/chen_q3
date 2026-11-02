# STATUS: TRY_PENALIZED_ENTROPY_UNIFORM_RESPONSE
```yaml
OPERATIVE_CLASS: TRY_PENALIZED_ENTROPY_UNIFORM_RESPONSE
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_DISCUSSION_OF_PENALIZED_MINIMA_AND_COMPETITOR_TRANSPORT
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_V_COMMIT: f73901ce86043a9aa98c3882497a405c58c0a146
SOURCE_V_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_PHASE_SPACE_V_2026-11-02.md
SOURCE_V_SHA256: 4491558db031348336e78a81229fefe941de817240dc61636906fb7fa4dffb26
SOURCE_V_GIT_BLOB: 5a6ddc3b7de2bc46199bea691983e90a589f92eb
SOURCE_NOESCAPE_COMMIT: 167dff63a632f170fed2d01d88af61268ad0af7f
SOURCE_NOESCAPE_GIT_BLOB: 453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc
CARRIER: LITERAL_CCM_EVEN_N_EQUALS_M_L_EQUALS_LOG_M
RESULT: EXACT_PENALTY_RESPONSE_AND_GAP_FREE_APPROXIMATE_BOTTOM_BRIDGE
ZERO_PENALTY_RIGHT_SLOPE: MINIMUM_V_ON_TRUE_BOTTOM_EIGENSPACE
MONOTONICITY_OF_VALUE_IMPLIES_UNIFORM_SLOPE: FALSE_IN_GENERAL
SHRINKING_PENALTY_PATH_IMPLIES_BOUNDED_V_OF_TRUE_BOTTOMS: FALSE_IN_GENERAL
SHRINKING_PENALTY_EXCESS_BOUND_IMPLIES_RH: PROVED_ON_PINNED_SUPPLIERS
COMPACT_REWARD_SHRINKING_PATH_IMPLIES_RH: PROVED_ON_PINNED_SUPPLIERS
LITERAL_SOURCE_UNIFORM_PENALTY_EXCESS: NOT_PROVED
LITERAL_SOURCE_COMPACT_REWARD_LOWER_RESPONSE: NOT_PROVED
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ADDITIONAL_PROGRESS: GAP_FREE_ENERGY_DEFECT_TRANSFER_AND_SCOPED_FALSE_INFERENCE_CONTROLS
COGNITIVE_OPERATOR: DUALIZE
EXACT_CONTROL_GROUPS: 6
NEW_LITERAL_NUMERICAL_SCAN: false
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
```

## 0. Decision

The penalty proposal is mathematically useful, but monotonicity of a minimum in window size does not control its sensitivity to a vanishing penalty. The correct scalar object is the normalized penalty excess, not the penalized minimum alone. A weaker sufficient interface is available: compact, asymptotically energy-minimizing competitors suffice for RH; they need not converge to each cell's exact ground vector. This avoids demanding uniform spectral gaps or differentiation of eigenvectors.

No uniform arithmetic estimate is proved in this report. All finite-dimensional statements below are proved for the unchanged literal matrices; the cofinal implications explicitly use the pinned NOESCAPE suppliers. Abstract counterexamples are not identified with CCM.

## 1. Sources and imported boundaries

S1. PHASE_SPACE_V at the commit and blob in the header, particularly Sections 2, 3, 5 and 7. Its local bytes were hashed and agree with the fetched Git blob. The fixed physical functional is

V[f] = A_arch[f] + integral log(1+x^2)|f(x)|^2 dx,

A_arch[f] = integral_0^infinity j(s)||f-T_s f||_2^2 ds,

j(s)=exp(-s/2)/(1-exp(-2s)). Its bounded unit sublevels are relatively compact in physical L2. It is not known to be monotone or uniformly bounded on exact CCM bottoms.

S2. NOESCAPE on 167dff63a632f170fed2d01d88af61268ad0af7f. L1-L2 supply r_m=P_m r -> r and ||A_m r_m|| -> 0 for every fixed finite even theta combination r; these r are dense in even L2. The separate even negative-witness return gives, under not-RH, lambda_min(A_m)<=-nu for all sufficiently large original m, for a fixed nu>0. L16-L18 identify a nonzero weak component and a fixed compact phase-space observer. These are inherited PAPER inputs, not reverified analytic suppliers here.

E1. G. Perelman, The entropy formula for the Ricci flow and its geometric applications, arXiv:math/0211159, Sections 1 and 3, especially (3.3)-(3.4). The Ricci metric, conjugate heat density and shrinking tau evolve together. The square formula is a derived identity for that coupled system, not a consequence of merely taking an infimum. PDF page 9 was inspected by web screenshot; equations (3.3)-(3.4) were read in parsed text. URL: https://arxiv.org/pdf/math/0211159

E2. P. Milgrom and I. Segal, Envelope Theorems for Arbitrary Choice Sets, Econometrica 70 (2002), 583-601, Theorem 1 and Corollary 4. These explain derivatives of a value function without differentiating its optimizers. The needed finite-matrix result is proved below. PDF parsed text was read; the screenshot attempt returned Cache miss and is not counted as visual verification. URL: https://milgrom.people.stanford.edu/wp-content/uploads/2002/03/Envelope-Theorems.pdf

E3. H. Attouch, A. Balhag, Z. Chbani and H. Riahi, Damped inertial dynamics with vanishing Tikhonov regularization: strong asymptotic convergence towards the minimum norm solution, arXiv:2108.00203, Introduction and assumptions. This is a comparison with hierarchical selection for a fixed convex problem. Its dynamical theorems are NOT imported for our indefinite quadratic form on a unit sphere or uniformly in expanding carriers. URL: https://arxiv.org/abs/2108.00203

A sign correction to the motivating analogy: gradient descent has dF/dt=-||grad F||^2. Perelman's nonnegative formula uses his coupled evolution and conventions. Existence of an envelope derivative does not determine its sign.

## 2. Exact finite-carrier penalty theorem

**[FINITE_CELL | PAPER.]** Let A=A* be a finite-dimensional Hermitian matrix, B=B*>=0, lambda=min spec A and E=ker(A-lambda I). Define

mu(eps)=min_{||f||=1}(<Af,f>+eps<Bf,f>), eps>=0,

v_0=min_{f in E, ||f||=1}<Bf,f>.

For literal CCM, A=A_m and B=B_m is the exact matrix of S1's V in the same orthonormal carrier. No modes or source terms are changed. The penalized matrix is an auxiliary problem only.

Then mu is nondecreasing and concave in eps, mu(0)=lambda, and

(2.1)  mu'_+(0)=v_0.

For eps>0 define q(eps)=(mu(eps)-lambda)/eps. Then

(2.2)  0<=q(eps)<=v_0; q is nonincreasing in eps;
       lim_{eps downarrow 0}q(eps)=v_0.

For every normalized penalized minimizer g_eps, with

d_eps=<Ag_eps,g_eps>-lambda>=0,

one has the exact identity

(2.3)  q(eps)=<Bg_eps,g_eps>+d_eps/eps,

hence

(2.4)  <Bg_eps,g_eps><=q(eps),  d_eps<=eps q(eps).

Proof. Mu is the infimum of affine functions of eps, with nonnegative slopes. A true ground vector minimizing B gives mu(eps)<=lambda+eps v_0. The lower bound <Ag,g>>=lambda yields (2.3)-(2.4) and <Bg_eps,g_eps><=v_0. For fixed A, compactness of the unit sphere and d_eps<=eps v_0 show every limit of g_eps lies in E. Its B value is at least v_0, so (2.1)-(2.2) follow. Concavity gives the asserted secant monotonicity. No simple eigenvalue and no gap denominator were used. QED.

At an arbitrary eps with degenerate penalized ground space, the right derivative is the minimum of B on that ground space; the left derivative is its maximum. This is the finite-envelope guard, not a choice of an arbitrary eigenvector.

**[COFINAL_FAMILY | PAPER, exact equivalence of proposed budgets.]** For any chosen unbounded original set M and any fixed eps_0>0,

(2.5)  sup_{m in M}V_m<=C
       iff 0<=mu_m(eps)-lambda_m<=C eps
       for all m in M and 0<eps<=eps_0.

Here V_m is the minimum V on the exact bottom eigenspace defined in S1. Thus the penalty replaces inverse-gap formulas by an epsilon-response problem; it does not supply the uniform response estimate.

## 3. Window monotonicity and its missing mixed estimate

**[ABSTRACT | PAPER, conditional only on the pinned closed full-window realization.]** For the full even form at N=infinity, let

mu(L,eps)=inf_{||f||=1, supp f subset I_L}(k[f]+eps V[f]).

At each fixed L the additional physical logarithmic potential is bounded on I_L, and multiplying the archimedean form by 1+eps preserves its form domain. The previous attainment and compactness proof applies. Since full support domains are nested and neither k nor V changes on a fixed zero-extended function,

(3.1)  L2>=L1 implies mu(L2,eps)<=mu(L1,eps).

This includes eps=0. It does not imply monotonicity of the difference mu(L,eps)-mu(L,0), nor a bound for its epsilon slope. Literal N=m Fourier carriers are not nested under changing L. Equation (3.1) must not be silently applied to their diagonal schedule.

A sufficient mixed transport law on the literal dyadic cells m_k=2^k is

(3.2)  [mu_{m_{k+1}}(eps)-mu_{m_k}(eps)]
       -[lambda_{m_{k+1}}-lambda_{m_k}] <= eps a_k,
       a_k>=0, sum_k a_k<infinity,

for all sufficiently small eps>0. Dividing by eps and telescoping, then using (2.2) at the fixed initial cell, gives sup_k V_{m_k}<infinity. This is sufficient, not established.

Crucially the loss in (3.2) must be O(eps). An error r_k independent of eps becomes r_k/eps and cannot be passed to eps=0, however small r_k is at the chosen m. A source estimate allowing just a selected shrinking eps_m can instead use Section 5; it need not prove (3.2) for every eps.

## 4. Exact falsifier of the proposed free conclusion

**[ABSTRACT | PAPER; not CCM.]** On ell2 take u=e_0, A e_0=0 and

A e_j=(-1+1/(j+1))e_j, B e_j=(j+1)e_j, j>=1,
B e_0=e_0.

Let A_m,B_m be principal restrictions to span(e_0,...,e_m). These carriers are nested, B has compact unit sublevels, and Au=0 exactly. Nevertheless

lambda_m=-1+1/(m+1), bottom=e_m, V_m=m+1 -> infinity.

The penalty minimum is

(4.1) mu_m(eps)=min{eps, min_{1<=j<=m}[-1+1/(j+1)+(j+1)eps]}.

For every eps it is nonincreasing in m, lies between -1 and eps, and is concave/nondecreasing in eps. For 0<eps<1/[m(m+1)] the ground branch remains e_m, so mu'_m(0+)=m+1. All the favorable monotonicity statements coexist with escape of the true minimum.

For each fixed eps>0 the optimizing index in (4.1) eventually stops changing with m. Thus apparent confinement at a fixed penalty does not test the zero-penalty minimum. This is the exact order-of-limits warning. It refutes monotone penalized values => uniformly bounded true-bottom V, not the CCM bound itself.

## 5. A weaker sufficient interface: compact near-bottom competitors

### 5.1 Gap-free extension of the NOESCAPE consumer

**[COFINAL_FAMILY | PAPER, using S2.]** Suppose g_m are unit literal-carrier vectors on an unbounded set, with energy defects

d_m=<A_mg_m,g_m>-lambda_m>=0, d_m->0,

and some subsequence has a nonzero weak limit. Then RH follows from S2. The g_m need not be exact eigenvectors, nor have a small norm residual.

Proof. Under not-RH, write lambda_m=-x_m with x_m>=nu>0 eventually. For every fixed theta combination r put r_m=P_mr, rho_m=||A_mr_m||->0, R_m=||r_m|| bounded. Positivity of A_m-lambda_m I gives Cauchy-Schwarz:

|<r_m,(A_m-lambda_m)g_m>|^2
 <=(<A_mr_m,r_m>+x_m R_m^2)d_m
 <=(rho_m R_m+x_m R_m^2)d_m.

Consequently

(5.1) |<r_m,g_m>| <= rho_m/nu
       + sqrt[(rho_m R_m/nu^2+R_m^2/nu)d_m] ->0.

Since r_m->r and the fixed theta span is dense, g_m converges weakly to zero, contradicting the hypothesis. This proof has no inverse spectral gap and no upper bound on ||A_m||. QED.

### 5.2 One shrinking-penalty path is sufficient for RH

**[COFINAL_FAMILY | PAPER, conditional consumer implication.]** Suppose there exist m_j->infinity, eps_j>0 with eps_j->0 and a finite C such that

(5.2)  0<=mu_{m_j}(eps_j)-lambda_{m_j}<=C eps_j.

Then RH follows. Indeed (2.4) gives V[g_j]<=C and d_j<=C eps_j->0. S1's compact sublevels yield a strongly convergent unit subsequence; apply 5.1.

Equation (5.2) is weaker than requiring a uniformly bounded V for exact bottoms. It is NOT proved here. In particular, the nearly silent trial P_m h only gives an upper bound mu_m(eps)<=o(1)+eps O(1). It gives no upper bound for mu_m(eps)-lambda_m unless the unknown lower energy is also controlled.

**[ABSTRACT | PAPER; strict logical distinction.]** Let delta_m=2^(-m^2), A_m have value 0 on e_0, delta_m on e_1,...,e_{m-1}, and -delta_m on e_m. Use B_m=diag(1,...,m+1). At eps_m=1/m the penalized minimum is e_0 and

(mu_m(eps_m)-lambda_m)/eps_m=1+m delta_m<2,

while the exact bottom is e_m and V_m=m+1. Thus (5.2) need not recover compactness of true bottoms in an arbitrary family. It does recover a sufficient RH interface for the literal source through 5.1. No false claim about exact ground selection is needed.

## 6. An even more economical observable

**[ABSTRACT | PAPER.]** Fix finite R,T>0 and use the existing NOESCAPE observer

C=1_{[-R,R]} P_T^freq, J=C*C.

Then J is positive compact, 0<=J<=I, and ||C||_HS^2=2RT/pi. Put J_m=P_m J P_m on the literal even carrier and define

nu_m(s)=lambda_min(A_m-s J_m),
chi_m(s)=(lambda_m-nu_m(s))/s, s>0.

The envelope calculation gives

(6.1) lim_{s downarrow 0}chi_m(s)
 =max_{f in exact bottom, ||f||=1}<Jf,f>.

A finite positive s overestimates this zero-field response and can select an excited localized state. It is not a certificate about the true bottom.

However, a shrinking-field target is sufficient without that selection claim:

(6.2) there exist fixed R,T,beta>0 and m_j->infinity, s_j->0 such that
       lambda_{m_j}-nu_{m_j}(s_j)>=beta s_j.

For a normalized minimizer g_j of A_m-sJ_m,

chi_m(s)=<Jg_j,g_j>-d_j/s,

so <Jg_j,g_j>>=beta and 0<=d_j<=s_j. Compactness of C gives a nonzero weak limit along a subsequence; 5.1 proves the RH implication.

This asks for one persistent compact component, not complete spatial/frequency tightness. It is therefore a useful weaker measuring device than V. Equation (6.2) is not established for the actual source.

## 7. What must be special to the arithmetic source

Adding a positive penalty does not create a positive commutator, a gap of size eps, or a Ricci-type sum of squares. Our unit-sphere minimization is not made strictly convex merely by adding eps V. At a fixed window one can compute the derivative of a value without differentiating the optimizer, but a sign or summable bound still needs an identity.

A concrete replacement/transport supplier sufficient for 5.2 would be: for selected literal m and eps_m, construct a unit g_m in the same carrier with

V[g_m]<=C_1,
<A_mg_m,g_m><=lambda_m+C_2 eps_m.

It must come from the full signed prime/archimedean/pole source, not from assuming that P_m h is already nearly minimizing. The latter is a circular substitution when a negative competing direction has not been excluded.

The log-2 perturbation test is a falsifier of an alleged SOURCE LAW, not a demand that V alone classify all artificial prime systems. V is a geometric functional; shifting one arithmetic atom generally breaks h's exact radicality. Hence a perturbed family could have a localized negative state and bounded V without contradicting the original implication to RH. The exact source-dependent cancellation, rather than the value of V itself, must distinguish the plant.

## 8. Selected next step and bridge map

Chosen target: a source bound for the normalized penalty excess along a declared shrinking eps_m, (5.2), rather than another derivative of the exact ground vector or a claim that monotonicity of mu is enough. The alternate minimal target is compact reward response (6.2). Do not silently replace these by fixed-eps evidence.

| Representation | Useful closed implication | Missing source input | Discriminator / relative cost |
|---|---|---|---|
| Positive penalty and near-bottom compactness | (5.2) => RH, no spectral gap | uniform normalized excess | tests epsilon boundary layer; cheap finite values, high analytic cost |
| Bounded compact reward | (6.2) => RH, only nonzero compact mass | positive small-field energy gain | rejects excited-state capture as s->0; cheap finite values, high analytic cost |

Cross-domain bridges: (a) envelope theory computes the exact penalty sensitivity; (b) hierarchical regularization supplies a fixed-problem selector but not uniformity in m; (c) compactness/NOESCAPE supplies the gap-free near-minimum consumer. None imports a theorem for a different flow as a CCM sign estimate.

**ONE CODEX DIRECTIVE: AUDIT_PENALTY_RESPONSE_AND_ENERGY_DEFECT_BRIDGE.** Check Sections 2 and 5 against the pinned V and NOESCAPE normalization, then test the two abstract plants in Section 4/5 before any source calculation. The next source attempt must bound (mu_m(eps_m)-lambda_m)/eps_m at a declared shrinking eps_m or provide a complete normalized competitor. A finite probe may locate a transition and falsify a proposed scale; it cannot certify (5.2). No large spectral scan, no new metric fitted to observed vectors, no claim that an artificial atom perturbation must preserve radicality.

## 9. Consumer-first ledger and closeout

DOWNSTREAM_CONSUMER: RH via the pinned actual negative witness and fixed theta quasimodes.
ACTUAL_CONSUMER_REQUIREMENT: nonzero compact component of unit approximate bottoms with absolute energy defect tending to zero.
ORIGINAL_REQUESTED_OBJECT: penalized entropy, competitor transport and recovery of bounded V on true bottoms.
ORIGINAL_OBJECT_IS: NOT_NECESSARY in its stronger exact-bottom form for this consumer.
KNOWN_WEAKER_INTERFACES: Sections 5.2 and 6.2, with their full quantified obligations.
FAILURE_TYPE: NO_DERIVATION of a cofinal arithmetic response; COUNTEREXAMPLE only to the generic monotonicity inference.
EPISTEMIC_STATUS: RESEARCH_DEBT for literal source bounds.
KILL_SCOPE: THEOREM_SHAPE only; no route-family death.
REOPEN_TRIGGER: a source-specific uniform response or an explicit energy-controlled compact competitor.
NOVELTY_AXIS: gap-free transfer for vanishing ENERGY defect, not a new entropy monotonicity theorem.
DISCRIMINATOR: a proposed law must survive eps->0 uniformly enough for (5.2), and distinguish the nested escaping plant from a genuinely compact near-bottom family.

Prediction ledger registered before running Appendix controls: P1 monotone minima can have diverging slopes; P2 one shrinking path can control near-bottoms without controlling exact bottoms; P3 a fixed-strength reward can select the wrong level; P4 mixed-scale errors must retain their eps factor. All four confirmed by the exact controls. No literal numerical prediction was registered or tested.

What became smaller: the required transfer no longer needs eigenvector differentiability, simplicity, gap bounds, or recovery of exact bottoms. What remains: the actual arithmetic estimate of normalized penalty excess, or compact-reward gain. What must not be repeated: infer uniform sensitivity from scalar monotonicity, or read a positive-eps minimizer as a true bottom.

Verification: six exact algebra groups passed. No independent analytic reviewer, Lean, Arb, or new literal CCM numerical scan. The new cofinal inequalities (5.2)/(6.2) remain unproved, and RH is not claimed. Repository delivery does not change this mathematical status.

## Appendix: executed exact controls

Run after extracting the following code as penalty_response_checks.py:
`uv run --with sympy penalty_response_checks.py`.

```python
"""Exact controls, not a CCM computation or an RH certificate.
Registered predictions before execution:
P1: nested monotonic penalized minima can have unbounded zero-penalty slopes.
P2: one shrinking-penalty path can control near-minimizers but not true bottoms.
P3: fixed-strength compact rewards can select the wrong eigenlevel.
P4: the mixed-scale loss must be divided by epsilon.
"""
import sympy as s

def mu_nested(m, eps):
    return min([eps] + [-1+s.Rational(1,j+1)+(j+1)*eps for j in range(1,m+1)])
for m in range(2,15):
    lam=-1+s.Rational(1,m+1)
    eps=s.Rational(1,2*m*(m+1))
    assert mu_nested(m,eps)==lam+(m+1)*eps
    for eps in [s.Rational(1,10000),s.Rational(1,100),s.Rational(1,10),s.Rational(1,2)]:
        assert mu_nested(m+1,eps)<=mu_nested(m,eps)
print('PASS 1 nested monotonic values and growing slope m+1')

for m in range(2,15):
    eps=[s.Rational(1,100000),s.Rational(1,1000),s.Rational(1,10),s.Rational(1,2)]
    lam=-1+s.Rational(1,m+1)
    sec=[(mu_nested(m,e)-lam)/e for e in eps]
    assert all(sec[i]>=sec[i+1] for i in range(len(sec)-1))
print('PASS 2 penalty secants decrease with epsilon; positive epsilon underreads the slope')

for m in range(3,14):
    delta=s.Rational(1,2**(m*m)); eps=s.Rational(1,m)
    a=[0]+[delta]*(m-1)+[-delta]
    b=list(range(1,m+2))
    penalized=[a[j]+eps*b[j] for j in range(m+1)]
    assert min(penalized)==eps and a.index(min(a))==m
    assert s.simplify((min(penalized)+delta)/eps)==1+m*delta
    assert (min(penalized)+delta)/eps < 2
print('PASS 3 bounded shrinking-path excess but unbounded true-bottom B')

# A=diag(0,-1), compact observer C=diag(1,0).
for t in [s.Rational(1,100),s.Rational(1,2)]:
    nu=min(-t,-1)
    assert (-1-nu)/t==0
assert (-1-min(-2,-1))/s.Integer(2)==s.Rational(1,2)
print('PASS 4 fixed reward may detect an excited level, small reward does not')

R=s.Matrix([[1,2],[0,3]]); M=R.T*R
r=s.Matrix([2,-1]); g=s.Matrix([s.Rational(3,5),s.Rational(4,5)])
assert (r.T*M*g)[0]**2 <= (r.T*M*r)[0]*(g.T*M*g)[0]
print('PASS 5 positive shifted-form Cauchy-Schwarz control')

mu2,mu1,l2,l1,eps=s.symbols('mu2 mu1 l2 l1 eps',nonzero=True)
assert s.simplify((mu2-l2)/eps-(mu1-l1)/eps-((mu2-mu1)-(l2-l1))/eps)==0
print('PASS 6 exact four-corner mixed increment')
print('ALL 6 EXACT CONTROL GROUPS PASSED; NO LITERAL CCM SCAN')

```
