# Exact residual: conditional Green kernel and the cost of changing fibres

STATUS: ACCEPTED_PAPER_CONDITIONAL_GREEN_AND_COMMUTATOR_ONLY.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET.
RH / IC / ODD2: OPEN. ACTUAL_V_NEGATIVE_WITNESS: NONE_SUPPLIED.
No canonical admission, runtime change, or general novelty claim.

## 1. Question, source and bounded outcome

This executes BRIEF_2026-09-13_RESIDUAL_COMPENSATION.md at base
e6065e50b0e8201cb9b5afd042e67123d643b3d9. Its pinned full-source dilation
report defines h, r=h*h, chi, f, mu, w, C, G, B and D=XG+B.
The newly accepted BROWNIANJOINT response, SHA256
a80f2a563788e72cd694cf61ad8fc3fe1e53f5517c54c7217a70f33ab5a91d36,
disproves the weighted rank-one Hodge premise only. It supplies no negative V.

The practical semantic return is: the conditional remainder is a covariance,
and its change with total energy is a commutator with conditional averaging.
Below we pay an exact Green-kernel representation, an actual-source derivative
domain, and a finite bound on that commutator. These are descriptions and bounds
for the remainder. They do not yet compare it with E_micro.

The known negative Gaussian deformations retain these conditional-law
properties. This pass identifies no sign-producing hypothesis distinguishing
the undeformed source. No equivalent TARGET is sent again under these names.

## 2. Reconciled local search

Three registered ask.sh queries preceded the external source reads:

| Exact query | Receipt status | stdout SHA256 |
|---|---|---|
| conditional covariance Stein kernel weighted projection defect | INCOMPLETE, exit 2: semantic-index freshness validation failed | a1d0c7667182df8fb6a24ea84976ada544147a4d39b5acc983e379b8404ed71b |
| ground state representation Picone identity quadratic remainder | INCOMPLETE, exit 2: same validation failure | 6fa28bdee87e7f2e9c507e42497965150dd2f285fe96d60cfb36cde6374e03dd |
| hypocoercivity corrected energy mixed term compensation | INCOMPLETE, exit 2: same validation failure | 35c357ea33ba06fd18b5c0b1c7319fe816a480be0780eb55fe410a9a64d04328 |

Existing results and failures were read, not treated as absence results.
No index repair or replacement query was performed. The accompanying
RESIDUAL_COMPENSATION_SEARCH_RECEIPTS_2026-09-13.json preserves queries,
ASK_RECEIPT_JSON values, hashes and the primary-source manifest.

Local predecessors actually read:

- q3.lean.aristotle/Q3/Proofs/RouteB/WeightedRayleighProjectiveDefect.lean:
  a finite weighted spectral-gap bound, requiring an already supplied gap.
  No such representation/gap for the full residual has been supplied.
- docs/routeB_bus/AGENT_REPORT_2026-09-05_PAPER_NOVELTY_PASS.md, section B:
  ground-state representations were already known to this project; the
  signed Weil jump-measure interface was not paid there.
- docs/routeB_bus/DENSITY_INDEPENDENT_CHECK_2026-09-11.md, CE4--CE5:
  the two-channel multiplier has determinant -(x1-x2)^2 d1^2 d2^2.
  Pointwise square positivity fails; cross-integral compensation remains
  possible. We do not count the same determinant again.

## 3. Three primary-source mappings

Each full HTML source was fetched and its theorem context read. Source
verification concerns what the paper states, not target-theorem acceptance.
Raw HTML and extracted text remain in the owned residual-compensation-hunt
evidence directory named in the receipt manifest.

### COV: exact conditional covariance representation

Saumard--Wellner, *On the isoperimetric constant, covariance inequalities and
Lp-Poincare inequalities in dimension one*, Lemma 2.1, (2.4)--(2.5):
https://arxiv.org/html/1711.00668v3 .
SHA256 a625a095f2202fc2f8011f29d2a22d5f35bcaebd314d582728d79b0147dff58d.
Quote: "If g and h are absolutely continuous".

For a probability CDF F, K(s,z)=F(min(s,z))-F(s)F(z) is nonnegative and
symmetric. The lemma represents Cov(g,h) by the double integral of
g'(s) K(s,z) h'(z), with absolute continuity and conjugate Lp/Lq
integrability. This is an established covariance identity.
Mapping: measure -> p_t(s)ds on (0,1); functions -> actual g_x(t,s);
covariance -> Sigma_ij(t); complex families -> sesquilinear extension.
Section 4 pays endpoints and retains finite-family quantifiers,
the physical f(X)^2 dX measure, and cutoff X>=0.
Strength: EXACT_FIT_FOR_COVARIANCE_IDENTITY_ONLY.
Control: the deformed source has the same conditional law; the identity
continues to hold and supplies no discriminating sign premise.

### GS: exact remainder from a ground-state identity

Frank--Seiringer, *Non-linear ground state representations and sharp Hardy
inequalities*, section 2.1, Assumption 2.1 and Proposition 2.3, (2.5):
https://arxiv.org/html/0803.0503v2 .
SHA256 7bb71219df750fc62cccc14fa784ae0e5ea736799de1b85807a8f25c9af8d9d1.
Quote: "If p=2, then (2.5) is an equality".

The mechanism needs a nonnegative symmetric jump kernel and a positive
ground state satisfying its potential equation, including regularized limits.
With compact support and finite energies, the p=2 remainder is exactly a
nonnegative weighted difference-square energy after division by that state.
Mapping sought: full energy minus potential -> whole V; u -> a linear
image of the whole finite complex family; ground state -> a positive
source-derived function. The required positive kernel, source equation,
full-form equality and support-limit argument have not been paid.
An identity for E_loss alone cannot silently be transferred to V.
Strength: PARTIAL_ANALOGUE, not a mapped theorem.
Control: an application must fail at a named hypothesis for the known
negative deformation. No such discriminating mapping is available.

### HYPO: mixed terms controlled in a modified energy

Dolbeault--Mouhot--Schmeiser, *Hypocoercivity for linear kinetic equations
conserving mass*, section 1.3, H1--H4 and Theorem 2:
https://arxiv.org/html/1005.1495 .
SHA256 f0490bf5ccb49431fa4d13041f2c9038b07cdf1d39d915abc0a7b96514d73747.
Quote: "Inspired by [20], we introduce the modified entropy".

The theorem assumes a semigroup generated by L-T, symmetric microscopic
dissipation, skew transport with macroscopic coercivity, Pi T Pi=0, and
bounded auxiliary operators. It controls mixed terms in a modified entropy
equivalent to the original norm and proves exponential decay.
Mapping sought: Pi -> C, microscopic component -> (1-C)G, transport T ->
an operator coupling fibres. C alone does not give L, T, their domains,
macroscopic coercivity or an identity equating their dissipation with V.
Changing the metric is not automatically an identity preserving V.
Strength: PARTIAL_ANALOGUE; section 5 pays only one concrete commutator bound.
Control: generic projection and norm equivalence survive; the missing
transport/coercivity hypotheses cannot be assumed for either source.

## 4. Paid compatibility: Green representation on actual fibres

For t>0 put s=u/t and

    p_t(s)=t h(ts)h(t(1-s))/r(t),  0<s<1,
    F_t(s)=integral_0^s p_t(v)dv,
    K_t(s,z)=F_t(min(s,z))-F_t(s)F_t(z).

p_t is a positive symmetric probability density. If S has this density,
K_t(s,z)=Cov(1_(S<=s),1_(S<=z)); the kernel is positive semidefinite
as well as pointwise nonnegative. For x in I, a=exp(2x), put

    g_x(t,s)=a^(alpha+2) h(ats)h(at(1-s))/(h(ts)h(t(1-s))).       (R1)

This is exactly the original G_x on the fibre, not a replacement source.

### Endpoint and derivative domain

The accepted complete theta identity BROWNIANJOINT (19) gives

    h(u)=(pi/2)u^(-5/2) exp(-pi/(4u))
         [1-2u/pi+O(exp(-2pi/u))],   u -> 0+.                  (R2)

For each fixed derivative order the differentiated remainder is bounded by
a polynomial in u^(-1) times exp(-2pi/u). Indeed, factor the k=0 exponential
from the complete series; the remaining terms have exponent
-pi*k*(k+1)/u, k>=1. Derivatives add polynomial factors in k,u^-1;
after factoring exp(-2pi/u), their sum is bounded for 0<u<=u0.
The bracket in R2 is bounded away from zero for small u. For fixed 0<a<1,

    ell_a(u)=a^(-3/2) exp[-pi*(1/a-1)/(4u)] (1+O(u)),           (R3)

with corresponding derivative bounds. It extends smoothly and flatly by
zero at u=0. For fixed t>0, R1 extends smoothly by zero at both s endpoints.
Every finite g=sum c_i g_xi and b=sum c_i x_i g_xi is C^1 on [0,1] with
bounded derivatives. No uniformity over all t or nodes is asserted here.

### Exact identity and outer domain

Use g(S)=g(0)+integral_0^1 g'(s)1_(S>s)ds. Bounded derivatives justify
Fubini; the covariance of the indicators is K_t. Thus, conjugating the
first argument,

    Cov_t(g,b)=integral_0^1 integral_0^1
                 conjugate(g'(s)) K_t(s,z) b'(z) ds dz.        (R4)

With b=g this is Var_t(g)>=0. This proves the needed special case of COV,
including complex coefficients and domains. Write the integral [g',b']_Kt.
In the original physical measure,

    E_loss=2 integral_0^infinity f(X)^2
              {X [g',g']_Kt + Re [g',b']_Kt} dX,
              t=exp(2X).                                     (R5)

This is an iterated fibre-then-X integral. Inner integrals are absolutely
finite. For the outer integral, Var_t(g)<=E_t|g|^2 and
|Cov_t(g,b)|<=sqrt(Var_t(g)Var_t(b)); the accepted weighted L2 domains of
G,XG,B give integrability by Cauchy--Schwarz. No absolute interchange of
all derivative integrals with infinite X integration is assumed.
The mixed term remains and has no established sign.

## 5. Paid transport cost: derivative of conditional averaging

This is the transport-side compatibility calculation for the same object,
not a second sign mechanism. Derivatives keep s fixed and t=exp(2X). Put

    chi(u)=exp(pi*u)h(u)/(2pi),
    J(t)=integral_0^t chi(u)chi(t-u)du,
    r(t)=4pi^2 exp(-pi*t)J(t),
    b0(u)=u chi'(u)/chi(u),
    H_t(s)=b0(ts)+b0(t(1-s)).

b0 is distinct from the finite-family b. From p_t=t chi(ts)chi(t(1-s))/J(t),

    rho_t(s):=partial_X log p_t(s)
            =2+2H_t(s)-2t J'(t)/J(t)
            =2(H_t(s)-E_t H_t).                              (R6)

The last equality follows by differentiating integral p_t=1. For t in a
compact subset of (0,infinity), R2 gives exponential endpoint domination
for all derivatives. Elsewhere the density is smooth; likelihood-family
derivatives have the same local domination. Differentiation under the
integrals is justified. Therefore

    partial_X E_t g - E_t(partial_X g) = Cov_t(rho_t,g),
    |partial_X E_t g - E_t(partial_X g)|^2
                       <= I(t) Var_t(g),
    I(t):=E_t rho_t^2=4 Var_t(H_t).                           (R7)

This nonnegative covariance budget follows from Cauchy--Schwarz. It bounds
the error in commuting differentiation and averaging. It is not the mixed
E_loss and has not been compared with E_micro.

A finite full-source constant also gives decay. Define

    M=integral_0^infinity u^2 chi'(u)^2/chi(u) du < infinity,
    c0=3/(2pi)<1.

Finiteness follows from the two full theta series. At zero R2 implies
b0(u)=pi/(4u)-5/2+O(u), while chi decays exponentially in 1/u.
At infinity chi=1-4exp(-3pi*u)+O(exp(-8pi*u)) and
chi'=12pi exp(-3pi*u)+O(exp(-8pi*u)). The integrand is integrable at both
ends. No numerical value or optimality of M is claimed.
Accepted full-source facts 0<chi<=1 and J(t)>=t-c0 give, for t>=1,

    E_t H_t^2
      = J(t)^(-1) integral_0^t chi(u)chi(t-u)
                       [b0(u)+b0(t-u)]^2 du
      <= 4M/J(t) <= 4M/(t-c0),
    I(t) <= 16M/(t-c0) <= 16M/((1-c0)t).                      (R8)

The factor 4 uses (a+b)^2<=2a^2+2b^2, reflection and chi<=1.
All estimates use the full density. R6--R8 describe and bound one actual
change-of-fibre term.

## 6. Exact admissible correction and limitation

For any N in L2(w mu) with CN=0 replace D by D+N. The projected target is
unchanged, and orthogonality gives

    delta E_micro = 2 Re <G,N> = 2 Re <(1-C)G,N>,
    delta E_loss  = 2 Re <(1-C)G,N>.                          (R9)

A zero-conditional-mean correction changes both accounts equally.
N=-(1-C)D erases the written loss but leaves E_micro_new=V with its
unknown sign. This is not a proof that every residual can be removed
while revealing a positive square.

For fixed X, the two-node projected matrix has entries
(2X+x_i+x_j)m_i m_j, m_i=E_t g_xi>0. Its determinant is
-(x1-x2)^2 m1^2 m2^2<0 for distinct nodes. This is the SAME multiplier
obstruction as accepted CE4, applied to current means. It rules out positivity
on every separate fibre, not positivity after X integration with fixed c.

## 7. Decision and first unpaid bridge

Retained: exact covariance representation R1--R5, source-domain proof,
conditional score/commutator and finite bound R6--R8, correction accounting R9.
The mechanism plan now has a worked semantic-return example and a concrete
partial-theorem mapping.

Not paid: a comparison of the entire weighted shift energy E_micro with
the mixed covariance R5 for every finite complex family. An integration by
parts or corrected-energy proposal must retain X=0, the derivative of f(X)^2,
and every node x_i. The conditional averaging bound alone pays none of these.

For the control Phi_epsilon=exp(epsilon X^2)Phi, epsilon<0, the conditional
objects p_t,K_t,rho_t,I(t),M are the SAME. Its natural g_x gains the
fibre-constant factor exp(epsilon x^2)t^(epsilon x). The endpoint proof and
identities still apply, as does conditional projection. Yet its full V has
negative rows. Therefore R4 or R8 is not a sufficient sign criterion without
an additional source-specific relation involving the total-energy weight
and node transport.

Next bounded mathematical action: inspect such a relation before another
sign attempt. A correction needs an exact zero identity, its domain, and its
effect on both sides as in R9. No new Proshka request was dispatched: no
narrower sign-producing hypothesis has yet survived the control comparison.

Historical source-sign no-delta remains 11 (BROWNIANJOINT already counted).
This compatibility pass has no source-sign delta and is not another failed
sign-construction attempt. No canonical counters or registers change.

## Independent receipt and subsequent bounded assignment

The sole read-only checker /root/sibling5_check returned CLEAN on full draft
SHA256 da146d309319ebecb4f4828679e1c53bb2f41b8863f074a728c8959842cb5002.
R1--R9, endpoints, complex covariance, outer domain, the finite M and constant
16, and negative-control limitation were checked. The parent checked the
same identities and constants before that read. Only the status and this
receipt/continuation were added afterward; the mathematical body is unchanged.

After the pass, one narrower candidate was identified: the integrated
derivative of f(X)^2 Var_t(g). It is a proposed exact zero correction with
a boundary term, not a reworded sign requirement. Under Gaussian deformation,
the derivative of its fibre-constant factors exposes the same mixed covariance
appearing in E_loss. The separate request
PROSHKA_REQUEST_GOAL058_NULLVAR_2026-09-13.txt asks to establish this full
identity and its domains, and locate the remaining sign obligation. It does
not assume the identity or its usefulness has already been proved here.
