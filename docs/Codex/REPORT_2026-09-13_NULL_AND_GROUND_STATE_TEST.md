# Testing null compensation and ground-state factorization on the exact theta remainder

STATUS: ACCEPTED_PAPER_NULL_IDENTITY_AND_NAMED_GROUND_STATE_TRANSFER_TEST.
SOURCE_BASE: c6694aba0a2f50b8f004e9e967ae0c63b14900be.
RH / GLOBAL_IC / GLOBAL_ODD2: OPEN. ACTUAL_V_NEGATIVE_WITNESS: NONE.
CONSUMPTION: ISOLATED_PAPER_ONLY; canonical theorem/consumer edge still unbound.
Owner request: try the two named methods mathematically on our actual residual.
Scope: one comparison report, received NULLVAR intake, independent paper reading;
no new sign campaign, canonical admission, runtime change or numerical sweep.

## 1. Exact inputs and what was actually read

- Full NULLVAR response at SOURCE_BASE:
  docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_NULLVAR_2026-09-13.md,
  48806 bytes / 699 LF, SHA256
  4fa7909725d2fa10ccc52d3413580289692d3a1489ecae7bed88956f80980730.
  Fetched from the authorized GitHub branch and fast-forwarded with no edits.
  Parent read the entire response, all proof sections and all three appendices.
- docs/Codex/REPORT_2026-09-13_RESIDUAL_COMPENSATION_HUNT.md, R1--R9:
  source covariance, derivative domains and commutator bound.
- docs/Codex/REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md, sections 1--6:
  exact original source, finite families, normalization and V=M-L.
- docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md, A1--A2:
  all-rank PSD of a holomorphic kernel propagates from any open real interval.
- docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md, sections 1--2:
  full source positivity, evenness, decay and the actual V.

Ground-state mechanism source: Frank--Seiringer, arXiv:0803.0503v2,
https://arxiv.org/html/0803.0503v2 , sections 2.1--2.3, especially (2.9)--(2.12).
Fetched HTML SHA256
7bb71219df750fc62cccc14fa784ae0e5ea736799de1b85807a8f25c9af8d9d1,
rechecked against retained raw bytes. The local p=2 mechanism below is proved
directly, with this half-line's boundary and our full-source domain. We do not
assume that the paper's nonlocal positive jump kernel has been mapped to V.

The null-Lagrangian analogy motivates retaining the boundary. N1 below is
proved directly; no invocation of a multidimensional classification theorem
is needed or claimed.

## 2. Actual target, not a substituted positive energy

Let f=Phi/||Phi||_2 be the full real positive even theta source. Put

    V(x,y)=integral_0^infinity (2X+x+y) f(X+x)f(X+y) dX,
    P(X)=sum_i c_i f(X+x_i),
    Q(X)=sum_i c_i (X+x_i)f(X+x_i),
    V[c]=2 Re integral_0^infinity conjugate(P)Q dX.             (T1)

All node lists are finite and coefficients complex. The original useful
interval is I=(-(log 2)/2,0); T1 also exists for arbitrary real nodes.

With the full two-energy conditional lift, write g=sum c_i g_i,
b=sum c_i x_i g_i, m=E_t g, z=g-m, F=E_t|z|^2,
rho=partial_X log p_t, t=exp(2X), and q=f'/f. Then

    M=2 integral f^2 [X E_t|g|^2+Re E_t(conjugate(g)b)] dX,
    L=2 integral f^2 [X F+Re Cov_t(g,b)] dX,
    V[c]=M-L.                                                (T2)

All these integrals are on X>=0. The accepted domain retains the cutoff,
the physical weight and the mixed term. M is not independently known positive.

## 3. First method: the actual null identity and its nonzero boundary

NULLVAR proves, on every such family in I,

    B= f(0)^2 F(0),
    J_tr=2 integral f^2 Re Cov_t(g,partial_X g) dX,
    J_sc=integral f^2 E_t(rho |z|^2) dX,
    J_wt=2 integral f^2 q F dX,
    B+J_tr+J_sc+J_wt=0.                                      (N)

Each integral is absolutely convergent, f^2 F has an integrable derivative,
and its trace at infinity is zero. These facts are proved from the complete
theta series, not a finite-mode substitute.

For one node x in I, g_x(1,s)>0 inside (0,1) and tends to zero at both ends.
It is nonconstant under the positive density p_1. Thus

    F_x(0)>0,  B_x>0,  J_tr+J_sc+J_wt=-B_x<0.                 (N-boundary)

This is a concrete warning against dropping the edge: the interior sum is
not zero for this actual admissible one-signal family.

For any real constant eta, the suggested reshuffle is

    M_eta=M+eta B,
    L_eta=L-eta(J_tr+J_sc+J_wt)=L+eta B,
    M_eta-L_eta=M-L.                                         (N-ledger)

It is a legal compensation identity, but it changes both accounts equally.
It proves no sign for their difference. In particular N does not say that
the original L is zero.

The producer additionally proves the Gaussian-deformation identity with
exactly 2epsilon L_epsilon; both the weight derivative and the likelihood
derivative are required. Its projected transport insertion preserves V,
whereas the unprojected insertion changes V by the explicitly retained
mean boundary plus score-commutator term. These are part of the accepted
scope below, not new positive premises.

Independent raw intake: sole read-only /root/sibling5_check returned
ACCEPT_FULL_N1_N2_AND_CORRECTION_ACCOUNTING_ONLY on the exact SHA256 above.
The proof, domains, tails, polarization and both accounting rows were CLEAN.
Appendix A's symbolic identities were checked algebraically; the reviewer
could not execute the literal SymPy script because SymPy was unavailable.
No literal execution or Lean validation is claimed in this intake.

## 4. Second method: an exact ground-state square for our actual f

Set D_f P=P'-qP. Direct expansion and integration by parts give

    E_f[P]:=integral_0^infinity |P'-qP|^2 dX
      =integral_0^infinity [|P'|^2+(f''/f)|P|^2] dX
         +q(0)|P(0)|^2.                                     (G1)

Since f is even, q(0)=0. Equivalently, P=f v gives
E_f[P]=integral f^2 |v'|^2>=0. This is the local p=2 ground-state
representation, now on the precise family P from T1.

Domain: on compact node sets the full theta series and its first two
derivatives have a common polynomial-in-exp(2X) times exp(-c exp(2X))
bound, c>0, for X large. From NULLVAR (8),(16),
q=5/2-2pi t+2tJ'/J and J>=t-c0, 0<=J'<=1, c0=3/(2pi).
The full endpoint series imply chi'' is absolutely integrable; chi'(0)=0.
Thus J''=integral_0^t chi(u)chi''(t-u)du is bounded, and
q'= -4pi t+4tJ'/J+4t^2[J''/J-(J'/J)^2] is O(t).
Consequently f''/f=q'+q^2 is O(t^2). These bounds prove absolute integrability
of every G1 term and q|P|^2 -> 0 at infinity. Finite X presents no issue
because f is strictly positive and smooth. Thus no compact-support limit
or zero boundary has been silently assumed.

But E_f is not V. In the limiting one-node case x=0, P=f:

    E_f[f]=0,
    V(0,0)=2 integral_0^infinity X f(X)^2 dX>0.                (G2)

Continuity in x at zero is justified by the same uniform bounds. Therefore
V cannot equal any fixed constant multiple of this E_f for all nodes in I.
G1 is a valid positive form built from the actual source; an identification
with the target remains a separate requirement.

## 5. A sibling where the entire target really closes

For k>0, take the positive Gaussian phi_k(y)=C exp(-k y^2), C>0.
Its first-order ground-state equation is

    phi_k'(y)+2k y phi_k(y)=0.

For its translates P_k=sum c_i phi_k(X+x_i) and
Q_k=sum c_i (X+x_i)phi_k(X+x_i), this gives P_k'=-2k Q_k.
Consequently the SAME target construction as T1 satisfies

    V_phi_k[c]=-(1/k) Re integral conjugate(P_k)P_k' dX
             =|P_k(0)|^2/(2k)>=0.                           (G3)

All finite real nodes and complex coefficients are allowed; Gaussian decay
pays the boundary at infinity. This is a complete mathematical sibling,
not evidence that the theta source satisfies the same equation.

## 6. Exact transfer back to theta, with the full defect

For the actual f and any fixed k>0 define

    r_k(y)=f'(y)+2k y f(y),
    R_k(X)=sum_i c_i r_k(X+x_i).

Then P'=-2k Q+R_k holds identically, giving

    V[c]=|P(0)|^2/(2k)+E_k[c],
    E_k[c]=(1/k) Re integral_0^infinity conjugate(P)R_k dX.    (G4)

This is exactly the requested transfer of the sibling's mechanism back
to our source. Every term is absolutely integrable by the domain in G1.
r_k is an explicitly known full-source profile, not an unknown constant
added to the original inequality.

The natural proposed sufficient step would be E_k[c]>=0 for every finite
family in I, for some fixed k>0. The next section disproves THIS step.

## 7. No fixed Gaussian boundary floor survives the actual source

For t>=1 use the exact q expression and bounds above:

    q(X)<=C0-2pi exp(2X),  C0=5/2+2/(1-c0).

Choose x>=0 sufficiently large that exp(2x)>=C0/pi. For every s>=0,

    q(x+s)<=-pi exp(2(x+s))<=-pi exp(2x),
    f(x+s)<=f(x)exp[-pi exp(2x)s].

Hence

    0<V(x,x)/f(x)^2
      <= x/(pi exp(2x))+1/(2pi^2 exp(4x)) -> 0.              (G5)

This follows by integrating the elementary exponential upper bound against
2(x+s). It bounds the entire source tail; no asymptotic equality,
quadrature or theta-mode truncation is used.

For every k>0, choose x large enough that the G5 upper bound is <1/(2k).
Then the exact residual kernel

    K_k(x,y):=V(x,y)-f(x)f(y)/(2k)

has K_k(x,x)<0. Thus the G4 remainder cannot be nonnegative for all real
families. In fact the failure reaches the requested interval I:
V is holomorphic on S x S, S={z:|Im z|<pi/4}, by accepted A2, and f is
holomorphic there. Thus K_k satisfies the exact A1 hypotheses. If all its
finite matrices on I were PSD, A1 would propagate that sign to all R,
contradicting the exhibited negative diagonal. Therefore

    for EVERY fixed k>0 there exist a finite family x_i in I
    and complex c_i with E_k[c]<0.                           (G6)

G6 is existence on I; it supplies no explicit local rank, nodes or coefficients.
Its witness concerns E_k, not V. V(x,x) in G5 is itself strictly positive.
The amount of negative E_k may be smaller than the positive boundary term,
so this result neither refutes the full V sign nor the possibility of another
ground-state map, boundary term, nonconstant compensation or square representation.

There is an independent diagnostic at the source-equation level:
D_f f(X+x)=[q(X+x)-q(X)]f(X+x). Replacing this factor by -2k x for all
X and x would require q to be affine with slope -2k, hence a Gaussian
source up to a linear exponential factor. The actual q expression grows
like -2pi exp(2X), so that exact Gaussian transfer is unavailable. The G4
identity retains precisely its missing source term instead.

## 8. Mathematical decision and next exact gap

Both methods were applied mathematically to the actual formulas:

- Boundary/null compensation: N is proved, including all domains and the
  strictly positive one-signal boundary. Dropping that edge is invalid;
  the admissible correction alone does not erase L or prove M>=L.
- Ground-state representation: G1 is a true nonnegative square for actual f;
  G2 blocks identifying it with V by a fixed scaling. The Gaussian sibling
  closes its complete V exactly by G3; transfer to theta yields G4. The
  hoped-for nonnegative E_k for one fixed k is disproved by G5--G6.

The universal sign question remains V>=0. A useful next construction must
allow cancellation BETWEEN the boundary contribution and the signed E_k,
or supply a different exact map to a positive energy. Requiring E_k>=0
would strengthen the target to a boundary floor that has just been refuted.
Repeating that sufficient step at another fixed k is excluded by G6.

This is one named ground-state/first-order transfer test, not a refutation
of all ground-state methods or all possible vortex constructions.
No new Proshka request, numerical campaign or source replacement is made here.
Any later candidate must be checked against the known negative Gaussian
deformations, not assumed positive from the ground-state terminology.

## Independent acceptance and bookkeeping

The sole read-only /root/sibling5_check returned CLEAN on complete draft
SHA256 eabf42209b4141a26f55469610a190aca85fccd293f7eb452ac8af41856272ab.
The checker verified G1's boundary and domain, G2--G4's normalization,
the full-source inequality G5 and the precise analytic propagation in G6.
Parent derived and checked these arguments before independent review.
Only the status and this receipt were added afterward; the mathematical
body is unchanged. No numerical tests, SymPy execution, or Lean run underlies
these proofs. The admitted scope here is PAPER only in the isolated branch.

This completes the owner's bounded mathematical comparison of the two
methods. NULLVAR is no longer pending; no additional Proshka task was sent.
One named sufficient sign step was tested locally: nonnegativity of E_k for
a fixed k>0. It failed at that exact scope. Historical source-sign no-delta
therefore advances 11 -> 12 once; this is one completed sign attempt under
the residual-compensation direction, not an additional count for NULLVAR,
paper review, source mapping or publication. These are explanatory records,
not edits to canonical counters. No fourth same-obstruction run is authorized
by the new representation, and no further fixed-k variant is useful after G6.
