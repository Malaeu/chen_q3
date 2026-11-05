# One explicit full-source field: primitive lift and exact boundary balance

STATUS: ANALYTIC_PRIMITIVE_LIFT_TEST; exact review belongs to the certificate.
SOURCE_BASE: 448b21ae183e73c03a242e604c6b4767bc1f10d1.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated owner-requested research.
FULL_V / IC / ODD2 / RH: OPEN. ACTUAL_NEGATIVE_V_WITNESS: NONE.
PX_RH_CLAIM: NOT_MADE.

## 1. Saved construction brief and return point

Owner authorized the parent to perform the concrete field construction described
in the preceding answer. The NULLFIELD coauthor request is already active;
this local test does not resend it or interrupt it. Own deliverables: this
report and its small hash/review certificate. No canonical proof admission,
numerical sign campaign, policy change or modification of another writer's files.

Keep I=(-log(2)/2,0), f=Phi/||Phi||_2, the complete positive even theta source,
all finite nodes x_i in I and every complex coefficient row c. Define

    P_c(X)=sum_i c_i f(X+x_i),
    Q_c(X)=sum_i c_i (X+x_i) f(X+x_i),
    V[c]=2 Re integral_0^infinity conjugate(P_c) Q_c dX.

Inputs in docs/Codex:
- REPORT_2026-09-15_STRUCTURED_ZERO_HUNT.md, Z1-Z6: full target,
  weighted null identity, its three q corrections, and the open matching step.
- REPORT_2026-09-14_FIRST_ORDER_COMPENSATION_PREFLIGHT.md, F8-F10:
  controlled differentiated full-series tail, not a first-mode substitution;
  the local (P,P') exclusion does not cover the primitive state below.
- REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md, R9-R12:
  the non-theta control f0=exp(-u^2)-exp(-2u^2)/4 has negative four-node V0.

The candidate keeps the independent weighted signal by its tail primitive
H_c(X)=integral_X^infinity Q_c(t)dt. It adds a periodic transverse coordinate
Y and uses a first sine/cosine mode in the conjugated field v=f u. The desired
invariant is exact equality to the original V, including every boundary.
The cheapest test is to compute the field's full quadratic energy and compare
its kernel with V before any claim about its sign.

Search hints, UNVERIFIED as theta transfers:
(1) mixed primitive/derivative energy and a null Lagrangian with boundary;
(2) harmonic replacement: excess energy of an arbitrary lift versus its
energy-minimizing extension, with a possible orthogonal correction;
(3) boundary observation: nonzero internal signals with a zero measured trace.
The f0 control must retain a failed transfer hypothesis; a generic identity
valid for both sources is not a theta positivity proof.

The bounded stopping condition is one exact full-source balance with a proved
fit or an explicitly identified unpaid term, independently reviewed and pushed.
After a miss, preserve these objects and their joint action before selecting a
new construction. Searches, algebra, domain checking and review are one test,
not separate sign attempts; no historical counter reset.


## 2. An explicit common field, with its actual domain

Write F(u)=integral_u^infinity t f(t)dt. Positivity, evenness and the full
theta tail imply F(u)=F(-u)>0 and F'(u)=-u f(u). Thus

    H_c(X)=sum_i c_i F(X+x_i), H_c'=-Q_c.                 (P1)

Fix ANY lambda>0, independent of the row, and use the cylinder
Omega=(0,infinity) x (R/2pi Z), with dX dY and periodic Y. Set

    v_(c,1)=lambda P_c(X) cos(Y)/sqrt(pi),
    v_(c,2)=lambda^(-1) H_c(X) sin(Y)/sqrt(pi),
    u_c=v_c/f(X), q=f'/f, D_X=partial_X+q.                (P2)

This is one linear map from every allowed finite complex row, constructed
only from the full source. It retains the weighted signal through P1. It
is not a square root of V and makes no positivity assumption about V.

All the integrations below are legitimate for the noncompact actual u_c.
For every fixed finite node family, the controlled full-series tail F8-F10
of the FIRST_ORDER report implies bounds of the form

    |f^(j)(X+x_i)| <= C exp(M X - a exp(2X)), j=0,1,2,
    |q(X)| <= C exp(2X), a>0, X sufficiently large.

The constants may depend on the fixed finite family; no uniform rank/node
limit is taken. Integration of the bound on (X+x_i)f(X+x_i) yields the same
type of bound for F(X+x_i), after decreasing a if necessary. Consequently
P,P',Q,H,qP,qH belong to L2(0,infinity); P and H tend to zero, including
the product P conjugate(H). All fields are smooth up to X=0. Although u
may grow, f u=v decays. The weighted derivatives of u are controlled by
P'-qP, H'-qH, P,H. This proves weighted absolute integrability of every
quadratic term in Q0, Qf and Qf-Q0, by Cauchy-Schwarz. No compact-support
claim or discarded cutoff limit is used. Periodicity cancels the two Y sides.

## 3. Full energy and boundary, with no missing q terms

The weighted derivative obeys exactly D_X u=f^(-1) partial_X v. Hence

    E_lambda[c]
      := integral_Omega f^2 |D_X u1+partial_Y u2|^2
       = integral_0^infinity |lambda P'+lambda^(-1) H|^2,
    D_lambda[c]
       := lambda^2 integral |P'|^2+lambda^(-2) integral |H|^2,
    B[c] := 2 Re(conjugate(P(0)) H(0)).                   (P3)

E_lambda,D_lambda are nonnegative. B has not been assigned a sign.

For the Qf and Jf from STRUCTURED_ZERO Z5, direct integration over Y gives

    integral_Omega f^2 Qf[u_c] = D_lambda[c]+V[c].        (P4)

Indeed the cross derivatives are
partial_Y v1=-lambda P sin(Y)/sqrt(pi) and
partial_X v2=-lambda^(-1) Q sin(Y)/sqrt(pi), so their
integrated cross product is exactly 2 Re integral conjugate(P)Q.

The divergence identity has a NONZERO initial boundary:

    integral_Omega f^2 Jf[u_c]
       = -Re(conjugate(P(0))H(0)) = -B[c]/2.              (P5)

To verify its sign, integrate
J(v)=partial_X Re(v1 conjugate(partial_Y v2))
     -partial_Y Re(v1 conjugate(partial_X v2)).
The term at infinity is zero and the term at X=0 is subtracted;
integral cos(Y)^2/pi dY=1. Thus Qf+2Jf=|D_X u1+partial_Y u2|^2 yields

    E_lambda = D_lambda+V-B,
    V[c] = E_lambda[c]+B[c]-D_lambda[c].                 (P6)

An independent one-dimensional check is

    Re integral conjugate(P') H
       = -Re(conjugate(P(0))H(0))
                         +Re integral conjugate(P)Q.

The weight correction has NOT been silently omitted: since v=f u,

    f^2 (Qf-Q0)
      =2q Re((partial_X v1-q v1) conjugate(v1))
          +q^2 |v1|^2+2q Re(partial_Y v1 conjugate(v2)).   (P7)

P7 is exactly Z6 after substitution. Its three terms are integrable by
section 2. Using Qf in P4, rather than Q0, includes them all.

## 4. Exact pairwise matching and the defect

For x,y in I, the kernels in P3 are

    E_lambda(x,y)=integral [lambda f'(X+x)+lambda^(-1)F(X+x)]
                              [lambda f'(X+y)+lambda^(-1)F(X+y)]dX,
    D_lambda(x,y)=integral [lambda^2 f'(X+x)f'(X+y)
                           +lambda^(-2)F(X+x)F(X+y)]dX,
    B(x,y)=f(x)F(y)+F(x)f(y).

Integration by parts as in section 3 gives, for every pair,

    V(x,y)=E_lambda(x,y)+B(x,y)-D_lambda(x,y).             (P8)

The arbitrary finite complex-row identity follows by finite summation,
retaining conjugation; it is not inferred from positivity of 2x2 minors.
The actual defect of the attempted positive field representation is
B-D_lambda. No free positive constant was generated by the null integral.

## 5. The boundary is genuinely indefinite for the full theta source

For two nodes x,y, the determinant of the boundary matrix is exactly

    det B_(x,y) = -(f(x)F(y)-f(y)F(x))^2.                 (P9)

There exist x,y in I for which this is strictly negative. Otherwise F/f
would be constant k>0 throughout I. Differentiating F=kf gives
q(u)=-u/k on I. Both sides are real analytic on R, so the identity extends
along R and forces f(u)=C exp(-u^2/(2k)). This contradicts the COMPLETE
source tail q(u)/exp(2u)->-2pi. Therefore the boundary kernel has a negative
two-node direction (as well as positive diagonal entries).

This is a negative boundary witness EXISTENCE statement only. It is not an
explicit numerical pair and emphatically not a negative full V witness;
full theta V remains positive on every two-node family by the earlier report.
P9 rules out treating this B alone as a nonnegative boundary term.

## 6. Boundary-only payment fails for every lambda, already at three nodes

Take any three distinct nodes x1<x2<x3 in I. The two homogeneous equations

    sum_i c_i f(x_i)=0, sum_i c_i F(x_i)=0                (P10)

have a nonzero real solution, by dimension. Thus P(0)=H(0)=0 and B[c]=0.
The resulting P is not identically zero. To verify independence of translates
using the exact full source, for x_j>x_i the F8 expansion gives

    f(X+x_j)/f(X+x_i) -> 0 as X->infinity.               (P11)

Indeed the logarithm has leading term
-pi exp(2X)(exp(2x_j)-exp(2x_i)), while every prefactor contributes only
bounded constants or lower-order terms. The controlled higher-mode remainder
tends to zero. In an identically zero linear combination, divide by its
leftmost nonzero translate and take the limit; its coefficient must be zero,
a contradiction. Repeating proves finite independence.

Since P tends to zero and is not the zero function, integral |P'|^2>0.
Therefore for the nonzero row P10 and EVERY lambda>0,

    D_lambda[c]>0, B[c]-D_lambda[c]<0,
    V[c]=E_lambda[c]-D_lambda[c]<E_lambda[c].             (P12)

THE SCOPE IS PRECISE: this common first transverse-mode primitive lift,
with arbitrary constant reciprocal scaling lambda, cannot give
V=E_lambda+nonnegative boundary. The bound B>=D_lambda fails, even on rows
whose entire boundary field v(0,Y) is zero. No assertion about the sign of
V=E_lambda-D_lambda on those rows follows. This does not exclude a different
field, extra transverse modes, source-specific relations between E and D,
or a compensation that acts inside the full energy rather than at its trace.

## 7. Positive sibling and negative control

For f_k(u)=C exp(-k u^2), k>0, F_k=f_k/(2k). Hence Q=-P'/(2k),

    V_k[c]=|P(0)|^2/(2k)>=0.

The same primitive field balance P6 remains correct; here H=P/(2k), so
2 Re integral conjugate(P')H=-|P(0)|^2/(2k), and B=|P(0)|^2/k.
The sign closes through the special equation F=f/(2k), not by declaring
E_lambda to equal V or by ignoring D_lambda. Theta fails this specific
Gaussian proportionality, as proved in section 5. That failure is not new
and is not counted as another attempt.

For the earlier non-theta control f0=exp(-u^2)-exp(-2u^2)/4,

    F0(u)=exp(-u^2)/2-exp(-2u^2)/16.

All of P1-P8 are valid with f0, including the weighted domain estimates.
The already proved negative four-node V0 implies E_lambda+B<D_lambda on
those rows. Thus the generic lift does not distinguish theta from f0;
no positivity inference has slipped in through the null identity.

## 8. Semantic return before any second construction

The concrete objects are now explicit: an arbitrary extension of the source
signals, its positive energy E, its internal cost D, and a boundary observation
B which sees only P(0),H(0). The first two are whole functions; the boundary
observation loses nonzero combinations of three signals. A zero trace is not
a zero interior field. Our surviving equation is V=E+B-D.

The next question is NOT a new name for B>=D: section 6 disproves that
sufficient condition for this lift. A potentially relevant different
mechanism is to identify D as the energy of an orthogonal, removable part
of the extension, with the remaining energy representing V. This is only a
search hypothesis. The requisite orthogonality and exact source identification
are unpaid, and an indefinite B cannot be dropped.

Source/shelf verification of that mechanism is recorded below before any
new construction is selected. No second full-sign attempt is launched here.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The explicit primitive null field has energy E=V+D-B; the true boundary is indefinite and B-D is strictly negative on a three-node zero-trace row, so this field does not furnish the requested positive representation.


## 9. Verified sibling and its unpaid transfer

Primary source: Thomas Schmidt, *Calculus of Variations*, version March 9,
2020, Chapter 1, printed pp.4-5 (PDF pages6-7), Theorem (Dirichlet principle)
and its proof. [Author/university PDF](https://www.math.uni-hamburg.de/en/forschung/bereiche/am/geom-part-differentialgleichungen/dokumente/calcvar.pdf).
SHA256: 2a4053647b4d4fcd5318d77bfae9e644e4806429d703e16dca7da08fabd2d4ed.
Quote: "u is weakly harmonic on" (p.4).

The source equates minimizing one-half integral |Dh|^2 at fixed Sobolev
boundary data with orthogonality to zero-boundary variations. Its proof
therefore gives, for r in W^(1,2)_0 and u=h+r,

    integral |Du|^2 = integral |Dh|^2 + integral |Dr|^2.

The mixed integral vanishes by weak harmonicity and density, not merely
because r has zero trace. Complex fields follow by real and imaginary parts.
This supplies a verified mechanism for subtracting an exactly identified
excess energy. It does not identify that excess with our D_lambda.

Our application check:
- PROVED: P2 is a common lift with finite weighted divergence-square energy
  E_lambda, with explicit boundary and defect.
- OPEN: a source-built orthogonal splitting that pays D_lambda and B together.
- INAPPLICABLE directly: the cited energy is the full gradient norm; ours is
  a divergence square on an unbounded periodic cylinder, with indefinite B.
- FALSE: paying D_lambda from B alone, by P12.
- CONTROL: the published principle also holds independently of f0; any theta
  application must prove the specific energy identification which f0 fails.

Three dictionaries were queried through ask.sh: primitive/null-boundary;
harmonic replacement/orthogonal zero-trace energy; and boundary observability.
All returned INCOMPLETE (exit2, semantic-index freshness validation failed).
The queried rows and previously read compensation reports supplied no verified
map for this field; no shelf absence or index repair is claimed. One external
primary-source mechanism was therefore checked, with the exact gap above.
The website PDF text was read on pp.4-5; no successful screenshot of both pages
is claimed. No speculative next construction has been promoted to a theorem.

## 10. Verification and bounded outcome

Independent reader /root/sibling5_check returned CLEAN on P1-P12 and their
full scope, draft SHA256 a62be25ad55cb285143ae6ce7fdc28b625c1471e9c668d90ae2d41ff7a47fc2a.
The reviewed construction/proofs are unchanged; section9 adds the source
mapping and section10 records the review. Exact final review is in the
certificate. No Lean proof, numerical sign sweep or canonical admission.

Outcome: one explicit common full-source auxiliary field, a rigorous complete
energy/boundary identity, and a precise obstruction to using THIS energy as
V plus a nonnegative boundary. Full V sign, IC, ODD2 and RH remain open.
Proshka's NULLFIELD request remains a separate pending wider construction;
it was not resent or interrupted by this test. One bounded construction test
is completed; no source-sign counter is reset by its review or publication.
