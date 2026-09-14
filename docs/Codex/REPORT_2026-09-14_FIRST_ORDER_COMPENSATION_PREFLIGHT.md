# First implementation test: local storage from the full source and its derivative

STATUS: ACCEPTED_PAPER_LOCAL_TWO_OBSERVABLE_OBSTRUCTION_ONLY.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated branch only.
SOURCE_BASE: ce8dc23af56ef63b45d135f859b1e51cabd88dcd.
FULL_V_SIGN / GLOBAL_IC / GLOBAL_ODD2 / RH: OPEN.
ACTUAL_V_NEGATIVE_WITNESS: NONE. PX_RH_CLAIM: NOT_MADE.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The local storage/square ansatz on (P,P') cannot reproduce the weighted source coefficient u+v; no term is dropped from the true V and no sign of its integral is inferred.

Owner request: "Ну и как мы будем это реализовывать? Давай go."
Outcome: implement one precise version of the proposed first-order compensation,
expand it on every pair, and stop at a proved fit or the first exact obstruction.
This report tests a local quadratic storage and local squares using P and P'.
It does not test all two-channel representations, nonlocal operators, or all
possible compensations. The source is never replaced by a finite theta sum.

## 1. Pinned inputs and scope

Fresh SHA256 checks at SOURCE_BASE:

- REPORT_2026-09-13_COMPENSATION_COUPLING_HUNT.md:
  250e638fc458e9f685c8c48944acb2e36c49c4365df146c734e0e7944e89a803.
  J4--J5 give the reverse-storage certificate and section 4 names this next test.
- REPORT_2026-09-13_NULL_AND_GROUND_STATE_TEST.md:
  19ce3481523bfb3f3f9ba8be24f2c86dc2f1916d80f9535a451d010bceef0d95.
  T1 fixes the full V, G1 its source domains, G3 the Gaussian control.
- docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_NULLVAR_2026-09-13.md:
  4fa7909725d2fa10ccc52d3413580289692d3a1489ecae7bed88956f80980730.
  Equation (1) fixes the complete theta series; (8)--(16) give the positive
  density and full-source derivative bounds.
- REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md:
  8ea7ed0b70f57d271b09cb44f53156cd50b71aa6511bd1fd4077111ba5bef5ef.
  Sections 1--6 fix normalization, interval and all finite complex families.

Report names without a longer prefix are under docs/Codex.
No assertion in the user's unreviewed small-shift L>0 argument is a premise.

Canonical plan remains HOLD, foreign owner ACTIVE, exact theorem/consumer
unbound. Its observation does not admit this candidate. Canonical files,
registries and unknown dirty paths are untouched. Only this report is delivered
in the already authorized isolated mathematical branch.

Registered shelf query, run once:
"Wronskian Christoffel Darboux theta source translated potential energy identity".
Result: exit 2, INCOMPLETE; q3_docs semantic-index freshness validation failed.
Nearby Wronskian declarations concern spheroidal/Ferrers sources and do not
supply this theta identity. This is not an absence verdict or a source admission.
Registered project-memory query:
"Wronskian translated theta potential compensation".
Result: exit 1, no hits in the queried layers. No global absence claim.
The mathematical test below is a direct derivation, not an external theorem.
No web search, numerical sweep or Lean verification is claimed for this test.

## 2. The actual signals and their first-order equations

Keep the full positive real-analytic even source

    Phi(u)=sum_(n>=1) [4pi^2 n^4 exp(9u/2)-6pi n^2 exp(5u/2)]
                         exp(-pi n^2 exp(2u)),
    A=||Phi||_2, f=Phi/A, q=f'/f, U=f''/f.                    (F1)

Positivity of f on R makes q and U real analytic on all R. U is a new symbol
for this potential, not the random variable U in the Brownian representation.

Let I=(-(log 2)/2,0). For every finite x_i in I and c_i in C set

    P(X)=sum_i c_i f(X+x_i),
    Q(X)=sum_i c_i (X+x_i) f(X+x_i),
    z(X)=(P(X),P'(X))^T,
    sigma_c(X)=2 Re(conj(P(X))Q(X)),
    V[c]=integral_0^infinity sigma_c(X) dX.                  (F2)

The exact individual source equation is

    d/dX (f(X+x),f'(X+x))^T
      = [[0,1],[U(X+x),0]] (f(X+x),f'(X+x))^T.              (F3)

This equation is source-defined without V or an assumption about its sign.
It is a repackaging of the derivative of f, available for any positive smooth
source, not a new theta-specific structural theorem or a positivity mechanism.
But its matrix depends on the node x. In particular

    z'=(P', R_U)^T,  R_U=sum_i c_i U(X+x_i) f(X+x_i).         (F4)

Replacing R_U by U(X)P is invalid. The collection of node equations is exact;
a common closed two-dimensional equation for their aggregate has not followed.

## 3. A concrete certificate class to try

Allow ANY C1 Hermitian matrix H(X) of size 2, and any continuous Hermitian
matrix L(X) of size 2. For a positive-square certificate one would require
L(X)=R(X)^*R(X), allowing any finite number of rows in R.

The matrices may depend arbitrarily on X and on the full fixed source.
They must be the SAME for every finite node list and every coefficient row.
They do not depend on that row or its nodes. Define

    S_c(X)=z(X)^*H(X)z(X).

Try the local storage identity

    sigma_c(X) = -S_c'(X) + z(X)^*L(X)z(X).                  (F5)

If it held with L>=0, S_c(0)>=0, S_c(infinity)=0 and the necessary convergence,
it would provide the desired nonnegative representation of V.

The test below proves that F5 cannot hold on the whole required family, even
if H and L are allowed to be indefinite. Thus positivity of their coefficients
is not the first obstruction.

The test is specific: states are P and P', storage is local and quadratic,
dissipation is a quadratic form of the same states, and equality is pointwise
in X. It does not exclude a cancellation that occurs only after integration.

## 4. Expanding the mixed coefficient exposes the obstruction

Fix X>0. For a node x write u=X+x and put

    a(u)=(1,q(u))^T,  b(u)=(q(u),U(u))^T.

Its contribution to z is f(u)a(u), and to z' is f(u)b(u).
Since F5 is to hold for every complex coefficient row, polarization makes
its pairwise coefficient identity, after division by f(u)f(v)>0,

    u+v
      = a(u)^* (L-H') a(v)
          - b(u)^* H a(v) - a(u)^* H b(v),                 (F6)

for EVERY u,v in X+I. H,H',L in F6 are evaluated at this fixed X.
Conjugation is retained; a,b are real on real arguments.

Fix one v=v0 in X+I. The right side of F6 is a linear combination, with
constant complex coefficients at this X and v0, of exactly three functions
of u: 1, q(u), U(u). Thus F5 would require constants alpha_0,alpha_1,alpha_2
such that

    u+v0 = alpha_0 + alpha_1 q(u) + alpha_2 U(u)             (F7)

on the nonempty open interval X+I.

Both sides are real analytic in u on R (separately for real and imaginary
parts). Therefore equality on that interval implies equality on all R.
The full-source tail below rules it out.

## 5. Full-source proof that the missing coefficient is independent

This uses a controlled tail of the COMPLETE series, not substitution by its
first mode. Put t=exp(2u) and d=3/(2pi). Exactly,

    f(u)=(4pi^2/A) exp(9u/2) exp(-pi t) [1-d/t+E(t)],
    E(t)=sum_(n>=2) (n^4-d n^2/t) exp[-pi(n^2-1)t].         (F8)

For j=0,1,2 and t>=1, termwise differentiation gives

    |E^(j)(t)| <= C_j exp(-3pi t).                          (F9)

Indeed the differentiated coefficient is bounded by a polynomial in n of
fixed degree, with bounded inverse powers of t. Factor exp(-3pi t); the
remaining series is dominated, uniformly for t>=1, by a constant times
sum_(n>=2) polynomial(n) exp[-pi(n^2-4)], which converges. This also
justifies the differentiated series, rather than differentiating an
uncontrolled asymptotic remainder.

Since 1-d/t is bounded away from zero on t>=1, logarithmic differentiation
using d/du=2t d/dt gives

    q(u)=9/2-2pi t+2d/(t-d)+O(t exp(-3pi t)),
    q'(u)=-4pi t-4d t/(t-d)^2+O(t^2 exp(-3pi t)),
    U(u)=q(u)^2+q'(u)=4pi^2 t^2-22pi t+O(1).               (F10)

In particular q/t -> -2pi and U/t^2 -> 4pi^2.

If F7 held, divide it by t^2 and take u->infinity: alpha_2=0.
Then divide by t: alpha_1=0.
It would remain u+v0=alpha_0, an impossibility.

THEOREM (local two-observable obstruction).
For the complete source F1 and the interval I, no matrices H,L in section 3
can satisfy F5 for all finite complex families. This holds without any sign
restriction on H or L.

This is an obstruction to one exact compensation construction. It is neither
a negative V witness nor a proof that the full form lacks a Gram representation.
It also shows directly that Q cannot be a source-defined X-dependent linear
combination of P,P',R_U valid for every node family. That conclusion concerns
a linear formula, not arbitrary nonlinear reconstruction of a finite family.

## 6. Boundary accounting, and a sibling that passes the same test

For any chosen H,L the exact finite-horizon accounting is

    e_c(X)=sigma_c(X)+S_c'(X)-z(X)^*L(X)z(X),
    integral_0^T sigma_c
      = S_c(0)-S_c(T)+integral_0^T z^*Lz+integral_0^T e_c.  (F11)

F6 specifies the entire pairwise coefficient of this e_c. No boundary has
been discarded. Arbitrary H need not have a vanishing trace or convergent
energy at infinity; those conditions would need proof before taking T->infinity.

The theorem proves e_c cannot vanish POINTWISE for all families in this class.
It does not prove its integral is nonzero, and does not assign its integral a
sign. An additional integrated identity involving other states remains possible.

For the positive Gaussian sibling f_k(u)=C exp(-k u^2), k>0,
q_k(u)=-2ku and P_k'=-2k Q_k. The SAME certificate class works with

    H=diag(1/(2k),0), L=0,
    sigma_c=-(|P_k|^2/(2k))',
    V_k[c]=|P_k(0)|^2/(2k)>=0.                              (F12)

Gaussian decay pays its infinite endpoint. This confirms that F5 is a real
working mechanism for a sibling; F7 pinpoints the failed transfer to theta.
No k is being optimized and no positivity of the old fixed-k theta remainder
is retried.

Multiplication of theta by exp(epsilon u^2), for fixed epsilon<0, changes
q to q+2epsilon u and changes U by lower-order terms relative to exp(4u).
The same leading limits and hence the same local obstruction persist.
It is therefore a filter on this representation class, NOT a condition that
distinguishes actual theta positivity from the known negative deformations.

## 7. What the implementation now requires

F3 writes out the tested first-order state; F6 makes its exact matching
requirement explicit. The new scoped conclusion is F7--F10: the local choice
(P,P') cannot pay that requirement for the complete theta source.

The immediate design requirement is to preserve the independent weighted
signal Q, or use another representation that carries the same information.
One exact expansion is

    P'=sum_i c_i q(u_i)f(u_i),
    (P')'=sum_i c_i U(u_i)f(u_i),
    Q'=sum_i c_i [1+u_i q(u_i)] f(u_i),  u_i=X+x_i.          (F13)

Thus adding Q is legitimate, but it introduces another explicit observable
in its evolution. It does not by itself close a positive energy identity.
An alternative is to retain the node label in the state and use an integral
operator that mixes labels; that is outside the local two-observable class.

We have NOT proved that infinitely many states are necessary, that all local
differential methods fail, or that F13 has no useful finite closure. Those
would be different claims. Nor have we built a positive operator for F13.

Stop this first test at its exact unmatched coefficient. Before another
full-sign attempt, return to the semantic question for the now explicit
objects: multiplication by the node, source evolution, and their interaction.
A new request saying only "find a positive H" would rephrase the same unpaid
sign problem and is not dispatched here.

No source-sign progress is claimed. This is one completed construction test
under the latest owner resumption; it is not three attempts for the separate
source, algebra and review stages. Historical failures are not erased.

## 8. Verification and delivery state

Parent checks: exact differentiation F3--F4; Hermitian polarization and all
terms/signs in F6; full-series differentiated bound F9; asymptotics F10;
analytic continuation only along the real axis; exact boundary equation F11;
Gaussian control F12; scope exclusions and negative-deformation filter.

No numerical experiment or Lean proof is used. The independent read-only
checker /root/sibling5_check returned CLEAN on full draft SHA256
510d7d05106afecddbb73d7e9c4bfb62da2b475926556de271133f396b31190d.
The reviewer checked F6 polarization, full-series F8--F10, real-analytic
continuation, finite-horizon F11, the Gaussian control and the precise scope.
Only this report is a repository deliverable. Acceptance metadata and a
clarification that F3 is a derivative repackaging were added after that review;
all displayed mathematical formulas and the obstruction proof are unchanged.
