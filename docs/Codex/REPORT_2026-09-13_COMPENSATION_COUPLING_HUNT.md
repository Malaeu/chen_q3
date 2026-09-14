# Semantic return: coupling a nonzero residual to the whole energy

STATUS: ACCEPTED_DISCOVERY_AND_CONDITIONAL_PREFLIGHT_ONLY.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET (canonical theorem/consumer edge unbound).
SOURCE_BASE: 4702d6d505dd6f497c73bb575d802f9486cbd678.
RH / GLOBAL_IC / GLOBAL_ODD2: OPEN. ACTUAL_V_NEGATIVE_WITNESS: NONE.
This is bounded discovery and mathematical preflight, not a new sign claim.

## 1. Input, new question and receipts

The source-pinned BRIEF_2026-09-13_COMPENSATION_COUPLING_HUNT.md fixes the complete
h, r, f, p_t, physical weight, finite complex families, negative control and
scope. Its SHA256 is 31a69b8f8a8b657417478046fd197fd3ea513aac91b3c5ee4c8cbb321ad9ae20.
The previous null and Gaussian-ground-state tests are completed inputs, not
pending work. The user-pasted small-shift L>0 proof is not an accepted premise
of this search; it needs its own exact independent check.

The question is how known proofs construct a compensator whose algebra reveals
positivity of the WHOLE V=M-L while L need not vanish. M is not assumed positive.
We looked for construction rules, not a theorem that every remainder is removable.

Three new registered shelf queries were executed once:

| Dictionary | Query | Result |
|---|---|---|
| Physics | Bogomolny energy square topological bound vortex critical coupling | INCOMPLETE |
| Probability/geometry | Helffer Sjostrand covariance Brascamp Lieb deficit Hessian identity | INCOMPLETE |
| Control | Kalman Yakubovich Popov positive real lemma storage spectral factorization | INCOMPLETE |

All three returned exit 2, q3_docs semantic-index freshness validation failed.
Exact shelves and knowledge returned nearby declarations but no consumed interface.
The local Andrews--Clutterbuck and Ashbaugh texts mention Brascamp--Lieb ground-state
log-concavity, not the requested full residual representation. They were inspected.
Previous covariance, ground-state and hypocoercivity sources/receipts were reused.
No absence claim or index repair follows from these results. mgrep external search
also failed with an expired JWT; web__run supplied primary-source discovery instead.
The accompanying COMPENSATION_COUPLING_SEARCH_RECEIPTS_2026-09-13.json retains
all raw-output hashes, primary-source hashes and local evidence paths.

External search was warranted because the prior identities do not connect the
whole energy to a positive expression. Stop condition: up to three verified
mechanisms, exact source/control mappings, and one named next test. The parent
handled probability/control, one read-only researcher handled physics; the
reserved independent checker did not author the report. No descendants.

## 2. Source-verified mechanism cards

VERIFIED below concerns source evidence, not a proof of our theta target.

### P: Poisson equation and Bochner compensation

Carlen--Cordero-Erausquin--Lieb, *Asymmetric Covariance Estimates of Brascamp-Lieb
Type and Related Inequalities for Log-concave Measures*, arXiv:1106.0709v2,
https://arxiv.org/html/1106.0709v2 .
HTML SHA256 405baaafbc1dcc613cedd6995d1eae41abc7dd767636112f8cc26c42198bb127.
Locators: Theorem 1.1; (2.1)--(2.10); Remark 2.1; section 5.
Quote (introduction, final paragraph): "something more algebraic was at stake".

The authors report that a stochastic representation suggested the sharp constant,
leading to their algebraic proof. They solve a Poisson equation for the centered
observable, then commute differentiation with the diffusion operator. The resulting
Hessian term controls covariance. Remark 2.1 identifies relatives in the quantum
oscillator and the Bochner--Lichnerowicz formula.

Mapping: their potential -> W_t=-log p_t, variable -> s, observables -> our g,b;
their conditional differentiation term -> our score covariance. Their theorem
assumes positive Hessian on R^n, smoothness and integrability. Our interval with
singular endpoint potential needs an endpoint/domain argument and a useful curvature
bound. Complex finite families follow by sesquilinear polarization of identities,
not by silently extending a nonlinear real-function estimate.
Strength: PARTIAL_ANALOGUE. The full X weight and mixed shift term remain unpaid.
Control: p_t is unchanged by the negative Gaussian deformation, so fibre curvature
and this identity alone cannot distinguish the actual source.

### C: Storage/dissipation certificate (KYP)

A. Megretski, MIT 6.241 lecture notes, *Kalman--Yakubovich--Popov Lemma*,
https://web.mit.edu/6.241/ameg_www_fall2006/www/images/L06kyp.pdf .
PDF SHA256 4c97e80ef0787e772dcf0bc4573f84abcb52e4216e35a61ad8d6c80537ad93af.
Locators: pp.1--2, (18.1),(18.3)--(18.7); Theorem 18.3, p.5.
Quote: "Assume that the pair (A, B) is controllable".

For a specified finite-dimensional linear system, subtracting the derivative of
a quadratic storage function from the supply leaves a nonnegative quadratic form.
Theorem 18.3 relates existence of that storage to a frequency-domain condition
under controllability. This supplies a construction target for a compensator;
it does not automatically construct one for arbitrary signals.

Mapping sought: X -> evolution parameter, theta translates -> state trajectories,
2 Re(conj(P)Q) -> supply, source-derived quadratic functional -> storage.
Missing: a common exact state equation, the matrix/operator certificate, domains
and the correctly oriented endpoints. Arbitrarily many nodes cannot be covered by
one verified finite truncation. Complex coefficients require a Hermitian identity.
Strength: PARTIAL_ANALOGUE. Positive storage alone is insufficient at a nonzero
initial boundary. Control: a certificate proving V>=0 cannot also apply to the
known deformed negative rows; the source equation/certificate must discriminate.

Source audit: the unnumbered matrix line after (18.7) prints plus signs inconsistent
with (18.7). The rendered PDF was inspected. We use (18.5),(18.7) and derive our
signs below; we do not copy that line or treat it as an additional theorem.

### F: Physics completion

David Tong, *TASI Lectures on Solitons*, chapter 3, Vortices,
https://davidtong.org/pdfs/teaching/solitons/tasi3.pdf .
PDF SHA256 4912d156fed211f4a88bfe1549e4a7238f12e16705896130882c59b9d7a3d85c.
Locators: pp.70--71, critical couplings; pp.72--73, (3.7)--(3.10).
Quote: "the couplings in front of the potential are not arbitrary".

At critical coupling the vortex energy is a sum of first-order squares plus
signed magnetic flux. Cross terms cancel using [D1,D2]=-iB3, and fixed winding
turns the flux into a bound. This is a demonstrated completion, not a claim
that arbitrary physical couplings work. The construction is motivated by
matching the cross terms of two squares and retaining the flux at infinity.

Mapping sought: a theta-derived first-order system -> the vortex equations;
quadratic V -> a second variation of that energy, NOT its nonlinear energy;
finite complex family -> admissible variations; physical measure/cutoff ->
a fully transformed domain and boundary. None of these identifications is paid.
Strength: PARTIAL_ANALOGUE. Critical coefficient matching, a background solving
the first-order equations and fixed boundary class are additional hypotheses.
Control: the identical construction cannot certify known negative V_e rows;
a source-dependent equation or matching condition must fail there.

The parent read the local PDF text and rendered p.73. Text extraction loses
the minus sign in the commutator; the rendered formula is -iB3. For the upper
sign in (3.8) and winding k<0, the flux term is -2pi v^2 k>0.

## 3. Own compatibility calculations, not claims quoted from a paper

### J1. What an exact covariance-deficit square would look like

This is a conditional algebraic template, not a paid application to the full source.
On a finite interval let p=Z^(-1)exp(-W)>0, W''>0, and let u be smooth with
u'=0 at both ends. Set H=-u''+W'u'; then E_p H=0. Integration by parts gives

    E_p |H|^2 = E_p |u''|^2 + E_p W'' |u'|^2,
    Re E_p(conj(H')u') = E_p |H|^2.

Consequently the ENTIRE Brascamp--Lieb deficit has the exact representation

    E_p(|H'|^2/W'') - E_p|H|^2
      = E_p|H'/sqrt(W'')-sqrt(W'')u'|^2 + E_p|u''|^2.       (J1)

For complex functions apply the real identity to real/imaginary parts, or expand
with conjugates. The boundary vanishes because u' vanishes, not by convention.
This explicitly illustrates a nonzero variance entering a positive difference.
For the actual singular p_t one must justify the Poisson solution and limiting
boundary terms. Even then the left side of J1 is not automatically our V or L.
The multiplication by X and the mixed covariance with b must remain in the mapping.

### J2. Why adding a favourable curvature hypothesis alone does not solve V

Consider the joint physical probability density on X>=0, 0<s<1:

    dnu=2 f(X)^2 p_(exp(2X))(s) dX ds,
    W(X,s)=-log(2 f(X)^2 p_(exp(2X))(s)).

The factor 2 normalizes the half-line since f is even and has L2 norm 1.
In the open interior, with rho=partial_X log p and q=f'/f,

    W_XX=-2q'-partial_X rho,
    W_Xs=-partial_s rho,
    W_ss=-partial_s^2 log p.                                (J2)

For the normalized deformed source f_e=C_e exp(e X^2)f, e<0,

    W_e=W-2e X^2+constant,
    Hess(W_e)=Hess(W)+diag(-4e,0).                           (J3)

Thus positive joint Hessian, if established, is preserved by this deformation.
The conditional Hessian W_ss is identical. If W_ss>0, the scalar Schur
complement W_XX-W_Xs^2/W_ss even increases by -4e>0.
The accepted DEFORMED_SOURCE_ZERO_WITNESS Z3 still supplies negative V_e rows.
Hence joint convexity plus the retained conditional identities is not a sufficient
criterion for V positivity. This does NOT refute Brascamp--Lieb: its positive
deficit is another form, and its identification with V is precisely missing.
No assertion that the actual joint Hessian is positive is needed for this filter.

### J3. The sign and boundary that a storage construction must actually pay

Let z_c(X) be a source-constructed state, linear in every finite coefficient
family, obeying z'=A(X)z. In a finite-dimensional template put

    S_c=z_c^* H(X) z_c,  H=H^*,
    sigma_c=z_c^* Q(X) z_c.

If an explicitly constructed R and H satisfy

    Q+H'+A^*H+HA=R^*R,                                    (J4)

then direct differentiation gives the reverse-orientation energy balance

    sigma_c=-S_c'+||R z_c||^2,
    integral_0^infinity sigma_c dX
      =S_c(0)-S_c(infinity)+integral_0^infinity ||R z_c||^2 dX. (J5)

The nonnegative conclusion requires S_c(0)>=0, S_c(infinity)=0 and convergence.
This orientation differs from the usual forward storage formula by reversal
of the evolution parameter. A forward inequality with nonnegative storage
would give an initial NEGATIVE boundary and is insufficient here.
For our target sigma_c=2 Re(conj(P_c)Q_c), where

    P_c=sum c_i f(X+x_i), Q_c=sum c_i (X+x_i)f(X+x_i).

The symbol Q(X) for the template matrix is distinct from Q_c above.
A state containing P alone with the old fixed Gaussian relation is already
excluded by G3--G6 in NULL_AND_GROUND_STATE_TEST; it is not retried.
For an infinite state one must supply operator domains and convergence; (J4)
is currently only a finite-dimensional template. Defining H by the unknown
target's positive square root or a tail integral and ASSUMING its positivity
is circular. No such H is supplied in this search.

### J4. The quadratic interface to a nonlinear square completion

Suppose in a real Hilbert setting E(u)=||F(u)||^2+T(u), with F differentiable,
E twice differentiable along a path u(t)=u0+t eta, F(u0)=0, and T constant
along that path. Taylor expansion yields

    (1/2) d^2/dt^2 E(u0+t eta)|_(t=0)=||DF(u0) eta||^2.      (J6)

Thus a nonlinear BPS energy can provide a positive QUADRATIC form through
its second variation. If F(u0) is nonzero, the second derivative also contains
Re <F(u0), D^2F(u0)[eta,eta]>, whose sign is not controlled. If T changes,
its second derivative must also be retained. Complex coefficients can be
encoded by real/imaginary variations, but the identification with the desired
Hermitian V must be checked, including absence of unwanted c_i c_j terms.
Neither existence of a theta background u0 nor equality of this Hessian with
V is inferred. This is the exact missing interface, not an actual theta proof.

## 4. Decision and one smallest next test

Retain F as the closest structural example of the requested compensation:
first-order equations fix a coupling, mixed terms cancel across squares,
and a boundary invariant survives. Retain C as a practical certificate format
for the whole X integral, and P as a way to expose a covariance through an
auxiliary equation. These are three complementary construction rules, not
three proofs of V and not a claim of a ready-made combined theorem.

First unpaid object: a SOURCE-DERIVED first-order system or evolution law
whose quadratic energy identity is exactly V, with the full x_i dependence.
No such system was found in this bounded search. The existence of the
compensator remains a mathematical problem; the literature supplies examples
and requirements, not this missing source equation.

Next bounded test, before asking for another universal sign proof:
write a proposed source-derived first-order system explicitly and compute
its linearization on a generic pair of shifted profiles f(X+x), f(X+y).
Compare its mixed energy coefficient, with the actual measure and both
boundaries, to

    V(x,y)=integral_0^infinity (2X+x+y)f(X+x)f(X+y)dX.

A proof of equality for every pair plus a positive Hilbert representation
would cover every finite family; checking finitely many pairs would not.
Stop that test at the first unmatched coefficient/boundary, or at the exact
remaining source equation. Do not define the system via an assumed positive
square root of V, or regard existence of an unknown storage function as a
solution. A mere replay of the fixed-k Gaussian floor is already excluded.

The actual construction cannot be supplied solely by p_t, covariance positivity
or even an additional joint-convexity assumption: J2--J3 expose the negative-control
failure. A proposed first-order relation must use more information, such as
an exact identity of the original theta source and its dilation profiles.
Which such relation works is not settled here.

This is the requested semantic return with a finite stopping condition.
It does not increment a source-sign failure count: no new full-sign construction
was asserted and then failed.

## 5. Scope and delivery

No new Proshka message, numerical sweep, Lean theorem, canonical state mutation,
source-sign counter increment, or memory-folder edit is part of this search.
The parent owns only this brief/report/receipt in its existing isolated branch.
Any later proof use needs the exact missing source equation/inequality, source
mapping, independent review and canonical consumer admission.

The reserved read-only checker /root/sibling5_check returned CLEAN on exact
full draft SHA256 21d03f81520183be637ab44c4aaa0b1edeb6ddf6f139a3f308cee14b7e3bb0ba.
The review checked all three mappings, J1 boundaries and signs, J2--J3's
negative-control filter, J4--J5 storage orientation and J6 second-variation
limitations. The parent independently read the quoted local sources and
checked all original calculations before this review. Only this status and
receipt were added afterward; the mathematical body is unchanged.
No Lean or numerical verification is claimed or needed for the discovery status.

Source locator correction: Tong bytes were fetched from the author's current
davidtong.org URL above. The Cambridge chapter URL was also read through
web__run, but a direct mirror request returned HTTP 403; no byte equality for
that mirror is asserted. The source PDF SHA256 and mathematical content are
unchanged. This correction records the producer's exact retrieval URL.

The same independent checker confirmed CLEAN on the source-locator-corrected
report SHA256 cd40a0a3520fff63984f1a8a056e37cdecc923462160210dba9a158b92b5cd6f.
The mathematics and earlier scoped verdict are unchanged.
