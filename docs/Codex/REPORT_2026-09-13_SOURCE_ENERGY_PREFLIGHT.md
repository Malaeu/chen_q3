# Source energy: the boundary orientation and a bounded-reservoir obstruction

STATUS: ISOLATED_SOURCE_ENERGY_PREFLIGHT; exact review recorded in PROSHKA_QUEUE.md.
SCOPE: ISOLATED_PAPER_PREFLIGHT; no source positivity or canonical admission.
DISCOVERY: INCOMPLETE_NO_CONSUMABLE_TARGET; canonical theorem/consumer edge unbound.
ACTUAL_V_SIGN: OPEN. IC: OPEN. ODD2: OPEN. RH: OPEN. PX_RH_CLAIM: NOT_MADE.
AUTOPSY: dropped=OBJECT_IDENTITY; note=Finite-time zero-state passivity is stronger than the required terminal supply, and bounded reservoir coupling cannot reproduce the full theta tail.

## 1. Exact source and discovery evidence

Source base: fcfd09bdf18806664cd1b69f61e516cc35a70775, Malaeu/chen_q3.
Use the complete Phi and A=||Phi||_2 from
BRIEF_2026-09-13_SOURCE_PASSIVITY.md (SHA256
2c67b05ca651bc143bb74c9047f726f04df355a1b0e259e4ca00d24c3bf22d3f).
Thus f=Phi/A is positive, real and even, with super-exponential tails, and

    P_c(t)=sum c_i f(t+x_i), Q_c(t)=sum c_i(t+x_i)f(t+x_i),
    V[c]=2 Re int_0^infinity conjugate(P_c) Q_c.

Nodes are arbitrary finite real families, coefficients arbitrary complex.
The accepted full-source identity is in TWOCHANNEL_INTAKE section 6,
SHA256 f8d5bd91e2c55692944af8508f272653d2dd4792dfdfba57da6366c8a5843dce.
The later THETARF_INTAKE, SHA256
9c9d60ecf8571ca09e51ad54d81625e3b17b585e6810f958bcfc387c237f8c83,
excludes the fixed RF, not V positivity. Its status supersedes the older RF-open line.

Three registered shelf passes were already run once with --defer-external:
operator (accretive translates/Hankel), analytic (positive-real/log derivative),
and physics (passive storage/half-line flux). Each returned exit 2,
INCOMPLETE / LOCAL_RECEIPT_FOREIGN_INCOMPLETE, due to semantic-index freshness.
They are incomplete searches, not absence evidence; no foreign index was repaired.
Retained stdout hashes, respectively:
31380864a451b7a468bd60cd92d2daf623f251a6cb9b9bad63efc10b2cb7d44a,
ddd94f37387f30138ebf885426ee6b8522816bac739def31aaa848dd6443f300,
87843ec0935af477ead47748526ff26992ee1e3a4bc9e986c0317e78ecf77c24.
Generic Lean and dossier snippets supplied no exact realization. The large
PO3 dossier was only partially read; no complete-dossier absence claim is made.

One primary source was inspected, within the brief's maximum of two:
Boyd, El Ghaoui, Feron, Balakrishnan, Linear Matrix Inequalities in System
and Control Theory (1994), section 2.7.2, printed p25 / PDF page 37.
https://web.stanford.edu/~boyd/lmibook/lmibook.pdf
Fetched PDF: 1165543 bytes, SHA256
ec834fb4a300b52da0e147ecb8a462db8933fb2661fe0495f95fa8a02b849b2b.
Both parsed text and rendered formula page were inspected.
Located quote: "for all solutions of (2.37) with x(0) = 0."
The finite-dimensional real LTI system has stable A and minimal (A,B,C).
A positive storage matrix satisfying (2.35) gives nonnegative supply for
all horizons from zero state. Proposed mapping u=P_c, y=Q_c has the same
sign and factor 2 after complexification, but lacks the required realization.
The target is only infinite-horizon supply on the specified translate family.
Verdict: SOURCE_VERIFIED_CONDITIONAL_ANALOGUE, not an exact source supplier.

## 2. Two elementary failures of the forward zero-state mapping

For one node x=-1 and coefficient 1, every 0<T<1 gives

    2 int_0^T (t-1) f(t-1)^2 dt < 0.                         (E1)

Yet evenness gives the positive terminal supply

    V(-1,-1)=2 int_1^infinity u f(u)^2 du > 0.                (E2)

Thus finite-time passivity of the proposed signals is actually false, without
any hypothesis about xi zeros. This does not give a negative V witness.

There is also no fixed proper finite-dimensional scalar-input/output LTI
realization y=Cz+Du, z'=Az+Bu, z(0)=0, mapping every f(t+x) to
(t+x)f(t+x). Continuity at zero forces D f(x)=x f(x). Since f(x)>0,
the two nodes x=0 and x=1 require D=0 and D=1. This contradiction is
independent of stability, minimality or a storage inequality. It excludes
only this fixed zero-state proper realization, not differential ports,
singular kernels, terminal-value realizations or source-dependent initial states.

With nonzero initial state the usual storage inequality instead gives
2 Re int_0^T conjugate(u)y >= S(T)-S(0). A positive S(0) cannot be
discarded when trying to prove a nonnegative supply. Both (E1) and this
initial-energy issue also occur for positive even Gaussian controls; this
failure is not a distinguishing property of theta.

## 3. The useful physical orientation is terminal release of stored energy

An independently constructed nonnegative quadratic energy E_c(t) satisfying

    E_c'(t)=-2 Re conjugate(P_c(t))Q_c(t),
    lim_(t->infinity) E_c(t)=0                              (E3)

would give V[c]=E_c(0)>=0. This is a sufficient interface, not a construction.
Defining E_c(t) by its future supply integral gives the identity automatically
but leaves exactly the original positivity problem. Such a definition is circular.

For the illustrative Gaussian f(x)=K exp(-b x^2), K,b>0, the mechanism is
explicit: Q_c=-P_c'/(2b), E_c=|P_c|^2/(2b), and (E3) holds for every row.
This example validates the orientation; it is not a replacement for full Phi.

Equivalently one may seek source-defined vectors Psi(x) in a positive Hilbert
space, with a C1 Gram kernel G and, for each x,y,

    (partial_x+partial_y)G(x,y)=-(x+y)f(x)f(y),
    G(x+t,y+t)->0 as t->infinity.                           (E4)

Integration along the diagonal gives G=V, hence positivity. All finite complex
rows are covered. Arbitrary Gram factorization of V presupposes the target
and is not a source-derived solution of (E4).

## 4. A bounded conservative reservoir is also too small

One tempting concrete realization of (E4) uses a real Hilbert space, a
skew-adjoint generator B, a fixed vector b, and

    Psi'(x)=B Psi(x)-x f(x)b, <b,Psi(x)>=f(x),
    ||Psi(x)||->0 as x->infinity.                           (E5)

Whenever the variation-of-constants identity is valid (in particular for
strong solutions), (E5) implies

    f(x)=int_0^infinity k(s)(x+s)f(x+s) ds,
    k(s)=<b,exp(-sB)b>, |k(s)|<=||b||^2.                    (E6)

This is impossible for full theta. Here is a direct bound using every term,
not a leading-term approximation. Set q_n=pi n^2 exp(2x),
phi_n=exp(x/2)(4q_n^2-6q_n)exp(-q_n). For x>=1 all phi_n>0 and

    phi_n'/phi_n = 9/2 + 6/(2q_n-3) - 2q_n <= -q_n,

since q_n>=pi exp(2)>10. The series and its derivatives converge uniformly
on compact x intervals by Gaussian decay in n. Summing gives
f'(x)<=-pi exp(2x)f(x), x>=1, and therefore, with L=pi exp(2x),

    f(x+s)<=f(x) exp(-L s), s>=0,
    int_0^infinity (x+s)f(x+s) ds / f(x) <= x/L+1/L^2 ->0.  (E7)

Consequently no bounded measurable k, even signed or complex, can satisfy
(E6) for all x>=1: its right side divided by f(x) tends to zero, not one.
This excludes bounded coupling (b in the Hilbert space) with unitary reservoir
evolution and terminal norm decay. Unbounded generators alone do not evade it,
because exp(-sB) is still unitary and |k(s)|<=||b||^2. Unbounded boundary
coupling or a different energy identity is outside this obstruction.

## 5. Actual-source discriminator and next bounded task

The accepted negative controls g_a=exp(a x^2)f, a<0, retain positivity,
evenness and squared-coordinate log-curvature, but their full V has finite
negative rows. Pins: DEFORMED_SOURCE_ZERO_WITNESS SHA256
70163ec5703ea516b8a191f705a26034cc9914d875f8e74cee7544a0b496bb4c;
THETA_CURVATURE_ORBIT_OBSTRUCTION SHA256
471489ba05fe8ab31e5ce4a12d1e386a1f7c7768cc5d0bbf0a55a80435f83a5f.
They also satisfy (E1) and the tail bound (E7). These obstructions alone
cannot distinguish the true source or imply positivity for it.

The next attempt must derive an actual energy from the full theta heat
trace/Poisson structure, with a justified boundary port and all mixed terms.
If reservoir language is used, the bounded-coupling case above is excluded
before dispatch; a merely formal unbounded realization is not enough.
Its positive energy must be established independently of V>=0 and xi zeros,
and a concrete hypothesis must fail for g_a. No fixed RF, new comparison J,
finite rank sweep or unconditional passive-system claim is commissioned.
This preflight is part of one SOURCE_ENERGY attempt, not an additional
completed source-sign attempt. Historical count 7 / since-owner-resume 1
remain; no positive source-sign delta or canonical CLOSES/OPENS is claimed.
