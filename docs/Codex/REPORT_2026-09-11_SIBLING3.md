RE: ADVICE_2026-09-11_SIBLING3  STATUS: VICTORY

# SIBLING3 — the proposed pole/fiber dictionary is refuted

PAPER counterexample, attempt1, no Proshka request, no numerical grid.
Source advice e6b5128d68357f1f8a48b63d24c0e2d46b43a554,
SHA256e5e64f1fc599884792f4636c735a79b6e208a8a0fc546497278e52694004b96c.
The victory is the protocol's explicit refutation with a witness, NOT a
positive Sonin-to-Hodge theorem or a proof of RH. Choose the advice's IF_B.
SIBLING1/2 finite and continuous identities remain valid; see their REPORTs
and ../routeB_bus/SIBLING_INDEPENDENT_CHECK_2026-09-11.md S16-S23.

## A. The finite calculation, including a missing projection

Use S9-S12's fiber convention F1={point}xX, F2=Xx{point}, so
Delta.F1=Delta.F2=1, Gamma.F1=1, Gamma.F2=q. For real
D=u Delta+v Gamma, let d1=D.F1=u+v, d2=D.F2=u+qv. The primitive projection is

    D0=D-d2 F1-d1 F2,
    D0.F1=D0.F2=0,
    -D0^2=2d1d2-D^2=C(D,D).                              (T1)

Thus C=-D^2 IF D is already primitive. But inside the RAW span{Delta,Gamma},
d1=d2=0 forces v(q-1)=0 and u=v=0. There is no nonzero primitive part obtained
merely by intersecting that raw two-dimensional span with both fiber kernels.
The nontrivial two-by-two Hodge form is on its PRIMITIVE PROJECTIONS, not on
that zero subspace. For complex coefficients the fiber term is
2Re(conjugate(d1)d2), not 2d1d2.

After q^{-(i+j)/2} normalization the projected Gram matrix is

    [[2g, p1], [p1, 2g]], p1=q^{-1/2}(q+1-#X(F_q)).        (T2)

For genus1, #X(F_q)=q+1-a, hence p1=a/sqrt(q). In the COEFFICIENT V basis
of S1/S16, the extra triangular congruence gives

    V=[[2,-a/sqrt(q)],[-a/sqrt(q),2]].                      (T3)

The raw normalized correspondence block T2 instead has +a/sqrt(q).
Changing sign of its second basis vector gives T3 as another congruence,
but normalization ALONE does not change that sign. T1 is the exact fiber
calculation requested; this distinction prevents conflating the two bases.

## B. Exact pole frequencies and two smooth witnesses

Use the paper's multiplicative Fourier convention, AppendixA (144)-(146),
with u=e^t, G(t)=g(e^t):

    g_hat(z)=int_R G(t)e^{-izt}dt,
    M_+(G)=g_hat(i/2), M_-(G)=g_hat(-i/2).                 (T4)

These are the two completed-zeta pole directions s=0,1. The frequency0
is s=1/2. The pole quadratic contribution in the canonical SL1 is

    Q_pole(G)=2Re(M_+(G)conjugate(M_-(G))).                (T5)

A positive rank-one correction c|g_hat(0)|^2 therefore cannot be identified
with this rank-two indefinite fiber/pole term on the full test class.
Here are explicit admissible witnesses, with no limiting or numerical input.
Take L=(log2)/4 and any nonzero nonnegative smooth bump psi supported on[-L,L],
for example exp(-1/(1-(t/L)^2)) for |t|<L and0 outside. Write Psi for its
Fourier transform; Psi(0)>0 and Psi(+/-i/2)>0.

1. G=(d/dt)^2 psi-(1/4)psi. Then

       G_hat(z)=(-z^2-1/4)Psi(z),
       M_+(G)=M_-(G)=0,
       G_hat(0)=-(1/4)Psi(0)!=0.                         (T6)

   It obeys BOTH pole/fiber moment constraints, and g(u)=G(log u) has the
   support allowed in CC Theorem6.11. Yet Q_pole(G)=0 while
   c|g_hat(0)|^2=c Psi(0)^2/16>0. This refutes the proposed equality of the
   defect bound with the fiber term, even on the primitive moment class.

2. G=(d/dt)(d/dt+1/2)psi. Then

       G_hat(z)=(iz)(iz+1/2)Psi(z),
       G_hat(0)=G_hat(i/2)=0,
       G_hat(-i/2)=(1/2)Psi(-i/2)>0.                     (T7)

   Hence the two hypotheses g_hat(0)=g_hat(i/2)=0 of CC Theorem1 do NOT
   mean that both fiber/pole moments vanish. The pole QUADRATIC term still
   vanishes when one pole moment vanishes; that weaker fact is not a
   two-dimensional primitive projection. For the autocorrelation g*g*,
   the two pole evaluations vanish as products. Keep that distinct from
   the two separate linear constraints on g itself.

CC p3 Theorem1 uses +i/2, while p48 Theorem6.11 prints -i/2. The involution
G(t)->conjugate(G(-t)) exchanges these hypotheses and leaves g*g* unchanged;
the harmless sign choice never turns the extra frequency0 into the other pole.
Finally c|g_hat(0)|^2 is a BOUND on the actual correction E(g*g*) in(142),
not a formula asserting E=c|g_hat(0)|^2. Both proposed identifications fail.

## C. What the paper actually controls about support

Primary: arXiv:2006.13771v1, ../routeB_bus/litreview/pdfs/2006.13771.pdf,
SHA256b8e0b54ade8535cf3ca633d1ef325bfc5c793b407da577a83d111726935b58e0.
Read directly: pp1-3,48-50; p3 and p48 visually inspected. Existing source
receipt/log retained; no new source intake or computation.

- p2 explicitly says the test support lies in(1/2,2) 'so that rational
  primes are not involved'. Thus 'only the prime2 and infinity' in the
  advice is incorrect for this smooth support class. At endpoints the
  smooth compact autocorrelation is0, so the p=2 term is also0.
- p48 Lemma6.10 fixes I=[-(log2)/2,(log2)/2], H=L2(I), the operator K_I,
  and a bound gamma approximately2.94355. Theorem6.11/(141) on the SAME
  interval gives c=4gamma/log2. Its proof(142) keeps the exact correction
  Tr(theta(g)S theta(g)*)-W_infinity(g*g*)=E(g*g*).
- p49 Remark6.12 establishes the nonzero optimal correction13<c<17 on
  this fixed interval. No function c(N), boundedness of c(N), or growth
  estimate as N->infinity is supplied by these statements. None is inferred.
- If it is g whose support grows to[1/N,N], then g*g* has support in
  [1/N^2,N^2], so the possible prime-power terms satisfy p^m<N^2, not N.
  If the AUTOCORRELATION is supported in[1/N,N], the corresponding
  threshold is p^m<N. The variable being enlarged must be specified.
- For a fixed curve, the prime powers are powers of ONE Frobenius q,
  whereas the rational formula adds distinct primes with all their powers.
  A logarithmic support size alone provides no identification of those
  representation spaces or of their pairings.

## Decision and exact remaining object

The proposed dictionary fails at(B), with the explicit smooth witnesses
T6/T7; (A) additionally needs primitive projection and a basis change.
(C) is bounded-source verification, not an unproved extrapolation c(N).
No request 'Castelnuovo for K primes' is sent on this false dictionary.
The remaining mathematical object is still a source-defined positive
pairing equal to the FULL W on all K_a, with the separate frequency0
correction and prime terms included. No claim that this object is
impossible, or that a different function-field Sonin dictionary is excluded.

AUTOPSY: dropped=SIGN; note=the proposed rank-one central-frequency defect is not the two pole/fiber moments; T6/T7 separate them within the actual smooth support class.
