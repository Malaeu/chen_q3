# Q10 audit discriminator: conditional geometric-shell reconstruction

2026-10-21. Prepared while Pro Q10 runs; no Pro intermediate consumed.
Root derivation; q10_geometric_discriminator independent bounded PAPER PASS. Not a new own attempt or arithmetic gain.

Assume explicitly the unproved increment variance J_h(X)<=C hX log²(2X)
uniformly for all required dyadic X and real1<=h<=X. This is an assumption,
not a theorem imported from Brent/Platt/Trudgian. Original CCM/P unchanged.

Fix gamma>0 and integer k with k gamma>1/2, before m grows.
Use the exact signed Richardson operator of CCM_Q10_HIGH_ORDER_RETURN.md.
At distance d from m (d between m delta and a fixed fraction of m), a smooth
bounded-overlap partition gives support O(d), derivative scales d^(-r),
||w||<=C/sqrt(m), ||w||_2<=C sqrt(d/m), and
||w^(k)||<=C_k m^(-1/2)[max(1/d,(1+Omega)/m)]^k.
Take h=c_k min(d,m/(1+Omega))*m^(-gamma), c_k small fixed.
Each Richardson increment remains in an O(m) dyadic interval. Global
variance and the localized L2 norm give cost
 C_k sqrt(d/h) log m <= C_k sqrt(1+Omega)m^(gamma/2)log m.
The reconstruction integrates against |dE|<=dpsi+dx. The elementary local
mass bound O((d+1)log m), with d>=1, yields
 C_k d/sqrt(m) log m *m^(-k gamma).
Sum O(log m) overlapping distance shells without replacing the scalar
coefficient vector, frequencies or projector.

Ordinary dyadic blocks X away from the top edge use
h=c_k X/(1+Omega)*m^(-gamma). Their derivative scale is (1+Omega)/X.
The same smoothing cost holds and total reconstruction is bounded by
C_k sqrt(m)log²m*m^(-k gamma).
Where h<1, pay the original small prime range directly, O(sqrt((1+Omega)
m^gamma) log m), rather than assume the variance below its stated domain.
The fixed lower endpoint is included in that range.

Take delta=m^(-1/8-epsilon). At the final top shell Q06's one-sided bound
pays all discrete prime powers by O(m^(-1/4-epsilon)) up to logarithms.
Its continuous part is paid ABSOLUTELY with the cubic bound
|q(L-u)|<=((2M+1)/L)Omega²u³/3,
giving O(sqrt(m)((2M+1)/L)Omega² delta^4)=O(m^(-epsilon)) up to logs.
The smooth transition weight is between0 and1. The full continuous main
is retained first and its removed shell returned with this absolute fee.
No negativity of the entire endpoint kernel is assumed.

Proposed CONDITIONAL conclusion for gamma=epsilon and k>1/(2epsilon):
S<=C_epsilon m^epsilon polylog(m) P.
A scalar T_{>R} upper adds the existing short fee of power3epsilon/2 once;
direct K adds arch50logm+8 with no duplicate short return.
This would repair an analytic transfer, not supply actual arithmetic variance.
Checklist for audit: support near fractional m exp(-delta), overlap partition,
real increment lengths, k-dependent constants, derivative endpoint terms,
small h cells, continuous main and atom cancellation. The bounded check passes with the explicit bookkeeping below.

## Bounded audit qualifications and root reconciliation

Use a nonnegative smooth endpoint cutoff, one for log-distance<=delta and
zero beyond C delta; bulk weights vanish on a collar before m. Bounds for
that cutoff remain at the same powers for fixed C. Divide at x=m/2 and use
boundedly many dyadic variance intervals for pieces crossing dyadic borders.
The reconstruction interval includes all O(kh) rightward spill; no over-m
atom is removed from Fubini. They cancel exactly in reconstruction.
For top shells, d>=c m^(7/8-epsilon), so h>=c_k m^(7/8-2epsilon)->infinity.
On cap-limited shells, precisely h=c_k m^(1-epsilon)/(1+Omega), of order
m^(1-2epsilon)log m. The reviewer informally shortened this to log m;
root corrects that scale here. The required h>=1 conclusion is unaffected.
Ordinary blocks below h=1 are paid directly, including their continuous part.
All log factors are retained as m^o(1), never absorbed into a fixed constant.
Thus choose eta(epsilon)=2epsilon for the full scalar T return, with
m0 and constants depending on fixed epsilon. This remains conditional on
uniform variance. No source gain, Lean/Arb run, or additional Pro send.
This note is an audit discriminator to compare with the eventual Q10 answer.

## Strength of the full assumed increment family

Root argument independently checked by q10_geometric_discriminator:
the full hypothesis for ALL dyadic X and ALL real1<=h<=X already implies
RH. This is an implication audit, not a proof of the hypothesis, not a
claim of novelty, and not a converse for strong increment variance.

Let a_X=X^(-1) integral_X^(2X) E. For0<h<1, at most one integer belongs
to(x,x+h], so |E(x+h)-E(x)|<=log(3X)+1 and J_h(X)<=CXlog²(3X).
The exact variance identity and the assumed bounds give
 integral_X^(2X)|E-a_X|²
 =X^(-1) integral_0^X integral_X^(2X-h)|E(x+h)-E(x)|² dx dh
 <=CX²log²(2X).

Compare A=[3X/2,2X] and B=[2X,5X/2]. Both have length X/2. Their pair
integral is at most integral_0^X J_h(X)dh<=CX³log²(2X), since x in A
is within the base interval and h=y-x<=X. Cauchy then bounds the difference
of their means by C sqrt(X)log(2X). The variance bounds on[X,2X] and[2X,4X]
bound their deviations from a_X and a_(2X) at the same scale. Hence
 |a_(2X)-a_X|<=C sqrt(X)log(2X).
Telescoping from a fixed initial dyadic interval yields
 |a_X|<=C sqrt(X)log(2X),
and therefore J_E(X)<=CX²log²(2X). The already checked Mellin argument in
CCM_Q10_MEAN_SQUARE_RETURN.md then excludes zeros with real part>1/2.
This does not prove that only the specific sparse Richardson step lengths
would suffice for that implication. Restricting the supplier to those actual
steps or a signed coupled pairing remains a legitimate, unproved question.
