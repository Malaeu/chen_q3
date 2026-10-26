# Post-Q40 supplier screen: Cotlar almost-orthogonality and the isolated split

2026-10-26. Bounded source/return screen, independent read-only bounded PAPER check PASS.
No new arithmetic exponent. Original P, N=m,L=log m,M=R=floor(m^epsilon).

## Exact return point and what is already known

Q40 §§5–6 supplies SAME original-P unit c_m and complete source matrices
 T=T_iso+T_rest, T_iso=-sum_(p in(alpha m,beta m])D_p,
 T_iso[c_m]>=c0 sqrt(m)/L, |T[c_m]|=o(sqrt(m)/L).
All inner k, real mu/Lambda, prime powers, both times and mixed entries stay.
Hence ||T_iso||>=c0sqrt(m)/L, although the whole T need not have that size.
The question was whether almost-orthogonality could retain enough interaction
between these two full parts to avoid Q40's channel-positive-part loss.

The immediate fixed-profile PNT extension is NOT new work: Q09_AUTOCORRELATION_PREFLIGHT,
section Explicit centered PNT fallback, already bounds the full original-P
form by C(1+Omega)sqrt(m)exp(-c sqrt L), exponent1/2+epsilon-o(1).
POST_Q31_ADDITIVE_FREQUENCY_RETURN repeats it with K², explicitly marking
the duplicate. Neither is counted as another post-Q40 attempt.

## Search scope and primary statement

Three ask dictionaries: Cotlar-Stein/signed logarithmic shifts; signed dyadic
Gram cross terms; Calderon-Zygmund T1/prime discrepancy. All returned
INCOMPLETE (q3_docs freshness), not absence. Literal CCM search found old
window-specific Carleson preflight but no mapped Cotlar application.
That is a bounded search outcome, not global novelty or absence.

Terence Tao, The Cotlar-Stein lemma, 25 May2011, Lemma1 equations(11)–(13):
https://terrytao.wordpress.com/2011/05/25/the-cotlar-stein-lemma/
Author's primary exposition of the theorem; no new arithmetic theorem imported.
Short quote: "a finite sequence of bounded linear operators".
Source requires BOTH row bounds
 sum_j ||T_i T_j*||^(1/2)<=C and sum_j ||T_i* T_j||^(1/2)<=C,
then ||sum_i T_i||<=C. Read the statement and its diagonal explanation
(14)–(15); external full proof is not newly recertified here.
Saved sources/tao_cotlar_stein_2011.html,255625bytes,
SHA256343b2e57acf3d62d2f91af40bdeb1e622b2ee3cd09858ac6f6b17ede40ecf38d.

## Exact mapping and decisive price

H=H'=ran(P) with Euclidean norm. T_1=T_iso,T_2=T_rest are finite bounded
self-adjoint matrices. No additional compression or square of the SOURCE
is asserted as equal to T; products occur only in the theorem hypotheses.
The i=j term is sqrt(||T_i*T_i||)=||T_i||. Therefore every legitimate
Cotlar C for this split obeys C>=||T_iso||>=c0sqrt(m)/L.
No estimate of off-diagonal products can remove this diagonal entrance fee.

The same obstruction holds for every finer decomposition T=sum_j U_j
that has some subset J with sum_(j in J)U_j=T_iso. The full two Cotlar row
bounds imply the same bounds for the subset (nonnegative norm terms only).
Apply the theorem to that subset: ||T_iso||<=C. This argument allows
non-self-adjoint U_j, provided BOTH row hypotheses are retained.
Thus partitioning the prime interval into more pieces does not evade the fee.

Scope: this rules out a sub-half-power Cotlar certificate for decompositions
preserving the isolated contribution as a subset. It does NOT rule out a
new decomposition that mixes positive isolated and negative rest contributions
INSIDE every block, or other one-sided methods, or the actual CCM bound.

## Full legal fallback budget

Since B_p=log2 h(2p) in the interval and ||h(x)||<=2/sqrt(x),
 ||T_iso||<=2log2 sqrt(m)=:a_m.
The full physical norm gives ||T||<=4sqrt(m)L(1+L)=:g_m, so
 ||T_rest||<=g_m+a_m=:b_m.
For the two-part split, both Cotlar rows are <=max(a_m,b_m)+sqrt(a_m b_m).
Hence a lawful price is C_m=b_m+sqrt(a_m b_m)=O(sqrt(m)L²).
Returning to K costs C_m+2(40+16Omega)sqrt(R)+50L+8 once.
This is worse than the inherited full-A cap; retain that cap unchanged.
The LOWER above is for the required Cotlar constant, not for ||T|| or its sign.

## Negative controls and decision

Orthogonal range/corange summands satisfy the theorem efficiently; this is
why the general mechanism can help elsewhere. In contrast, U and -U sum to
zero but still force C>=||U||. That algebraic control is not our source;
Q40's real original-P isolated block supplies the actual mapped obstruction.

Two unverified hints remain for future supplier search: a decomposition
mixing T_iso and T_rest before norms, or a direct signed form comparison.
Neither is an estimate; recombining all pieces as one T simply restates the goal.
Stop the mapped Cotlar import before expensive numerics. No Q41 prepared/sent.

Independent q39_joint_supplier confirmed the primary theorem mapping,
subset restriction, actual Q40 norm lower and fallback constants/short/arch
fees. Q09/Q31 predecessor inspection confirmed the PNT repeat. Finite-template
extension also lacks uniform polarized cross-term estimates; Q40 alone is
not such a supplier. No new source bound and no global absence claim.
