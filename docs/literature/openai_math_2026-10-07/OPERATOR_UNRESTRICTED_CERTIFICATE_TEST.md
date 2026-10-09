# Unrestricted null-corrector existence is exactly the energy inequality

2026-10-09. Own bounded follow-up to O14 of the owner operator answer.
Independent read-only mobius_short_transfer U1-U2 PASS.
No new arithmetic estimate; RH/SP/MB34 OPEN.

Retain the entire finite divisor-closed ideal set I_X, unit coordinate e,
E=ee*, and aggregate A=D+C_Lambda=D T, T=I+P as in O16.
D has entries d_1=0, d_n=log qn>0 otherwise. P is strictly lower
triangular in increasing norm, so T is invertible with a FINITE inverse.
T mu=e, and e*T=e*, e*T^(-1)=e*. No analytic inverse bound is inferred.

For the exact physical Hermitian G, put G'=T^(-*) G T^(-1).
Then G'11=mu*Gmu=:E_M. For any real budget B, define the Hermitian Z by

 Z_11=0;  Z_ij=-G'_ij/(d_i+d_j) whenever (i,j)!=(1,1),
 Y=Z T.                                                       U1

The denominators in U1 are strictly positive. Directly
D Z+Z D=-G'+E_M E. Therefore congruence by T^(-1) gives

 T^(-*)[B E-G-(A*Y+Y*A)]T^(-1)=(B-E_M)E.                      U2

Because T*E T=E, the bracket itself also equals (B-E_M)E.
This is an exact explicit finite algebraic identity, not a method for
bounding its scalar coefficient. The aggregate correction is allowed
by O12: take Y_p=(log qp)Y for each good prime qp<=X.

Consequently unrestricted finite multipliers satisfying O14 exist
IF AND ONLY IF B>=E_M. Necessity follows by evaluation at mu; sufficiency
is U1-U2. This remains true when B=E_M, without a strict-margin assumption.
The conclusion concerns the exact full-energy certificate, not necessity
of full-energy control for every weaker MB34/high-value approach.

U1 hides the entire joint arithmetic calculation inside T^(-*)GT^(-1).
It therefore cannot count as a proof of the desired upper bound or as
a new positivity mechanism. The formula cancels every non-unit entry
but leaves EXACTLY the old unknown energy at the unit entry.
This strengthens the answer's warning about arbitrary dense multipliers:
existence alone is a reformulation. It does NOT refute a local mixed-prime
construction with a separately proved quantitative bound.

The next useful test must restrict the proposed correction to an explicit
local/arithmetic form and estimate its residual independently. A generic
finite linear solve, pseudoinverse, or SDP feasibility statement cannot
replace that estimate. All source premises and consumer return costs stay
as in OWNER_OPERATOR_Q07_CONCLUSION.md; no new Pro message was sent.
