# Post-Q47: position commutator in the original metric

Status: BOUNDED_PAPER_PASS; no new arithmetic exponent or source lower bound.
Original source: Q47 finite causal Z_sigma,M_sigma, B_sigma=-dot Z_sigma M_sigma,
full physical L2(0,L), original sparse P only at the final compression.
This tests position-operator order as an alternative to separate state derivatives.

Let X be multiplication by t-L/2, bounded self-adjoint with norm L/2.
For the actual truncated shift V_s, [X,V_s]=s V_s, including V_s=0 for s>=L.
Consequently -dot Z=[X,Z] and, at sigma=1/2,
 B=X-ZXM, M=Z^-1.
There are no boundary distributions: X and every finite shift are bounded.
Thus the complete original first form is exactly
 C0=I_m* [2X-ZXM-M*XZ*] I_m+H_d.
In particular, the adjoint of ZXM is M*XZ*, not Z*XM. Both time directions
and all ordered arithmetic products are retained; no intermediate P is inserted.
This is a reformulation, not yet a sign estimate.

## Test of the proposed order transfer

Although X+L/2 I is nonnegative, its similarity Z(X+L/2 I)M need not have
nonnegative Hermitian part. Similarity is not a positive congruence. A finite
control uses X0=diag(0,1), Z0=[[1,a],[0,1]], M0=Z0^-1: Z0 X0 M0=[[0,a],[0,1]].
Its Hermitian part [[0,a/2],[a/2,1]] has determinant -a²/4 for a!=0.
This is not an actual CCM or original-P counterexample; it excludes only a
generic inference from position order and invertibility.

## Full available cost

Using actual |mu|<=1 and sum_(n<=m)n^-1/2<=2sqrt(m), both ||Z|| and ||M||
are at most2sqrt(m). Hence
 ||B+B*||<=2||X||+2||Z||||X||||M||<=L+4mL.
This gives a legal but weaker original-P upper:
 T_gtR<=(L+4mL+b_div)P,
 PKP>=-(L+4mL+50L+8)P.
The +H_d in C0 cancels on returning A=C0-H_d; no extra H_d fee.
Do not replace the better inherited s_keep<=6sqrt(m)+6m^(1/4) by this trial.
Even the direct actual B norm bound is cheaper than this product payment.

The precise unpaid joint quantity is Re<f,ZXMf> in the original norm; mere
location of the spectrum of ZXM does not control it. An independent lower
bound for this pairing could help, but the identity supplies none. Q42 already
warned against similarity-to-Loewner transfer; this position calculation is
a bounded source crosswalk of that warning, not a new general impossibility.
Rollback before paying ||Z||||M||. No Q48 sent; goal OPEN.

Independent q44_bounded_audit: bounded PAPER PASS, no defects in commutator,
adjoint, L+4mL calculation, single H_d return or limited toy-witness scope.
Root exact Fraction control at a=2 gives Hermitian determinant -1; this is
a generic order-transfer diagnostic only, not a CCM spectrum.
