# Post-Q44: positive smoothing of the auxiliary prime cutoff

2026-10-26. Own bounded attempt; independent bounded PAPER PASS. Original all-P goal
unchanged. This auxiliary calculation uses the accepted actual conditional
pair, not arbitrary profiles and not an all-P estimate. No Q45 sent.
Sources: Q44 §§4–6, Q17 §2/§6 and original sparse-band receiver.

## Operation and exact original-source return

Keep original m,P,L=log m,h=L/2-log L and the same pair g,k. For a fixed
B>=0 and 0<=s<=B, let H_s denote Q44 forcing with cutoff n<=exp(L+s)
(integer floor implicit), and J_s=J(h;exp(L+s)). This is an auxiliary
scalar sum, NOT a larger production matrix or a new projector.
For a probability measure nu on[0,B], J_nu=int J_s dnu(s). Equivalently its
prime coefficient is weighted by nu{s:log n<=L+s}; every n<=m keeps weight1.
Both time signs and all prime powers remain in the scalar sum.

Let C be the ACTUAL cross-correlation of g,k. Then
 J_s-J_0=sum_(m<n<=exp(L+s))Lambda(n)/sqrt(n)
                  [C(2h-log n)+C(2h+log n)].                 (1)
Its complete absolute tail is <=C_w sqrt(m) exp(-c_w L²)=o(1), uniformly
in s>=0, by Q17 double-exponential tails and unit log-interval mass.
Therefore |J_nu-J_0|<=the same tail. This is not a swap of infinite prime
and forcing-inverse integrals: (1) is on the already constructed actual C.
Return J_nu to J_0 FIRST; only then use the ORIGINAL m matrix's norm for
cutoff/Fourier/P correction. Applying the enlarged operator to projected
Fourier leakage would need a different fee and is not done here.
Self terms and full H-decay term in original C0 are unchanged, O_w(1).

## Completed forcing-seam certificate

Put q=2r, L_s=L+s, b_s=(3/2)log L_s and
 u_s=L_s-b_s-2h=s+2log L-(3/2)log(L+s).
At s=0, u_0=(1/2)log L. For L>3/2, u_s is increasing and positive.
Apply the Q44 interior/far decomposition at cutoff exp(L_s) and the FIXED
y=2h. For fixed B, all interior/far bounds are uniform o(1): the main
term is O_w(exp(-5h)), the analytic error O_w(exp(-6h)), and the cutoff
error <=C_w sqrt(m)exp(B/2)exp(-c L^(3/2)). Both seam sides survive.

Using only the completed pointwise forcing cap
 |H_s(x)|<=12||F0||² sqrt(m)exp(s/2)
and extending the positive inverse weight from the seam to[u_s,infinity)
gives the explicit price
 F_m(s)=12|kappa| ||F0||² sqrt(m)exp(s/2) delta^(-q)
           exp(-delta u_s) P_(q-1)(delta u_s),               (2)
 P_(q-1)(t)=sum_(j=0)^(q-1)t^j/j!.
The finite gamma-tail identity proves (2); complex phases were retained
until this particular absolute completion. For nonnegative nu the completed
price is int F_m(s)dnu(s), plus the already paid o(1) sectors.

Exactly,
 F_m(s)/F_m(0)=exp((1/2-delta)s)(1+s/L)^(3delta/2)
                    P_(q-1)(delta u_s)/P_(q-1)(delta u_0)>=1. (3)
Every factor is >=1 since0<delta<1/2. Thus NO normalized nonnegative
averaging of these enlarged cutoffs improves this particular price even
at the constant level. This is a lower bound on the DISPLAYED CERTIFICATE,
not on |J_nu|, actual J_seam, a CCM eigenvalue or signed cancellation.

For fixed w, q, the price at zero is
 F_m(0)=Theta_w(sqrt(m)L^(-delta/2)(log L)^(q-1)).           (4)
The corresponding full pair upper price is2int F_m dnu+O_w(L)+o(1).
Dividing (4) by X=m^delta L^(-2delta) retains
 Theta_w(m^(1/2-delta)L^(3delta/2)(log L)^(q-1)) -> infinity.
It is worse than the inherited endpoint O_w(sqrt(m)/L+L), which we keep.
The distinct averaged-translation price O_w(sqrt(m)/L²+L) is also retained
with its own averaged signal. All-P fallback and conditional3/8 unchanged.

## Decision and limits

This is auxiliary prime-cutoff smoothing, not Q17 averaging the translation
parameter. Its return is paid, but its elementary absolute completion fails
for the same loss of signed coupling. Do not tune a positive cutoff mixture
against (2) again. Signed cutoff weights or estimates of the JOINT smoothed
forcing before absolute values are not excluded; their total variation and
full return would have to be paid. No general impossibility or new exponent.
AUTOPSY: dropped=CANCELLATION; note=Positive auxiliary cutoff average followed by gamma-tail absolute cap preserves half-power certificate expense.

Independent q44_bounded_audit checked equations(1)–(4), fixed-B uniformity,
original-m return order and certificate-only scope; no material findings.
Inherited source/receiver facts not recertified; no numerical/Lean/Arb run.
