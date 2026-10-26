# Post-Q50: a shrinking isolated-atom packet cannot return to this band

2026-10-27. Bounded transfer preflight, original source unchanged.
Root derivation; post_q50_packet_resolution read-only bounded check PASS:
complex concentration, projection distance, integer-gap sufficiency and
certificate-only scope confirmed. No full source theorem admitted.
Question: can Q50's fixed n2 constant-sign test simply be moved above the
cheap prime-index cutoff R while retaining its o(1) original-P return?

## Exact resolution bound

Keep L=log m,M=R=floor(m^epsilon),d=2M+1 and the original Fourier synthesis.
Every unit vector in the FULL band, hence every unit vector in ran P,
satisfies |f(t)|²<=d/L by Cauchy on its Fourier coefficients.
For any measurable E of length at most4a,
 integral_E |f|² <=4ad/L.
For a normalized physical prototype phi supported in E,
 |<f,phi>|<=sqrt(4ad/L),
 ||f-phi||²>=2-2sqrt(4ad/L).
This retains complex phases; a change of phase cannot improve this bound.
Without normalizing the approximation, the best full-band projection error
is at least sqrt(1-4ad/L) whenever 4ad/L<=1.

## Apply to one explicit moving-atom construction

Choose a prime R<p<=m with packets centered at (L-log p)/2 and
(L+log p)/2, provided they lie inside the window. Set a=1/(100p).
The union has length4a. This width is SUFFICIENT to isolate the integer p:
the closest upper integer has log((p+1)/p)>=1/(p+1)>2a, and the lower
integer is at least as far in logarithmic distance. No actual prime gaps
are assumed. Contact-filtered compact profiles may be formed as in Q50.

But since p>R>=1,
 4ad/L=(2R+1)/(25pL)<3/(25L).
Thus every normalized original-P approximation has distance at least
 sqrt(2-2sqrt(3/(25L))) ->sqrt(2).
No choice of bump smoothness or integration-by-parts order fixes this loss.
The Q50 fixed-profile Fourier-tail argument cannot be applied with a moving
width while treating its derivative constants as independent of m.
The corresponding physical absolute-norm return does not tend to zero.
In particular the normalized estimate2(12sqrt(m)+4)||f-phi|| cannot certify
the much smaller isolated weight log(p)/sqrt(p) after such a transfer.
This statement concerns that error allowance, NOT the actual form error.
Even before projection the isolated prime contribution is only
 +/-log(p)/sqrt(p), and the decay contribution is at most4a=1/(25p).
For p>R and R sufficiently large both vanish uniformly as R grows. Thus
this moving single atom does not furnish a constant-scale obstruction
even if its return were granted free; it cannot disprove subpower upper.

## Scope, budget, and next decision

The width1/(100p) is a sufficient construction, NOT a necessary width for
isolating an actual prime. No assertion about all actual gaps, all packets,
or every signed transfer is made. No full-source sign or spectrum is inferred.
The result blocks this specific continuation of the fixed-atom diagnostic.
It does not block broad packets containing many actual prime powers.

Q50's centered prime-index return still costs16sqrt(R), separately from
b_div for T. No new bound for the long centered source is supplied; preserve
s_keep<=6sqrt(m)+6m^(1/4) and its unchanged short/arch return. Full CCM OPEN.

Do not repair this by increasing production M or projecting between source
factors. A next broad-packet argument must keep every actual atom under the
packet and its signed continuous comparison. Separate atom signs cannot be
promoted to that joint statement. The existing Q46 mesh/mass distinction
must be checked before counting any such argument as a new attempt.

Shelf comparison: post-Q35 concentration concerns frequency exceptional
sets, not narrow physical packets. Q39 incidence/prime-dilation variance
also differs. This is one resolution preflight only, not a new arithmetic
estimate or a claim of global literature absence. No Q51 sent.
