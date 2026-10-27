# After Q55: subtracting an affine symbol retains a diagonal price

2026-10-27. Root bounded own calculation, not independent admission.
Original P, fixed epsilon, all actual Lambda coefficients and full B=A-A_cont retained.
Read Q55 §§2–3 and prior CCM_Q07_DISPLACEMENT_PREFLIGHT.md first: the Hilbert map and rank-two displacement were already known. This is a test of a particular scalar completion, not a new map or source no-go.

Let J=diag(j), H_jk=1/(j-k) off diagonal, H_jj=0, and
 B=diag(d)-[diag(g),H]/pi.
For any real b put r_j=g_j-bj. Since [J,H]=11^T-I exactly,
 B=diag(d+b/pi)-[diag(r),H]/pi-(b/pi)11^T.
Original endpoint contact P1=0 removes ONLY the final rank-one term. Thus
 PBP <= [max_j d_j+b/pi+osc_j(g_j-bj)]P.
The compensating diagonal b/pi cannot be discarded. All complex pairings
are retained by this matrix identity; additional two contacts can only help
an estimate justified separately, not change this identity.

At the envelope-information level Q55 supplies |g_j|<=Bcal and d_j<=4Bcal.
For fixed b and M>=1, the worst permitted real g has
 osc(g-bj)=2Bcal+2M|b| (opposite saturated endpoint values).
Hence the worst scalar allowance is
 6Bcal+b/pi+2M|b| >= 6Bcal,
with equality at b=0. Even adaptively choosing b does not improve the
worst class: select odd endpoint values g_M=Bcal, g_-M=-Bcal and d_j=4Bcal.
Then osc(g-bj)>=2|Bcal-bM|, whose optimized price is Bcal/(pi M),
so the resulting allowance remains >=4Bcal, still the same full power.
This relaxed (d,g) class is NOT asserted realizable by actual Lambda or E'.
It shows only that the already supplied independent scalar envelopes cannot
certify a new power by this affine repair. Actual correlated diagonal/symbol
information could improve the result and remains unpaid.

Full return of this trial is T_>R<=(s_aff+bdiv)P and
 PK_mP>=-(s_aff+50L+8)P, only when the actual s_aff is independently bounded.
With the available uniform information, choose b=0 and retain Q55 half power.
Do not add the trial cost to the independent fallback. No source lower bound,
no route killed, no eta(epsilon)->0 gain, no Q56 sent.
Next discriminating input must use actual joint d/g information beyond
separate VK scalar envelopes; rank-two displacement alone was already excluded.
AUTOPSY: dropped=NO_DERIVATION; note=Affine-symbol contact cancellation carries a diagonal price; existing scalar information still returns half power.
