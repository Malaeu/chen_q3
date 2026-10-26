# Post-Q36: close-prime coherence and the complete centered square

2026-10-26. Bounded own preflight, original P and all source coefficients.
No new arithmetic exponent; not a new independent mean-square mechanism.

Let f be the zero-extended unit original-P function and
r(s)=integral conj(f(t))*f(t+s)dt. Write the finite real signed log-measure
 nu=mu-gamma,
 mu=sum_(2<=n<=m) Lambda(n)/sqrt(n) delta_(log n),
 gamma=exp(s/2) 1_[0,L](s) ds.
The original centered symbol is b(xi)=2 integral cos(xi*s)dnu(s).
With rho=|fhat|^2/(2pi), the exact squared identity is
 J=integral b^2 rho=2 integral integral K(s,t)dnu(s)dnu(t),
 K(s,t)=Re[r(s-t)+r(s+t)].
All integrals are finite; rho is integrable and b bounded. Hence
 J=2 integral K dmu dmu -4 integral K dmu dgamma
   +2 integral K dgamma dgamma.
Both time orientations, all prime powers and the endpoint remain present.
This is the weighted version of Q36's finite-frequency square expansion,
not a new arithmetic estimate. The first moment remains c*C0*c=integral b rho.

For Q36's actual close prime pair p,q with pq>m, r(log(pq))=0.
The two ordered discrete cross terms together equal
 4*(log p/sqrt(p))*(log q/sqrt(q))*Re r(log(p/q)).
They are positive eventually by Q36's original-P coherence estimate.
Thus that relation alone supplies no negative credit in the squared sum.
It also supplies no lower bound for J: the negative continuous mixed term
has NOT disappeared. Nor is J a lower bound for the first moment.

Cauchy would give c*C0*c<=sqrt(J). A bound J<=C m^(2eta) would suffice,
but is an additional unsigned arithmetic demand, not a consequence of the
close-prime relation or a necessary condition for our one-sided target.
Returning S=A_prime gives c*S*c=integral b rho-c*Hd*c, 0<=Hd<=4P.
There is no projection or Hd surcharge; mixed continuous terms cannot be
replaced by independent phase averages. Ordinary short-interval averaging,
Taylor reconstruction and cumulative variance returns were already tested
in CCM_Q10_MEAN_SQUARE_RETURN.md and the post-Q24 high-order interval note.
Do not count those again as new attempts or infer absence of other suppliers.

No smaller full price has been supplied. Preserve
 S<=s_keep P, s_keep<=6sqrt(m)+6m^(1/4),
 T_>R<=(s_keep+b_div)P,
 P K_m P>=-(s_keep+50log(m)+8)P.
All these are inherited bounds, not consequences newly proved here.

Decision: close-prime coherence is useful evidence against the independent
phase model, but does not select a favorable first-moment mechanism.
Rollback before squaring to the joint centered pairing. This is a duplicate
recognition/preflight, not a third failed arithmetic attempt and not Q37.
Three rational toy square-expansion controls were checked; they are not
actual source measurements or evidence for a cofinal arithmetic bound.
Independent read-only q32_annulus_audit: bounded algebra/scope PASS.
The crucial distinction is linear first moment versus quadratic ratio pairing;
Q36 already supplies the close-pair fact, not a first-moment sign.
