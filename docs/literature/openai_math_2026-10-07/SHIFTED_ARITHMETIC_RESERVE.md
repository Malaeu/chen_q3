# Shifted arithmetic reserve: direct bridge candidate

Root derivation2026-10-07; independent squarefree_conductor_check audit PASS for constants, endpoints, increment and quantitative bounds. Source Suzuki §11, same PDF/hash as SHIFT_DESCENT_OWN_ATTEMPT.md. All statements involving ZF78 remain conditional on that unverified external premise.

For 0<=eta<=3/8 put a=1/2-eta, b=1/2+eta and
c_eta=(digamma(b/2)-log pi)/2+1/b-1/a,
k_eta=trigamma(b/2)/4-1/a²-1/b².
Cancellation of the k=0 Lerch term gives exactly
B_eta(t)=exp(at)/a²+c_eta t+k_eta-R_eta(t),
R_eta(t)=(1/4)sum_(k>=1)exp(-(2k+b)t)/(k+b/2)²,
0<R_eta(t)<=exp(-(2+b)t)/[4(1+b/2)²(1-exp(-2t))], t>0.
Here Psi_eta=B_eta-sum_(n<=exp(t))Lambda(n)n^(-b)(t-log n).

For a prime-power cell [log q,log q_next] retain ALL prior prime powers:
A_eta,q=sum_(n<=q)Lambda(n)n^(-b), D_eta,q=sum_(n<=q)Lambda(n)log(n)n^(-b), y=A_eta,q-c_eta>0.
The elementary part exp(at)/a²-y t+D+k has global minimizer t*=log(a y)/a and minimum
E_eta,q=D_eta,q+(y/a)(1-log(a y))+k_eta.
Consequently Psi_eta(t)>=E_eta,q-d_eta,q on the entire cell, where
d_eta,q=q^(-(2+b))/[4(1+b/2)²(1-q^-2)].
This is a sufficient reserve; a negative lower bound does NOT refute the exact cell minimum.

At the event q=p^j put w=log(p)q^-b and y=A_eta,q_previous-c_eta. Then exactly
Delta E=w[log q-(1/a)log(a y)]-(1/a)[(y+w)log(1+w/y)-w].
The last bracket has second derivative1/(y+w), so the nonnegative loss ell obeys
0<=ell<=w²/(2a y).
Ordinary PNT gives y~q^a/a for fixed eta. Summing over all integers already bounds the entire loss tail by O_eta(Q^-b log² Q), since 2b+a=1+b. Finite initial events are retained in the anchor.

## What the imported strip pays, and what it does not

ZF78 gives psi_Ch(x)=x+O_epsilon(x^(7/8+epsilon)). Partial summation at fixed eta and any sufficiently small epsilon>0 gives
y=q^a/a+O_(eta,epsilon)(q^(3/8-eta+epsilon)).
The same estimate holds pre-jump, with w absorbed. Thus a*y/q^a=1+O(q^(-1/8+epsilon)). Writing u_q=a*y/q^a-1,
the exact signed drift term is -(w/a)log(1+u_q).
Its magnitude summed through X is at most O_(eta,epsilon)(X^(3/8-eta+epsilon)), after harmless log absorption. This supplies no eventual sign at eta<3/8. It reproduces, rather than improves, the exponential allowance exp((3/8-eta)t) of the inverse-shift calculation.

Exact remaining supplier, from any prime-power anchor Q:
E_eta,q=E_eta,Q-(1/a)sum_(Q<r<=q, r prime power) w_r log(1+u_r)-sum_(Q<r<=q)ell_r.
An upper bound on the SIGNED logarithmic sum sufficient to pay the anchor, loss and d_eta,q would establish eventual Psi_eta>=0. Every u_r retains the complete previous prime-power history. Absolute values, deleting proper powers from that history, or assuming each u_r<=0 are not justified.

At eta=0 these constants and increments reduce exactly to SCALAR_RESERVE_OWN. At eta=3/8 external positivity is already supplied; the objective is a genuine smaller eta, ultimately eta=0 or shifts tending to0. No strip improvement is proved here.

Alias return: the three local queries (Suzuki inverse shift; inverse Volterra positivity; exponential tilting/integrated Chebyshev/stop-loss order) all returned INCOMPLETE due to semantic-index freshness, not absence. Primary Suzuki §11 was reread locally and online. Generic inverse positivity is rejected by the finite quartet control; no external theorem supplying the actual signed arithmetic bound has been admitted.
