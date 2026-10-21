# Q09 waiting discriminator: exact half-grid and contact balance

2026-10-21. Prepared while the already-sent Q09 naturally runs. Not a second
request and not a new arithmetic improvement. Source: same full sparse-band
CCM, f=Fc on[0,L], zero outside, ||c||=1, all three original contacts.
Let xi_k=pi k/L and u_k=fhat(xi_k)/sqrt(2L).

## Direct Parseval proof avoids an uncharged sampling remainder

View zero-padded f as a periodic L2 function on[0,2L]. Its normalized Fourier
coefficients are u_k. For 0<=s<=L, overlap of this f with its periodic shift
is exactly the physical zero-extended overlap: the wrapped piece lies in the
zero half of the period. Endpoint s=L contributes zero, not an extra atom.
Parseval therefore gives

 2Re<f,V_s f>=2 sum_(k in Z) cos(xi_k s)|u_k|²,
 sum_k |u_k|²=1.

The series is absolutely convergent. Finite prime sums and the finite
continuous s-integral may be interchanged with it. Consequently

 <f,A_prime f>=sum_k a_m(xi_k)|u_k|²,
 <f,G f>=sum_k g_m(xi_k)|u_k|²,
 <f,(A_prime-G)f>=sum_k b_m(xi_k)|u_k|².

All prime powers and all mixed coefficient terms remain in u_k. These are
exact quadratures on the FULL half-grid, not a finite-grid estimate.
At even k=2j, u_(2j)=c_j/sqrt2 for |j|<=M and zero otherwise.
Thus sum_even |u|²=sum_odd |u|²=1/2. Odd samples are not independent
variables: they are linear images of the SAME original c.

## Exact continuous cancellation and stronger contact balance

Write alpha_k=1/4+xi_k². Direct integration gives

 g_m(xi_k)=(((-1)^k)sqrt(m)-1)/alpha_k.

The physical decaying kernel H(t,u)=exp(-|t-u|/2) has the analogous
quadrature multiplier

 h_m(xi_k)=(1-(-1)^k/sqrt(m))/alpha_k.

Original exponential contacts give <f,Gf>=-<f,Hf>. Adding the last two
multipliers proves, since m>1,

 sum_k (-1)^k |u_k|²/alpha_k=0.

Therefore the even and odd weighted masses also agree, and

 <f,Hf>=sum_k |u_k|²/alpha_k,
 <f,A_prime f>=sum_k b_m(xi_k)|u_k|² - sum_k |u_k|²/alpha_k.

This explicitly displays where the growing continuous term cancels. Dropping
the odd samples or treating the two sampled families independently can lose
that equality. Conversely, retaining only these two scalar balance conditions
would enlarge the attainable density class; no such relaxation is exact by
assertion. The original c-dependence and all mixed terms must remain.

## Use in audit, not promotion

Check any proposed Q09 quadrature against these normalizations, full-grid
quantifiers, endpoint zero, and constraints. A useful arithmetic comparison
must then bound the FULL signed b_m pairing. Neither Parseval nor these
balance identities provide that new estimate. Finite truncation additionally
needs its full tail return. No new source exponent, Lean/Arb, or numerics.
Independent q09_halfgrid_discriminator bounded PAPER PASS without reading
Pro intermediate work: full-grid normalization, endpoints, absolute
convergence and weighted parity checked. No message sent to Pro.

Important nonlinear boundary: this proof covers a,g,h,b LINEAR multipliers.
For a² or ag, inverse supports reach2L before multiplying by rho; the
quadrature aliases at +/-2L may be interior and need not vanish. A positive
part b_+ is not automatically of the same compact exponential type either.
Do not apply the exact linear quadrature to moments or positive parts without
a new proof and full alias return. This is a limitation of the argument,
not a claim every such special alias is nonzero.
