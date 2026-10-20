# Q02 waiting diagnostic: the exact finite-k top range

20 October 2026. Original m,N=m,L=logm,P; fixed epsilon<1 and eventually R<m/3.
This is an exact diagnostic, not a new bound for the full signed source.

For m/2<d<=m, only k=1 survives and log1=0. Thus B_(m,d)=0 exactly,
and Q01's C_m(d)+E_(m,d)=0 on this whole tail. Separately majorizing C and E
can destroy this exact cancellation. It is not legitimate to infer a source
obstruction from a large separate tail bound for either piece.

For m/3<d<=m/2, only k=1,2 survive, so the full block is exactly

    V_m = (log2)/sqrt2 sum_(m/3<d<=m/2) mu(d) d^-1/2
              P Q_M(log(2d)) P.

No other k, endpoint or mixed mode has been dropped within this block.
At d=m/3 the k=3 term enters, hence that endpoint is excluded. At d=m/2,
Q_M(L)=0, so the possible endpoint atom contributes zero.

Put a=m/3,b=m/2 and S_a(x)=sum_(a<d<=x)mu(d). Let
f(x)=(log2)/sqrt2 x^-1/2 P Q_M(log(2x))P. The inherited source derivative
bound ||Q_M'||<=D_M=(2+8pi M)/L gives

    ||f'(x)|| <= (log2)/sqrt2 (1+D_M) x^-3/2,
    V_m = -integral_a^b S_a(x) f'(x) dx,
    ||V_m|| <= sqrt2 log2 (sqrt3-sqrt2)(1+D_M)/sqrt(m)
                 * sup_(a<=x<=b)|S_a(x)|.

A supplied prefix bound of order m^theta would give this particular absolute
return exponent theta-1/2+epsilon, up to logarithms. No such improved prefix
bound is supplied here. With |S_a|<=m the budget still has power1/2+epsilon.
This is an upper-budget diagnosis, not a lower bound on V_m. In particular
V_m may compensate with the rest of T; separate smallness is not necessary.

For the reciprocal expansion on comparable t,d, the lowest harmonic phase
h t/d has O(1) variation when h=1. Nonseparability alone supplies no growing
oscillation there. Any claimed full improvement must pay this range via actual
mu structure, joint C+E cancellation, or cancellation with other ranges.
Do not infer failure of the complete reciprocal mechanism from this diagnostic.

No extra Pro message sent while Q02 runs. Use this as a readback discriminator.

## Exact first Bernoulli return: where the phase disappears

For F_d(t)=log(t/d)A_m(t), both endpoint values vanish. Write
B1(u)={u}-1/2 and B2(u)={u}^2-{u}+1/6. The periodic B2 is continuous
and has derivative 2B1 almost everywhere. Thus, with the fixed finite matrix,

    E_d=integral_d^m B1(t/d) F_d'(t)dt
       =(d/2) B2(m/d) F_d'(m) - A_m(d)/12
         -(d/2) integral_d^m B2(t/d) F_d''(t)dt.

The endpoints in this formula are one-sided. F_d'(d)=A_m(d)/d;
F_d'(m)=log(m/d) A_m'(m). Its vanishing needs the source projector, not merely A_m(m)=0; see correction below.
The finite source entries are smooth in the interior; integration is intervalwise,
and B2 continuity cancels all internal boundary jumps. No Fourier convergence
interchange is required for this identity.

The lower endpoint after summation over d is
-(1/12) sum_(R<d<=m)mu(d) A_m(d), still a signed arithmetic operator.
The reciprocal Fourier phases equal e(h)=1 at this boundary. Therefore
integration by parts in t alone does not turn every contribution into a rapidly
oscillating mu sum. Its upper boundary and integral remainder must remain
jointly present; a sign or small bound for any one part is not established.
This is an exact readback check for Q02, not a proof that reciprocal methods fail.

### Source-specific correction: upper derivative vanishes

The literal Q diagonal is 2(1-s/L)cos(2pi j s/L), and off-diagonal is
[sin(2pi k s/L)-sin(2pi j s/L)]/[pi(j-k)]. At s=L every entry of Q'_M
is -2/L, hence Q'_M(L)=-(2/L)11*. The original b constraint gives P1=0.
Therefore P Q'_M(L)P=0 and A_m'(m)=0. The upper Bernoulli boundary above
vanishes for the actual source. A prior draft warned it need not vanish
from Q(L)=0 alone; this misses the additional original projector identity.
The correct actual formula is

    E_d= -A_m(d)/12 -(d/2) integral_d^m B2(t/d) F_d''(t)dt.

Source locator: CCM_PRIME_TRANSITION_TEST.md:25-26 (literal Q), and original
sparse-band b constraint. The lower signed mu operator and full integral
remain unpaid. No derivative bound or sign for their sum is asserted.
