# Post-Q44 forcing primitive preflight

2026-10-26. Root derivation; bounded independent read-only check PASS (q45_primitive_screen). This is a
preflight, not a new arithmetic supplier or a closed all-P node.
Sources: Q44 full verdict §§4–6; Q17 full verdict §§3–6; Q43 conclusion.

Keep actual real even F0, A(z)=M_F0(z), its correlation R0, and BOTH time
terms in the finite H_m. Finite sums and rapidly decaying R0 justify

 integral_R H_m(x) dx = 2 A(0)^2 sum_(n<=m) Lambda(n)/sqrt(n).       (P1)

This is signed total mass, not absolute mass, and not the pair's value.
A(0)=xi(1/2) is nonzero: e.g. the alternating eta series is positive at1/2,
zeta(1/2)=eta(1/2)/(1-sqrt(2))<0 and the completed prefactor is negative.
Thus the finite forcing has nonzero positive total mass. With the inherited
ordinary PNT the mass is (4 A(0)^2+o(1))sqrt(m). No RH-size error is used.
It is invalid to choose an ordinary primitive vanishing at BOTH infinities.
A mean subtraction would require returning its entire contribution.
This does not imply a half-power value of the oscillatory pair.

For the actual Q44 seam let y=2h, a=(1/2)log L, b=(7/2)log L,
q=2r, W(u)=u^(q-1)exp(-conj(w)u)/(q-1)!,
B(u)=integral_a^u H_m(y+t)dt. Then exactly

 J_seam=kappa[W(b)B(b)-integral_a^b W'(u)B(u)du].                 (P2)

The terminal term W(b)B(b) must remain. Given only |H_m|<=C0 sqrt(m),
|B(u)|<=C0 sqrt(m)(u-a), the completed price is

 C0 |kappa| sqrt(m)[(b-a)|W(b)|+integral_a^b(u-a)|W'(u)|du].       (P3)

It cannot improve the direct pointwise price C0|kappa|sqrt(m)int_a^b|W|:
W(t)=W(b)-int_t^b W'(u)du, followed by integration of its triangle bound,
proves the displayed bracket >=int_a^b|W|. For fixed w,r and L->infinity
both brackets have order exp(-delta a)a^(q-1). Hence (P3) retains
sqrt(m)L^(-delta/2)(log L)^(q-1). Full pair adds the same once-paid O_w(L)
and original-P rho_K+rho_S=o(1); Q44 interior/far are o(1). This is worse
than the inherited endpoint sqrt(m)/L+L. Keep the inherited bound.

There is extra exact information, but it must not be advertised as a sign:
M_Hm(z)=A(z)^2 sum_(n<=m)Lambda(n)/sqrt(n)(n^z+n^-z).
At z=-conj(w), derivatives through order2r-1 vanish. They allow exchanging
one oriented incomplete inverse integral for its complementary integral,
including every terminal jet. The complementary kernel grows exponentially and converges only using the
finite forcing tails; it is not literally Q17's stable decaying kernel.
Q17 already uses stable causal/anticausal inverses and shows that deleting terminal mixed data loses
the conditional signal. No independent favorable bound follows merely from
these full moments. Ordinary mass (P1) and zero WEIGHTED moments are compatible.

Decision: basic integration by parts is not a new supplier. The precise unpaid
object is the JOINT complex combination in (P2), or an independent all-P
signed comparison. Do not optimize its two terms separately or count this
screen as another substantive arithmetic improvement. A stronger source-specific
bound on the weighted primitive remains possible but is not supplied here.
AUTOPSY: dropped=CANCELLATION; note=Separate primitive and terminal payment only repackages the same pointwise half-power allowance.
