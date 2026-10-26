# Q37: full arithmetic exponential and failure of zero-slack log-chord return

2026-10-26. Full original read:84852bytes/1319LF, SHA256
bd7cfd1890c5c787390b563b4504da51d2d821a30e5d64a4ab24fd6ffbf1eb71.
Five hash/size-verified assets in q37_replay;1041exact controls,8 planted errors,
12 source bodies reproduced, both generated JSON byte-identical.
Independent read-only q32_annulus_audit: qualified PAPER PASS §§2–7.
No material defect found; S11 Gram/contact and S10 consumer inputs inherited.

## Full-source arithmetic input

On physical L2(0,L), B=sum Lambda(n)/sqrt(n) V_log(n), A=B+B*.
Multiplication is BEFORE projection: B^k=sum Lambda^{*k}(n)/sqrt(n)V_log(n).
All ordered products and prime powers are present; products n>=m vanish
because V_log(n)=0, not because arithmetic coefficients vanish. B is nilpotent.
The divisor identity sum_(d|n)Lambda(d)=log n gives
 0<=Lambda^{*k}(n)<=(log n)^k.
Thus U(z)=exp(zB) and its inverse U(-z) obey
 ||U(z)||<=1+sum_(2<=n<=m)(n^|z|-1)/sqrt(n).
For z=+1,-1 this is <=N_m=1+m^(3/2). No preservation of the band or
contacts by U is assumed. These auxiliary bounds do not bound A by log N_m.

## Tested transfer and actual-source defect

For unit original-P f, F_f(t)=log||exp(tB)f||^2 has F_f'(0)=<f,Af>.
The proposed zero-slack inequality F_f'(0)<=F_f(1) would suffice, since
|F_f(1)|<=2log N_m<=3log m+2log2. It is the tested missing step.
Let a=1/100, s=log2, u=chi''-chi/4 for the stated fixed smooth compact bump.
Two identical normalized packets separated by s in the final strip of width
s+2a<log3 have both exponential contacts zero. The whole B on this physical
f_L sees only n=2, and B^2 f_L=0. With alpha=log2/sqrt2,
 <f_L,Af_L>=alpha, ||U(t)f_L||^2=1+alpha*t+alpha^2*t^2/2.
Its log is strictly concave for t>0 and
 alpha-log(1+alpha+alpha^2/2)>32/6561.
This uses exact inequalities, not float64 sign inference.

The compact function is NOT itself an original band vector. Its corrected,
normalized original-P approximation f_m has
 delta=||f_m-f_L||<=C_q L^(q-1/2) M^(1/2-q),
using S11's normalized contact Gram>=I/2 eventually. Choose fixed
q>2/epsilon+2 after fixing epsilon. Pay the whole source and exponential:
 first-form error<=12sqrt(m)*(2delta+delta^2),
 log-orbit error<=4N_m*delta once N_m*delta<=1/2.
Both are o(1). No compact-support cancellation is reused after projection.
Consequently log||U(1)f_m||^2-<f_m,Af_m><=-16/6561 eventually.
The continuous Hd cancels exactly on both sides of the centered comparison.
This excludes only the zero-slack chord (and a stronger operator-log
version implying it). The actual A-value is alpha+o(1), compatible with a
subpower upper. Constant/polylog paid repairs and CCM remain open.

## Complete legal return

Let H=6+3L. Summing actual ordered products yields
 ||B^k||<=6sqrt(m)H^(k-1).
The exact small-time polarization keeps the negative square
-||(U(t)-I)f||^2/t and the mixed remainder -2Re<f,R_t f>/t.
Discarding the former and bounding the latter at t=1/m gives
 A<=[12sqrt(m)+144+24(6+3L)/sqrt(m)]P for m>=16.
This is weaker than inherited S10; retain
 A<=s_keep P, s_keep<=6sqrt(m)+6m^(1/4),
 T_>R<=(s_keep+b_div)P,
 P K_m P>=-(s_keep+50L+8)P.
No duplicate U_sf, prime-power, Hd or short fee. Both time orientations and
all complex mixed terms are preserved. No new eta(epsilon)->0 or pair margin.

Because |F_f(1)|<=G_m=2log N_m, an arbitrary upper on
 d_m(c)=c*A*c-F_f(1) is equivalent up to G_m=O(L) to the original A upper.
Giving this defect the desired budget as a hypothesis is not a new supplier.
Rollback before log interpolation to the exact first derivative/full C0.
No Q38 sent. Goal/RH OPEN; no Lean/Arb or production spectrum run.
