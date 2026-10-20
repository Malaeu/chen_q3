# Own Q03-cycle attempt 2: the projected endpoint kernel is indefinite

2026-10-20. Independent bounded PAPER review ccm_q01_return_review: PASS (both original constraints and Taylor signs checked). No full exponent gain.

A possible upper-bound shortcut is to drop a near-upper-endpoint prime block
because its cubic Taylor term is a negative rank-one form. Test this on the
literal original three-constraint space, M>=2, L=log m, w=2pi/L.

Use the real Fourier polynomial

    f_e(t)=-3/4+(1+4w^2)cos(wt)-(1/4+4w^2)cos(2wt).

Its endpoint values vanish. For a=±1/2,

    integral_0^L exp(a t)cos(jwt)dt
      = a(exp(aL)-1)/(a^2+j^2w^2),

including j=0. The coefficient-weighted reciprocal-denominator sum is
-3+4-1=0. Hence both exponential constraints vanish exactly. The original
Fourier coefficient vector is in ran(P), with no new modes or source changes.

Now f_e'(0)=0 and f_e''(0)=12w^4 !=0. Let b=f_e''(0). The same exact
translation overlap as in CCM_Q03_ONE_SIDED_PRIMITIVE_CONE_TEST.md gives

    q_e(L-h)=2 integral_0^h f_e(t-h) f_e(t)dt
            =(b^2/2) integral_0^h (t-h)^2 t^2 dt+O_L(h^6)
            =b^2 h^5/60+O_L(h^6)>0

for sufficiently small h>0 at each fixed cell. The odd sine vector in that
other note gives q_o(L-h)<0 on a sufficiently small common interval.
Consequently P Q_M(L-h) P is indefinite there, even with ALL THREE original
constraints. Positive normalization at each fixed cell preserves both signs.
No assertion is made that the interval width is uniform in m.

The negative rank-one cubic term is not a Loewner upper bound for the full
kernel: on its nullspace, the positive fifth-order term survives. Thus the
full endpoint operator cannot simply be discarded using that leading sign.
One may instead bound the Taylor remainder with its actual m,M-dependent
price, or prove cancellation across arithmetic atoms; neither follows from
this sign test. Positive prime weights do not change the sign of an individual
positive quadratic contribution, but this fact is NOT a counterexample for
the full weighted prime sum or actual T_{>R}.

This tests a geometric shortcut, not an arithmetic mechanism. It leaves the
joint C+E_slow bound OPEN and does not count as improvement of its exponent.
