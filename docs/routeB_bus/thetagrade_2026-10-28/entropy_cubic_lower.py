#!/usr/bin/env python3
"""Interval lower bound for the cubic theta moment; no RH assertion.

Checks the compact integral on [0,1]. The analytic reduction/tail positivity
and LSI domain bridge require separate mathematical review.
"""
from flint import arb, ctx
import json

ctx.dps = 50
pi = arb.pi()
cells = 2000
# For n>=5 and 0<=x<=1, t=pi*n²*exp(2x)>=pi*n²>4.
# t² exp(-t) decreases, exp(x/2)<=exp(1/2). Consecutive tail
# bounds have ratio <=(6/5)^4 exp(-11pi)<1/2.
ratio = (arb(6)/5)**4 * (-11*pi).exp()
assert ratio.upper() < arb(1)/2
tail_h = 2*arb('0.5').exp()*16*pi**2*5**4*(-25*pi).exp()
# h_n=8t(2t-3)exp(x/2-t)>0.
# a_n=(D²-1/4)h_n=16t(4t³-28t²+41t-9)exp(x/2-t).
# a_n>0 for t>=7; hence omitted n>=5 terms increase a.
# On x>=1, every t>=pi*exp(2)>7, so the full cubic tail is >=0.
assert (pi*arb(2).exp()).lower() > 7
total = arb(0)
for i in range(cells):
    x = arb(2*i+1)/(2*cells) + arb(0, arb(1)/(2*cells))
    u = (2*x).exp()
    h = arb(0)
    a = arb(0)
    for n in range(1,5):
        t = pi*n*n*u
        weight = (x/2-t).exp()
        h += 8*t*(2*t-3)*weight
        a += 16*t*(4*t**3-28*t**2+41*t-9)*weight
    assert h.lower() > 0
    h_full = h + arb(tail_h/2, tail_h/2)
    # For each x, a_full>=a_truncated. Cubing is increasing on R.
    # h_full encloses the actual positive denominator. Thus the lower
    # endpoint of this box is a valid lower bound, even when a is negative.
    total += (x/2).cosh()*a**3/h_full**2/cells

print(json.dumps({
    'status': 'INTERVAL_COMPACT_LOWER_BOUND_PENDING_ANALYTIC_REVIEW',
    'cells': cells,
    'dps': ctx.dps,
    'theta_h_tail_upper_ball': str(tail_h),
    'truncated_numerator_integral_enclosure': str(total),
    'lower_endpoint_ball': str(total.lower()),
    'certified_compact_lower_gt_100000': bool(total.lower()>100000),
    'limitations': 'Full M3 lower follows with analytic tail and monotonicity argument; sharp LSI obstruction additionally needs domain bridge. No RH claim.'
}, indent=2))
