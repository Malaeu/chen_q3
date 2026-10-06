"""Independent exact-rational reproduction of answer6 (21)-(22).

No floating-point or external libraries. Logarithm: positive atanh series
with geometric tail. Cosine: Taylor through degree 200, Lagrange remainder
using the vanishing degree-201 coefficient. Argument error costs at most
its radius since |cos'|<=1. This certifies an AUXILIARY kernel, not CCM.
"""
from fractions import Fraction as F
from math import factorial, isqrt


def log_ratio(q):
    assert 1 <= q <= 2
    z = (q - 1) / (q + 1)
    count = 50
    lower = 2 * sum((z ** (2*k+1) / (2*k+1) for k in range(count)), F(0))
    tail = 2*z**(2*count+1) / ((2*count+1)*(1-z*z))
    return lower, lower + tail


log2 = log_ratio(F(2))


def log_int(n):
    k = n.bit_length() - 1
    lo, hi = log_ratio(F(n, 2**k))
    return lo+k*log2[0], hi+k*log2[1]


def cos_interval(lo, hi):
    x, radius = (lo+hi)/2, (hi-lo)/2
    term = F(1)
    total = term
    for k in range(1, 101):
        term *= -x*x / ((2*k-1)*(2*k))
        total += term
    error = abs(x)**202 / factorial(202) + radius
    return max(F(-1), total-error), min(F(1), total+error)


def main():
    head_lo = head_hi = F(0)
    powers = []
    for p in range(2, 101):
        if any(p % d == 0 for d in range(2, isqrt(p)+1)):
            continue
        lp_lo, lp_hi = log_int(p)
        n, k = p, 1
        while n <= 100:
            c_lo, c_hi = cos_interval(10*k*lp_lo, 10*k*lp_hi)
            products = [a*b for a in (lp_lo, lp_hi) for b in (c_lo, c_hi)]
            head_lo += min(products) / n**2
            head_hi += max(products) / n**2
            powers.append(n)
            n, k = n*p, k+1
    assert len(powers) == 35
    coarse_lo, coarse_hi = F(115499356026, 10**12), F(115499356027, 10**12)
    assert coarse_lo < head_lo <= head_hi < coarse_hi
    lo100, hi100 = log_int(100)
    assert F(4605170185988, 10**12) < lo100 <= hi100 < F(4605170185989, 10**12)
    upper = F(2, 104)+F(1, 101)-coarse_lo+(F(4605170185989, 10**12)+1)/100
    assert upper == -F(3980476992010243, 131300000000000000)
    assert upper < -F(3, 100)
    assert F(6561, 800)*F(7, 22) > 2  # pi < 22/7
    print('PASS: 35 prime powers; exact head and log100 enclosures; v(10)<-3/100.')
    print('Coarse rational upper bound:', upper)


if __name__ == '__main__':
    main()
