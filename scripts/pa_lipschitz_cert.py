#!/usr/bin/env python3
"""Compute Lipschitz bound for P_A(B_min, t_critical) on [-1/2, 1/2].

Outputs:
- max_deriv (grid of |P_A'(theta)|)
- L_ub (chosen safe upper bound)

This is numerical evidence for the Lipschitz certificate.
"""
import argparse
import mpmath as mp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--B", type=str, default="3")
    parser.add_argument("--t", type=str, default=str(mp.mpf(3) / 20))
    parser.add_argument("--N", type=int, default=4000)
    parser.add_argument("--dps", type=int, default=60)
    parser.add_argument("--out", type=str, default="")
    parser.add_argument("--L_ub", type=str, default="249.3")
    args = parser.parse_args()

    mp.mp.dps = args.dps
    B = mp.mpf(args.B)
    t = mp.mpf(args.t)
    L_ub = mp.mpf(args.L_ub)
    pi = mp.pi

    def a(xi):
        z = mp.mpf('0.25') + 1j * pi * xi
        return mp.log(pi) - mp.re(mp.digamma(z))

    def a_prime(xi):
        # a'(xi) = -pi * Im(psi'(1/4 + i*pi*xi))
        z = mp.mpf('0.25') + 1j * pi * xi
        return -pi * mp.im(mp.polygamma(1, z))

    def w(xi):
        if abs(xi) >= B:
            return mp.mpf('0')
        return max(mp.mpf('0'), 1 - abs(xi) / B) * mp.e ** (-4 * pi ** 2 * t * xi ** 2)

    def w_prime(xi):
        if abs(xi) >= B:
            return mp.mpf('0')
        hat = max(mp.mpf('0'), 1 - abs(xi) / B)
        c = 4 * pi ** 2 * t
        gauss = mp.e ** (-c * xi ** 2)
        if xi == 0:
            dhat = mp.mpf('0')
        else:
            dhat = -mp.sign(xi) / B
        dgauss = -2 * c * xi * gauss
        return dhat * gauss + hat * dgauss

    def g_prime(xi):
        return a_prime(xi) * w(xi) + a(xi) * w_prime(xi)

    def P_A_prime_abs_bound(theta):
        m_min = int(mp.floor(-B - theta))
        m_max = int(mp.ceil(B - theta))
        s = mp.mpf('0')
        for m in range(m_min, m_max + 1):
            xi = theta + m
            if abs(xi) < B + mp.mpf('1e-30'):
                s += abs(g_prime(xi))
        return 2 * pi * s

    N = args.N
    max_deriv = None
    theta_max = None
    for i in range(N + 1):
        theta = -mp.mpf('0.5') + mp.mpf(i) / N
        val = P_A_prime_abs_bound(theta)
        if (max_deriv is None) or (val > max_deriv):
            max_deriv = val
            theta_max = theta

    lines = []
    lines.append("Lipschitz cert for P_A at t_critical")
    lines.append("====================================")
    lines.append(f"B_min = {B}")
    lines.append(f"t_critical = {t}")
    lines.append(f"N = {N}")
    lines.append(f"max_deriv = {max_deriv}")
    lines.append(f"theta_max = {theta_max}")
    lines.append(f"L_ub = {L_ub}")
    out = "\n".join(lines)

    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(out)
    else:
        print(out)


if __name__ == "__main__":
    main()
