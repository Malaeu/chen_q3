#!/usr/bin/env python3
"""
Compute a grid + Lipschitz-style certificate for
P_A(B_min, t_critical, θ) on θ ∈ [-1/2, 1/2].

Outputs:
- min_grid
- theta_min
- Lipschitz bound estimate L via 2π * sum |g'(θ+m)|
- certificate: min_grid - L*h/2

This is numerical evidence to be turned into a formal certificate.
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
    args = parser.parse_args()

    mp.mp.dps = args.dps
    B = mp.mpf(args.B)
    t = mp.mpf(args.t)
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

    def g(xi):
        return a(xi) * w(xi)

    def g_prime(xi):
        return a_prime(xi) * w(xi) + a(xi) * w_prime(xi)

    def P_A(theta):
        m_min = int(mp.floor(-B - theta))
        m_max = int(mp.ceil(B - theta))
        s = mp.mpf('0')
        for m in range(m_min, m_max + 1):
            xi = theta + m
            if abs(xi) < B + mp.mpf('1e-30'):
                s += g(xi)
        return 2 * pi * s

    def P_A_prime_abs_bound(theta):
        m_min = int(mp.floor(-B - theta))
        m_max = int(mp.ceil(B - theta))
        s = mp.mpf('0')
        for m in range(m_min, m_max + 1):
            xi = theta + m
            if abs(xi) < B + mp.mpf('1e-30'):
                s += abs(g_prime(xi))
        return 2 * pi * s

    # Grid search for min P_A
    N = args.N
    min_val = None
    min_theta = None
    for i in range(N + 1):
        theta = -mp.mpf('0.5') + mp.mpf(i) / N
        val = P_A(theta)
        if (min_val is None) or (val < min_val):
            min_val = val
            min_theta = theta

    # Grid search for Lipschitz bound
    L = None
    L_theta = None
    for i in range(N + 1):
        theta = -mp.mpf('0.5') + mp.mpf(i) / N
        val = P_A_prime_abs_bound(theta)
        if (L is None) or (val > L):
            L = val
            L_theta = theta

    h = mp.mpf(1) / N
    c_star = mp.mpf(11) / 10
    cert = min_val - L * h / 2

    lines = []
    lines.append(f"B = {B}")
    lines.append(f"t = {t}")
    lines.append(f"grid N = {N}")
    lines.append(f"min P_A = {min_val}")
    lines.append(f"theta_min = {min_theta}")
    lines.append(f"Lipschitz (grid) L = {L}")
    lines.append(f"theta_L = {L_theta}")
    lines.append(f"h = {h}")
    lines.append(f"L*h/2 = {L * h / 2}")
    lines.append(f"certificate = {cert}")
    lines.append(f"margin (cert - c_star) = {cert - c_star}")
    out = "\n".join(lines)

    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(out)
    else:
        print(out)


if __name__ == "__main__":
    main()
