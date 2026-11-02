"""SHAKE: how sharply does the Weil-window sign depend on where the primes sit? DIAGNOSTIC_NEVER_A_PROOF.
Hellmann-Feynman on the literal CCM matrix K_m (full_center_probe.matrix_K): prime entry -c_k q(log k, n, v).
For each prime p: shift log p -> log p + eps (powers p^j shift by j eps, Beurling-style generalized prime), and
scale its weights c_{p^j} -> (1 + delta) c_{p^j}. Reports d lam0 / d eps and d lam0 / d delta for the even bottom
lam0(K_E) and the odd bottom lam0(K_O), next to lam0 itself. One finite-difference control per cell.
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402

def q(x, n, j, L):
    if n == j: return 2 * (L - x) / L * mp.cos(2 * mp.pi * n * x / L)
    return (mp.sin(2 * mp.pi * j * x / L) - mp.sin(2 * mp.pi * n * x / L)) / (mp.pi * (n - j))

def dq(x, n, j, L):
    w = lambda k: 2 * mp.pi * k / L
    if n == j: return -2 / L * mp.cos(w(n) * x) - 2 * (L - x) / L * w(n) * mp.sin(w(n) * x)
    return (w(j) * mp.cos(w(j) * x) - w(n) * mp.cos(w(n) * x)) / (mp.pi * (n - j))

def prime_powers(p, m):
    out, j = [], 1
    while p**j <= m: out.append((j, p**j)); j += 1
    return out

def form(vec, fn, m, L):
    modes = range(-m, m + 1); s = mp.mpf(0)
    for a, n in enumerate(modes):
        for b, v in enumerate(modes):
            s += vec[a] * vec[b] * fn(n, v)
    return s

if __name__ == "__main__":
    mp.mp.dps = int(sys.argv[1])
    for m in [int(a) for a in sys.argv[2:]]:
        K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m)
        row = {"m": m}
        for name, B in (("E", E), ("O", O)):
            ev, V = mp.eigsy(B.T * K * B); f = B * V[:, 0]; lam = ev[0]
            sens = {}
            for p in [k for k in range(2, m + 1) if all(k % d for d in range(2, k))]:
                pw = prime_powers(p, m)
                d_eps = form(f, lambda n, v: -sum(j * mp.mangoldt(k) / mp.sqrt(k) * dq(mp.log(k), n, v, L) for j, k in pw), m, L)
                d_del = form(f, lambda n, v: -sum(mp.mangoldt(k) / mp.sqrt(k) * q(mp.log(k), n, v, L) for j, k in pw), m, L)
                sens[p] = (d_eps, d_del)
            # finite-difference control: shift log 2 by h (powers too), recompute sector bottom
            h = mp.mpf(10)**(-mp.mp.dps // 3)
            dK = mp.matrix(K.rows)
            for a, n in enumerate(range(-m, m + 1)):
                for b, v in enumerate(range(-m, m + 1)):
                    dK[a, b] = -sum(mp.mangoldt(k) / mp.sqrt(k) * (q(mp.log(k) + j * h, n, v, L) - q(mp.log(k), n, v, L)) for j, k in prime_powers(2, m))
            fd = (mp.eigsy(B.T * (K + dK) * B, eigvals_only=True)[0] - lam) / h
            row[name] = {"lam0": mp.nstr(lam, 5), "fd_check_p2": mp.nstr(fd, 6), "hf_p2": mp.nstr(sens[2][0], 6),
                         "d_lam_d_eps": {p: mp.nstr(s[0], 4) for p, s in sens.items()},
                         "d_lam_d_delta": {p: mp.nstr(s[1], 4) for p, s in sens.items()},
                         "max_ratio_eps_over_lam": mp.nstr(max(abs(s[0]) for s in sens.values()) / lam, 4)}
        print(json.dumps(row), flush=True)
