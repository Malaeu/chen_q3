"""NOESCAPE (4.8) discriminator: split k(e_m, v_i) into the sampled Xi tail F and the exterior part X.
DIAGNOSTIC_NEVER_A_PROOF. Literal K_m (full_center_probe.matrix_K), even sector, extra window modes |n| > m
only in the leakage sum (entries K_L(n, j) at the same L and prime cutoff; never added to the eigenproblem).
  T_i = -Z lam_i a_i                         (= Z k(e_m, v_i), radical identity (4.1))
  F_i = sum_{m<|n|<=M} (-1)^n L^-1/2 4Xi(omega_n) k(psi_n, v_i)      (Proshka (4.8))
  G_i = sum_{m<|n|<=M} c_n k(psi_n, v_i), c_n = true window coefficient of h
  X_i = T_i - F_i (closure, NOT the independent check asked in verdict §11); k(h_out, v_i) = T_i - G_i (closure)
  D_ext = |X_1| / |T_1|                      (verdict (4.17))
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
from radical_rayleigh import h  # noqa: E402

mp.mp.dps = int(sys.argv[1]); EXTRA = int(sys.argv[2])


def Xi(tt):
    s = mp.mpf(1) / 2 + 1j * tt
    return mp.re(s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s))


def mang(k):
    for p in range(2, k + 1):
        if any(p % d == 0 for d in range(2, int(p ** .5) + 1)):
            continue
        a = p
        while a < k:
            a *= p
        if a == k:
            return mp.log(p)
    return mp.mpf(0)


for m in [int(a) for a in sys.argv[3:]]:
    L = mp.log(m); b = L / 2; M = m + EXTRA
    K = t.fc.matrix_K(m); E, _ = t.parity_bases(m)
    ev, V = mp.eigsy(E.T * K * E); W = E * V
    with mp.workdps(mp.mp.dps):
        coef = {n: mp.quad(lambda x: h(x) * mp.cos(2 * mp.pi * n * (x + b) / L),
                           mp.linspace(-b, b, max(8, 2 * abs(n)) + 1)) / mp.sqrt(L) for n in range(-M, M + 1)}
    cin = mp.matrix([coef[n] for n in range(-m, m + 1)]); Z = mp.norm(cin); u = cin / Z
    # archimedean moments for every mode up to M (fine grid for high frequency)
    mom = {0: mp.mpf(0)}
    for n in range(1, M + 1):
        om = 2 * mp.pi * n / L
        sn = mp.quad(lambda x: om / 2 if not x else mp.exp(x / 2) * mp.sin(om * x) / (2 * mp.sinh(x)),
                     mp.linspace(0, L, max(8, 2 * n) + 1))
        mom[n] = sn; mom[-n] = -sn
    lam_k = [(k, mang(k) / mp.sqrt(k), mp.log(k)) for k in range(2, m + 1)]
    lam_k = [x for x in lam_k if x[1] != 0]

    def KL(n, v):
        w02 = 32 * L * mp.sinh(L / 4) ** 2 * (L ** 2 - 16 * mp.pi ** 2 * v * n) / ((L ** 2 + 16 * mp.pi ** 2 * v * v) * (L ** 2 + 16 * mp.pi ** 2 * n * n))
        wr = (mom[v] - mom[n]) / (mp.pi * (n - v))
        pr = mp.fsum(c * (mp.sin(2 * mp.pi * v * x / L) - mp.sin(2 * mp.pi * n * x / L)) / (mp.pi * (n - v)) for _, c, x in lam_k)
        return w02 - wr - pr

    assert [mang(k) for k in (3, 4, 6, 9)] == [mp.log(3), mp.log(2), 0, mp.log(3)]  # regression: early return bug 30.10
    # control: extended formula reproduces the literal in-window entries
    ctrl = max(abs(KL(n, v) - K[m + n, m + v]) for n in range(-m, m + 1) for v in range(-m, m + 1) if n != v)
    out = {"m": m, "M": M, "dps": mp.mp.dps, "Z": mp.nstr(Z, 12), "entry_ctrl": mp.nstr(ctrl, 3), "levels": []}
    tail = [n for n in range(-M, M + 1) if abs(n) > m]
    rows = {n: [KL(n, v) for v in range(-m, m + 1)] for n in tail}
    H = {n: 4 * Xi(2 * mp.pi * n / L) for n in tail}
    print(f'# m={m}: setup done', file=sys.stderr, flush=True)
    for i in range(4):
        vi = W[:, i]; a = mp.fsum(u[j] * vi[j] for j in range(2 * m + 1))
        T = -Z * ev[i] * a
        kpsi = {n: mp.fsum(rows[n][j] * vi[j] for j in range(2 * m + 1)) for n in tail}
        Fp, Gp, F, G = [], [], mp.mpf(0), mp.mpf(0)
        for k in range(m + 1, M + 1):
            for n in (k, -k):
                F += (-1) ** n / mp.sqrt(L) * H[n] * kpsi[n]
                G += coef[n] * kpsi[n]
            if k in (m + EXTRA // 3, m + 2 * EXTRA // 3, M):
                Fp.append(mp.nstr(F, 6)); Gp.append(mp.nstr(G, 6))
        X = T - F
        maxterm = max(abs(H[n] * kpsi[n]) / mp.sqrt(L) for n in tail)
        out["levels"].append({"i": i, "lam": mp.nstr(ev[i], 6), "a": mp.nstr(a, 6), "T": mp.nstr(T, 8),
                              "F": mp.nstr(F, 8), "F_partial": Fp, "G": mp.nstr(G, 8), "G_partial": Gp,
                              "X_closure": mp.nstr(X, 6), "k_hout_closure": mp.nstr(T - G, 6),
                              "D_ext": mp.nstr(abs(X) / abs(T), 6), "max_single_F_term": mp.nstr(maxterm, 4),
                              "cancellation_digits": mp.nstr(mp.log10(maxterm / abs(T)), 4)})
    print(json.dumps(out), flush=True)
