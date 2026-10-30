"""CONFINE probes. DIAGNOSTIC_NEVER_A_PROOF.
(1) Confinement law: compare lam0 of each sector with tail functionals of the plateau radical vector f_inf
    (even: 0.9986 h + 0.0533 h'' + 0.0036 h'''', odd: 0.9938 h' + 0.1108 h''' + 0.0090 h^(5), weights c_i ||D_i||):
    T1 = int_{|x|>L/2} f^2,  T2 = f(L/2)^2. Reports lam0, T1, T2, lam0/T1, lam0/T2.
(2) Heat flow: best one-parameter fit of the even bottom by e^{t x^2} h (de Bruijn-Newman deformation of the Polya kernel),
    residual compared with the radical-family fit (pingeom_fit.py, 2e-6 .. 2.4e-4).
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402

def h(x):
    x = abs(x); s = mp.mpf(0); n = 1
    while True:
        e2 = mp.e**(2 * x) * n * n
        if mp.pi * e2 > 3 * mp.mp.dps + 400: break
        s += (16 * mp.pi**2 * e2**2 - 24 * mp.pi * e2) * mp.e**(-mp.pi * e2); n += 1
    return mp.e**(x / 2) * s

W = {"E": ((0, 2, 4), (mp.mpf("0.9986"), mp.mpf("0.0533"), mp.mpf("0.0036"))),
     "O": ((1, 3, 5), (mp.mpf("0.9938"), mp.mpf("0.1108"), mp.mpf("0.0090")))}
mp.mp.dps = int(sys.argv[1])
with mp.workdps(40):
    NG = 1200; XG = 3.2; gx = [-XG + 2 * XG * (k + 0.5) / NG for k in range(NG)]; gdx = 2 * XG / NG
    norms = {k: mp.sqrt(sum(mp.diff(h, x, k)**2 for x in gx) * gdx) for k in range(6)}
def finf(S, x):
    ks, ws = W[S]
    with mp.workdps(mp.mp.dps + 20):
        return sum(w / norms[k] * mp.diff(h, x, k) for k, w in zip(ks, ws))
with mp.workdps(40):
    fnorm = {S: mp.sqrt(sum(finf(S, x)**2 for x in gx) * gdx) for S in "EO"}
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m)
    row = {"m": m}
    for S, B in (("E", E), ("O", O)):
        ev, V = mp.eigsy(B.T * K * B); lam = ev[0]
        T1 = 2 * mp.quad(lambda x: finf(S, x)**2, [L / 2, L / 2 + 0.5, L / 2 + 2]) / fnorm[S]**2
        T2 = finf(S, L / 2)**2 / fnorm[S]**2
        row[S] = {"lam0": mp.nstr(lam, 6), "T1": mp.nstr(T1, 6), "T2": mp.nstr(T2, 6),
                  "lam_over_T1": mp.nstr(lam / T1, 6), "lam_over_T2": mp.nstr(lam / T2, 6)}
        if S == "E":
            f = B * V[:, 0]; xs = [-L / 2 + L * (k + 0.5) / 240 for k in range(240)]
            fc = [sum(f[j] * mp.exp(2j * mp.pi * (j - m) * (x + L / 2) / L) for j in range(2 * m + 1)) for x in xs]
            kk = max(range(240), key=lambda i: abs(fc[i])); ph = fc[kk] / abs(fc[kk]); y = [mp.re(v / ph) for v in fc]
            hx = [h(x) for x in xs]
            def res(tt):
                g = [mp.e**(tt * x * x) * hv for x, hv in zip(xs, hx)]
                c = sum(a * b for a, b in zip(y, g)) / sum(b * b for b in g)
                return mp.sqrt(sum((a - c * b)**2 for a, b in zip(y, g)) / sum(a * a for a in y))
            best = min((res(mp.mpf(k) / 400), mp.mpf(k) / 400) for k in range(-200, 201))
            lo = best[1] - mp.mpf(1) / 400; hi = best[1] + mp.mpf(1) / 400
            for _ in range(40):
                a1 = lo + (hi - lo) / 3; a2 = hi - (hi - lo) / 3
                if res(a1) < res(a2): hi = a2
                else: lo = a1
            tt = (lo + hi) / 2
            row["heat"] = {"t_best": mp.nstr(tt, 6), "rel_residual": mp.nstr(res(tt), 4), "residual_t0_pure_h": mp.nstr(res(0), 4)}
    print(json.dumps(row), flush=True)
