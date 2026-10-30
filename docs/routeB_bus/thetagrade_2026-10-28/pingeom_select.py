"""Which element of the xi-radical family does the window select? DIAGNOSTIC_NEVER_A_PROOF.
Candidates in span{h, h'', h''''} (even) / {h', h''', h^(5)} (odd): minimisers of int w(x) f^2 / int f^2 for
w = x^2, x^4, cosh(x), e^{2|x|}. Weights reported in the same normalisation as pingeom_fit.py (c_i * ||D_i||).
Target plateau (m = 20..24): even (0.9986, 0.0533, 0.0036), odd (0.9938, 0.1108, 0.0090).
"""
import mpmath as mp
mp.mp.dps = 30
def h(x):
    x = abs(x); s = mp.mpf(0); n = 1
    while True:
        e2 = mp.e**(2 * x) * n * n
        if mp.pi * e2 > 120: break
        s += (16 * mp.pi**2 * e2**2 - 24 * mp.pi * e2) * mp.e**(-mp.pi * e2); n += 1
    return mp.e**(x / 2) * s
N = 400; X = 2.6; xs = [-X + 2 * X * (k + 0.5) / N for k in range(N)]; dx = 2 * X / N
D = {k: [mp.diff(h, x, k) for x in xs] for k in range(6)}
weights = {"x^2": lambda x: x * x, "x^4": lambda x: x**4, "cosh x": mp.cosh, "e^{2|x|}": lambda x: mp.e**(2 * abs(x))}
for name, ks in (("even", (0, 2, 4)), ("odd", (1, 3, 5))):
    G0 = mp.matrix(3, 3); nrm = [mp.sqrt(sum(v * v for v in D[k]) * dx) for k in ks]
    for i in range(3):
        for j in range(3): G0[i, j] = sum(D[ks[i]][p] * D[ks[j]][p] for p in range(N)) * dx
    for wn, w in weights.items():
        W = mp.matrix(3, 3); wx = [w(x) for x in xs]
        for i in range(3):
            for j in range(3): W[i, j] = sum(wx[p] * D[ks[i]][p] * D[ks[j]][p] for p in range(N)) * dx
        Lc = mp.cholesky(G0); Li = Lc**-1; ev, V = mp.eigsy(Li * W * Li.T); c = Li.T * V[:, 0]
        v = [c[i] * nrm[i] for i in range(3)]; s = mp.sqrt(sum(a * a for a in v)); sg = 1 if v[0] > 0 else -1
        print(name, wn, [mp.nstr(sg * a / s, 5) for a in v])
