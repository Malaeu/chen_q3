"""Is the window-selected radical vector a Gaussian smoothing of h, i.e. Fourier 4 xi(1/2 - iz) e^{-s z^2}? DIAGNOSTIC.
e^{-s z^2} ~ 1 - s z^2 + s^2 z^4 / 2 and -z^2 <-> d^2/dx^2, so f = h + s h'' + (s^2/2) h'''' (odd: h' + s h''' + (s^2/2) h^(5)).
Plateau weights (pingeom_fit, m = 24, normalisation c_i ||D_i||) are converted back to raw c_i; test c_2 / c_0 = (c_1 / c_0)^2 / 2
and equality of s between the sectors.
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
N = 600; X = 2.6; xs = [-X + 2 * X * (k + 0.5) / N for k in range(N)]; dx = 2 * X / N
nrm = {k: mp.sqrt(sum(mp.diff(h, x, k)**2 for x in xs) * dx) for k in range(6)}
for name, ks, w in (("even m=24", (0, 2, 4), ("0.99857", "0.053274", "0.0035853")), ("even m=20", (0, 2, 4), ("0.99858", "0.053222", "0.0034541")),
                    ("odd m=24", (1, 3, 5), ("0.9938", "0.11081", "0.0090408")), ("odd m=20", (1, 3, 5), ("0.99383", "0.11056", "0.0086986"))):
    c = [mp.mpf(wi) / nrm[k] for wi, k in zip(w, ks)]
    s = c[1] / c[0]; pred = s * s / 2; obs = c[2] / c[0]
    print(f"{name}: s = c1/c0 = {mp.nstr(s, 6)}   c2/c0 observed = {mp.nstr(obs, 6)}   predicted s^2/2 = {mp.nstr(pred, 6)}   ratio = {mp.nstr(obs / pred, 5)}")
