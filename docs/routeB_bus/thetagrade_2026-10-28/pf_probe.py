"""Perron-Frobenius probe: is the bottom eigenfunction of G = K - W02 (pole term removed) positive on the window?
DIAGNOSTIC_NEVER_A_PROOF. Literature agent 29.10 (own derivation, unverified): archimedean part = Levy-Khintchine
generator, prime part = negative shifts, so exp(-tG) may be positivity improving; only the rank-2 pole term W02 obstructs.
Matrix as full_center_probe.matrix_K: K = w02 - wr - prime in modes -m..m, basis exp(2 pi i n x / L) on [0, L].
Reports, for G and K: bottom eigenvalue, sector of the bottom (E/O), sign changes of the bottom function on the
interior grid, min/max of the function, and lambda_min of even and odd blocks.
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402

def parts(m):
    K = t.fc.matrix_K(m); L = mp.log(m); modes = range(-m, m + 1); n = 2 * m + 1
    W = mp.zeros(n)
    for i, a in enumerate(modes):
        for j, b in enumerate(modes):
            W[i, j] = 32 * L * mp.sinh(L / 4)**2 * (L**2 - 16 * mp.pi**2 * a * b) / ((L**2 + 16 * mp.pi**2 * a * a) * (L**2 + 16 * mp.pi**2 * b * b))
    return K, W, L

def bottom_function(M, m, L, grid=400, margin=0.02):
    ev, V = mp.eigsy(M); c = V[:, 0]
    xs = [L * (margin + (1 - 2 * margin) * k / grid) for k in range(grid + 1)]
    fc = [sum(c[j] * mp.exp(2j * mp.pi * (j - m) * x / L) for j in range(2 * m + 1)) for x in xs]
    # Real odd coefficients synthesize an imaginary odd function (MARKOV verdict 2.5): remove a common phase, never mp.re alone.
    k = max(range(len(fc)), key=lambda i: abs(fc[i])); ph = fc[k] / abs(fc[k])
    f = [y / ph for y in fc]
    assert max(abs(mp.im(y)) for y in f) < mp.mpf(10)**(-mp.mp.dps // 2) * max(abs(y) for y in f), "phase not common"
    f = [mp.re(y) for y in f]
    if sum(f) < 0: f = [-y for y in f]
    changes = sum(1 for a, b in zip(f, f[1:]) if a * b < 0)
    E, O = t.parity_bases(m)
    sec = "E" if mp.norm(E.T * c) > mp.norm(O.T * c) else "O"
    return ev[0], sec, changes, min(f), max(f)

if __name__ == "__main__":
    mp.mp.dps = int(sys.argv[1]); out = []
    for m in [int(a) for a in sys.argv[2:]]:
        K, W, L = parts(m); G = K - W
        E, O = t.parity_bases(m)
        row = {"m": m}
        for name, M in (("G", G), ("K", K)):
            lam, sec, ch, fmin, fmax = bottom_function(M, m, L)
            le = mp.eigsy(E.T * M * E, eigvals_only=True)[0]; lo = mp.eigsy(O.T * M * O, eigvals_only=True)[0]
            row[name] = {"bottom": mp.nstr(lam, 6), "sector": sec, "sign_changes": ch,
                         "fmin_over_fmax": mp.nstr(fmin / fmax, 4), "lam_E": mp.nstr(le, 6), "lam_O": mp.nstr(lo, 6),
                         "even_below_odd": bool(le < lo)}
        print(json.dumps(row), flush=True)
