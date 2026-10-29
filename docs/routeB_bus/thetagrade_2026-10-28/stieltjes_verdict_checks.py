"""Observer checks of PROSHKA_VERDICT_STIELTJES_2026-10-29. DIAGNOSTIC_NEVER_A_PROOF.

1. Identity (1.4) chi(t) = h^T adj(E - tI) e0 = det(O - tI) on literal cells, at t = lambda_min(E)
   and at two other points; plus the coefficient cone (4.2) of P(x) = det(O - lambda I + x I).
2. Plants (5.1), (5.4), (5.8), (7.3): rebuilt from (A_n, b_n) via K_nk = (b_n - b_k)/(n - k),
   K_nn = A_n and our own parity_bases, so the claim "same exact displacement class" is tested.
"""
import sys
from pathlib import Path

import mpmath as mp

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402


def adj_cofactor(E, h, e, tt):
    n = E.rows
    M = E - tt * mp.eye(n)
    # h^T adj(M) e = sum_ij h_i adj_ij e_j, adj_ij = (-1)^(i+j) det(M without row j, col i)
    s = 0
    for i in range(n):
        for j in range(n):
            if h[i] == 0 or e[j] == 0: continue
            rows = [r for r in range(n) if r != j]; cols = [c for c in range(n) if c != i]
            sub = mp.matrix([[M[r, c] for c in cols] for r in rows]) if n > 1 else mp.matrix([[1]])
            s += h[i] * (-1)**(i + j) * mp.det(sub) * e[j]
    return s


def blocks(K, m):
    E, O = t.parity_bases(m)
    return E.T * K * E, O.T * K * O


def structured_K(A, b):
    m = len(A) - 1; modes = range(-m, m + 1); n = 2 * m + 1
    Af = lambda k: A[abs(k)]; bf = lambda k: b[k] if k >= 0 else -b[-k]  # noqa: E731
    K = mp.zeros(n)
    for i, p in enumerate(modes):
        for j, q in enumerate(modes):
            K[i, j] = Af(p) if p == q else (bf(p) - bf(q)) / (p - q)
    return K


def report(name, K, m):
    Eb, Ob = blocks(K, m)
    ev_e, VE = mp.eigsy(Eb); ev_o = mp.eigsy(Ob, eigvals_only=True)
    h = mp.matrix([1] + [mp.sqrt(2)] * m)
    w = [(h.T * VE[:, i])[0] * VE[0, i] for i in range(m + 1)]
    W = [mp.fsum(w[:k + 1]) for k in range(m + 1)]
    print(f"{name}: even={[mp.nstr(x, 6) for x in ev_e]} odd={[mp.nstr(x, 6) for x in ev_o]} "
          f"G1a={ev_e[0] < ev_o[0]} w0={mp.nstr(w[0], 6)} W={[mp.nstr(x, 6) for x in W]}")
    return Eb, Ob


if __name__ == "__main__":
    mp.mp.dps = 120
    for m in (3, 6, 9):
        K = t.fc.matrix_K(m); Eb, Ob = blocks(K, m)
        lam = mp.eigsy(Eb, eigvals_only=True)[0]
        h = mp.matrix([1] + [mp.sqrt(2)] * m); e = mp.matrix([1] + [0] * m)
        errs = []
        for tt in (lam, lam - 1, mp.mpf('0.37')):
            chi = adj_cofactor(Eb, h, e, tt); pO = mp.det(Ob - tt * mp.eye(m))
            errs.append(mp.nstr(abs(chi - pO) / abs(pO), 3))
        # coefficients of P(x) = det(O - lam I + x I) = prod (x + d_j)
        d = [mu - lam for mu in mp.eigsy(Ob, eigvals_only=True)]
        c = [mp.mpf(1)]
        for dj in d: c = [a + b for a, b in zip([0] + c, [x * dj for x in c] + [0])]
        print(f"literal m={m}: chi vs p_O rel err at (lam, lam-1, 0.37) = {errs}; "
              f"min c_k = {mp.nstr(min(c), 4)}; chi(lam) = det(O-lam) = {mp.nstr(mp.det(Ob - lam * mp.eye(m)), 4)}")
    mp.mp.dps = 50
    s2 = mp.sqrt(2)
    Eb, _ = report("plant 5.1 (expect w0>0, G1a False)", structured_K([4, 0, 0], [0, 1, 1]), 2)
    print("   E matches (5.1):", mp.nstr(mp.mnorm(Eb - mp.matrix([[4, s2, 1/s2], [s2, 1, mp.mpf(2)/3], [1/s2, mp.mpf(2)/3, mp.mpf(1)/2]]), 1), 3))
    report("plant 5.4 (expect G1a True, W1<0)", structured_K([mp.mpf(-2)/3, 0, 0], [0, 1, 1]), 2)
    report("plant 5.8 (expect degenerate bottom, G1a False)", structured_K([0, 0, 1], [0, 0, 0]), 2)
    K73 = mp.matrix([[0, 1, 1], [1, 4, 1], [1, 1, 0]]); T73 = mp.matrix([[1, 1, 0], [1, 4, 1], [0, 1, 1]])
    print("plant 7.3: K from (A0=4,A1=0,b1=1) equals displayed K:", mp.mnorm(structured_K([4, 0], [0, 1]) - K73, 1) == 0,
          " [T,K]=0:", mp.mnorm(T73 * K73 - K73 * T73, 1) == 0)
    report("plant 7.3 (expect odd ground, G1a False)", K73, 1)
