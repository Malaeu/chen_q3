"""CONFINE verdict audit: check displacement identity (6.3) K(n,k)=(beta_n-beta_k)/(n-k), beta_n=n K(n,0),
and measure Proshka's first unpaid G1a term (6.11)/(9.2): a, s=r^T C^{-1} r, Delta=a-s, for the derivative trial
v = X f_E/||X f_E|| in the odd block. DIAGNOSTIC_NEVER_A_PROOF.
"""
import sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402

mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); E, O = t.parity_bases(m); n = 2 * m + 1
    idx = list(range(-m, m + 1))
    beta = mp.matrix([idx[i] * K[i, m] for i in range(n)])
    disp = max(abs(K[i, j] * (idx[i] - idx[j]) - (beta[i] - beta[j])) for i in range(n) for j in range(n) if i != j)
    evE, VE = mp.eigsy(E.T * K * E); f = E * VE[:, 0]; lamE = evE[0]
    KO = O.T * K * O; evO, VO = mp.eigsy(KO); k = KO.rows
    alpha = sum(f[i] for i in range(n))
    z = O.T * mp.matrix([idx[i] * f[i] for i in range(n)]); d = mp.norm(z); v = z / d
    bO = O.T * beta
    A = KO - lamE * mp.eye(k)
    res = mp.norm(A * v + (alpha / d) * bO)          # (6.6) residual
    a = (v.T * A * v)[0]
    r = A * v - a * v
    # orthonormal basis of v-perp inside odd block: Gram-Schmidt on identity columns
    Bs = []
    for j in range(k):
        w = mp.matrix([1 if i == j else 0 for i in range(k)])
        w = w - (v.T * w)[0] * v
        for b in Bs:
            w = w - (b.T * w)[0] * b
        nw = mp.norm(w)
        if nw > mp.mpf(10) ** (-mp.mp.dps // 3):
            Bs.append(w / nw)
        if len(Bs) == k - 1:
            break
    P = mp.matrix(k, k - 1)
    for j, b in enumerate(Bs):
        for i in range(k):
            P[i, j] = b[i]
    C = P.T * A * P; rc = P.T * r
    evC = mp.eigsy(C)[0]
    s = (rc.T * mp.lu_solve(C, rc))[0]
    gap = evO[0] - lamE
    inv = 1 / (v.T * mp.lu_solve(A, v))[0]
    print(f"m={m}: disp_err={mp.nstr(disp,3)} res(6.6)={mp.nstr(res,3)} lamE={mp.nstr(lamE,5)} lam0O={mp.nstr(evO[0],5)} "
          f"a={mp.nstr(a,5)} s=r'C^-1 r={mp.nstr(s,5)} Delta=a-s={mp.nstr(a-s,5)} 1/(v'A^-1 v)={mp.nstr(inv,5)} Delta/gap={mp.nstr((a-s)/gap,8)} a/gap={mp.nstr(a/gap,5)} "
          f"s/a={mp.nstr(s/a,8)} crude(6.12) |r|^2/(minC*a)={mp.nstr((rc.T*rc)[0]/(evC[0]*a),4)} minC={mp.nstr(evC[0],4)} minC/gap={mp.nstr(evC[0]/gap,4)}", flush=True)
