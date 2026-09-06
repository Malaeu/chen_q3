"""THEOREM_CONTROL_CC20: S={inf}, lambda=1, supp v in [-log2/2, log2/2],
int v = A_+ = A_- = 0.  CC20 Thm 1/6.11 => Q(v) >= N_inf(k), i.e. E_inf <= 0."""
import sys, json, time
import numpy as np
import tests
from quad import Quad
from ops import SemiLocal, theta_matrix, quantities

Ns = [int(x) for x in sys.argv[1:]] or [4096]
fam = tests.family_thm()
qr = {}
for name, v, a in fam:
    q = Quad(v, a, dx=2e-5)
    D = q.D(ngl=400, nseg=12)
    Q, pall = q.Qform(Dval=D) if hasattr(q, 'Qform') else (None, None)
    r = q.all(Sf=(2,))
    qr[name] = r
    print(f"{name:32s} ||v||^2={r['norm2']:.8f} D={r['D']:.6f} L_inf={r['base']:+.6f} "
          f"P02={r['P02']:+.2e} prime_all={r['prime_all']:+.2e} Q={r['Q']:+.6f}", flush=True)

res = {}
for N in Ns:
    sl = SemiLocal(N, semilocal=False)
    pr = sl.pair(1.0)
    print(f"  N={N}: nblk={len(pr['alpha'])}, alpha={np.array2string(pr['alpha'][:5],precision=6)}",
          flush=True)
    for name, v, a in fam:
        T = theta_matrix(sl.M, v)
        r = quantities(pr, T, qr[name]['norm2'])
        L = qr[name]['base']
        res.setdefault(name, {})[N] = dict(N_S=r['N_S'], E_S=r['E_S'], NmE=r['N_S'] - r['E_S'],
                                           L=L, resid=r['N_S'] - r['E_S'] - L)
        print(f"    {name:32s} N_inf={r['N_S']:+.6f} E_inf={r['E_S']:+.6f} "
              f"E/N={r['E_S']/r['N_S']:+.4f} N-E={r['N_S']-r['E_S']:+.6f} L={L:+.6f} "
              f"res={r['N_S']-r['E_S']-L:+.2e}", flush=True)
        del T
    del sl
json.dump({k: {str(n): vv for n, vv in d.items()} for k, d in res.items()},
          open('thm_results.json', 'w'), indent=1)
json.dump({k: {kk: (float(x) if not isinstance(x, complex) else abs(x)) for kk, x in v.items()}
           for k, v in qr.items()}, open('thm_quad.json', 'w'), indent=1)
