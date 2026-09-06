"""Error bar for N_S: recompute N_S with the SYMMETRISED F_S and report the difference.
This propagates the semilocal model defect ||F_S - F_S^T|| directly into N_S."""
import sys, json, time
import numpy as np
import tests
from ops import SemiLocal, theta_matrix, quantities

N = int(sys.argv[1]) if len(sys.argv) > 1 else 4096
only = sys.argv[2:] if len(sys.argv) > 2 else None
fam = [(n, v, a) for (n, v, a) in tests.family()] + [(n, v, a) for (n, v, a) in tests.family_extra()]
if only:
    fam = [x for x in fam if any(k in x[0] for k in only)]
q = json.load(open('quad_results.json'))
sl = SemiLocal(N, semilocal=True)
pr_raw = sl.pair(1.0)
pr_sym = sl.pair(1.0, use_sym=True)
print(f"blocks raw={len(pr_raw['alpha'])} sym={len(pr_sym['alpha'])}", flush=True)
out = {}
for name, v, a in fam:
    t0 = time.time()
    T = theta_matrix(sl.M, v)
    n2 = q[name]['norm2']
    r1 = quantities(pr_raw, T, n2)
    r2 = quantities(pr_sym, T, n2)
    d = abs(r1['N_S'] - r2['N_S'])
    out[name] = dict(N_raw=r1['N_S'], N_sym=r2['N_S'], dN=d,
                     rel=d / max(abs(r1['N_S']), 1e-300), Q=q[name]['Q'])
    print(f"{name:40s} N_raw={r1['N_S']:+.6f} N_sym={r2['N_S']:+.6f} |dN|={d:.3e} "
          f"rel={d/max(abs(r1['N_S']),1e-300):.2e}  [{time.time()-t0:.0f}s]", flush=True)
    del T
json.dump(out, open(f'bar_N{N}.json', 'w'), indent=1)
