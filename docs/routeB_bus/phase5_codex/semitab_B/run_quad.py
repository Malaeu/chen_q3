import numpy as np, time, json, sys
import tests
from quad import Quad, C_A

fam = [(n, v, a, 'main') for (n, v, a) in tests.family()] + \
      [(n, v, a, 'extra') for (n, v, a) in tests.family_extra()]
res = {}
print(f"c_A = {C_A:.15f}")
for name, v, a, tag in fam:
    t0 = time.time()
    dx = 1e-4 if a <= 3.5 else 2e-4
    q = Quad(v, a, dx=dx)
    r = q.all()
    r['a'] = a
    r['dx'] = dx
    res[name] = {k: (float(x) if not isinstance(x, complex) else [x.real, x.imag])
                 for k, x in r.items()}
    print(f"{name:42s} |v|^2={r['norm2']:.8f} D={r['D']:.8f} base={r['base']:+.8f} "
          f"pS={r['prime_S']:+.8f} L_S={r['L_S']:+.8f} P02={r['P02']:+.8f} "
          f"pall={r['prime_all']:+.8f} Q={r['Q']:+.8e}  P02err={abs(r['P02']-r['P02_alt']):.2e} "
          f"[{time.time()-t0:.1f}s]", flush=True)
json.dump(res, open('quad_results.json', 'w'), indent=1)
