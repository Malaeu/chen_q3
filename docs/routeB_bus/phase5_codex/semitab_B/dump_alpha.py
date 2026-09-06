import numpy as np, json
from ops import SemiLocal
out = {}
for tag, sem in (('arch', False), ('semi', True)):
    sl = SemiLocal(2048, semilocal=sem, verbose=False)
    for lam in (1.0, np.sqrt(2.0), 2.0):
        pr = sl.pair(lam, tol=1e-8)
        out[f'{tag}_{lam:.4f}'] = pr['alpha'][:12].tolist()
        print(f"{tag} lam={lam:.4f} |alpha|_max={np.max(np.abs(pr['alpha'])):.12f} "
              f"nblk(>1e-6)={int((np.abs(pr['alpha'])>1e-6).sum())} nblk(>1e-8)={len(pr['alpha'])}")
        print("   ", np.array2string(pr['alpha'][:10], precision=8, max_line_width=200))
    del sl
json.dump(out, open('alpha_spectra.json', 'w'), indent=1)
