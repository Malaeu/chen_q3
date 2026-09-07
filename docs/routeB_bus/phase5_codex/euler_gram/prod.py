"""Production: Euler-Gram lower bound for k_2 on xi = 0(0.25)700."""
import sys, os, time, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import k2

def main(lo, hi, over, U, h, out, ximax=700.0):
    t0 = time.time()
    nodes = k2.make_nodes(lo, hi, over=over)
    print(f"nodes {nodes.size} in [{lo},{hi}] over={over}", flush=True)
    eg = k2.EulerGram(nodes, U=U, h=h, verbose=True)
    print(f"built n={nodes.size} rank={eg.rank} gram_err={eg.gram_error():.3e} "
          f"Gev=[{eg.gev.min():.4f},{eg.gev.max():.4f}] t={time.time()-t0:.0f}s", flush=True)
    XI = np.round(np.arange(0.0, ximax+1e-9, 0.25), 4)
    res = {}
    for s in range(0, XI.size, 400):
        e = min(s+400, XI.size)
        o = eg.eval(XI[s:e], full=False)
        for k, v in o.items():
            res.setdefault(k, []).append(v)
        print(f"  eval {e}/{XI.size} {time.time()-t0:.0f}s", flush=True)
    R = {k: np.concatenate(v) for k, v in res.items()}
    np.savez(out, nodes=nodes, rank=eg.rank, gev=eg.gev, gram_err=eg.gram_error(),
             U=U, h=h, over=over, lo=lo, hi=hi, **R)
    print(f"saved {out}  total {time.time()-t0:.0f}s", flush=True)

if __name__ == '__main__':
    lo, hi, over, U, h, out = (float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]),
                               float(sys.argv[4]), float(sys.argv[5]), sys.argv[6])
    main(lo, hi, over, U, h, out)
