import numpy as np, time
from semilocal import build

def FS_polar(N, verbose=True):
    C, F, Dil = build(N)
    n = N+1
    Jinv = np.eye(n)-Dil
    J = np.linalg.inv(Jinv)
    G = J.T@J
    w, U = np.linalg.eigh(G)
    Gmh = (U*(w**-0.5))@U.T
    V = J@Gmh
    FS = V@F@V.T
    FSraw = J@F@Jinv
    if verbose:
        print(f"  N={N}: ||V^TV-I||={np.abs(V.T@V-np.eye(n)).max():.2e}  "
              f"||F_S-F_S^T||={np.abs(FS-FS.T).max():.2e}  ||F_S^2-I||={np.abs(FS@FS-np.eye(n)).max():.2e}  "
              f"||JFJ^-1 - VFV^*||_2={np.linalg.norm(FSraw-FS,2):.3e}")
        print(f"     ||B_S|| bounds: sigma_min(Jinv^T)={np.linalg.svd(Jinv,compute_uv=False)[-1]:.6f} "
              f"sigma_max={np.linalg.svd(Jinv,compute_uv=False)[0]:.6f}  (a_S={1-2**-0.5:.6f}, b_S={1+2**-0.5:.6f})")
    return C, F, FS

if __name__ == "__main__":
    for N in [800, 1600, 3200]:
        t0=time.time(); C, F, FS = FS_polar(N); 
        lam=1.0; nl=int(round(lam/C.delta)); m=nl+1
        ev=np.linalg.eigvalsh(0.5*(FS[:m,:m]+FS[:m,:m].T)); i=np.argsort(-np.abs(ev))
        print(f"     alpha_n(F_S) lam=1: {np.array2string(ev[i][:8],precision=7)}   [{time.time()-t0:.0f}s]")
