"""Production 2: Euler-Gram k_2 with the FULL two-sided residual sandwich.

Lower: k_2 >= |b|^2 p^H G^{-1} p            (Galerkin in span{K(xi_j,.)})
Upper: k_2 <= |b|^2 (E + |z|^2/g0),  |z|^2 = k_inf - 2Re<w,Gy> + |Gy|^2,
       |Gy|^2 = (1+r^2)^2|y|^2 - 2(1+r^2) r Re<y,psi> + r^2 |P psi|^2,
       |P psi|^2 EXACT through the orthogonal complement (pperp).
"""
import sys, os, time, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import k2, pperp

def main(lo, hi, over, U, h, out, ximax=700.0, npan=500, step=0.25):
    t0 = time.time()
    nodes = k2.make_nodes(lo, hi, over=over)
    print(f"nodes {nodes.size} in [{lo},{hi}] over={over} U={U} h={h}", flush=True)
    eg = k2.EulerGram(nodes, U=U, h=h)
    print(f"built rank={eg.rank} gram_err={eg.gram_error():.3e} "
          f"Gev=[{eg.gev.min():.4f},{eg.gev.max():.4f}] t={time.time()-t0:.0f}s", flush=True)
    comp = pperp.Complement(npan=npan)
    print(f"complement grid {comp.u.size}, alpha={np.abs(comp.lam).max():.10f}", flush=True)
    up = comp.u[comp.n2:]                      # u in (1/2,1)
    W = pperp.wphys(eg.fk, nodes, 2*up)        # (ns, n)
    gam = np.exp(2j*pperp.fastk.theta_RS(nodes))
    Fa = W @ eg.B                              # (ns, rank)
    Fb = (W.conj()*gam[None, :]) @ eg.B
    print(f"wphys done {time.time()-t0:.0f}s", flush=True)
    XI = np.round(np.arange(0.0, ximax+1e-9, step), 4)
    XeAll = eg._Xext(XI)
    print(f"Xext done {time.time()-t0:.0f}s", flush=True)
    XeB = (XeAll @ eg.B).T                     # (rank, nXI)
    r = eg.r; s1 = 1+r*r
    res = {}
    CH = 350
    for s in range(0, XI.size, CH):
        e = min(s+CH, XI.size)
        x0 = XI[s:e]
        D0 = eg.fk.data(x0)
        P = eg.fk.block(D0, eg.Dn)
        pt = eg.B.conj().T @ P.T
        ct = eg.Gti @ pt
        E = np.real(np.einsum('im,im->m', pt.conj(), ct))
        kinf = eg.fk.diag(D0)
        cmpl = np.real(np.einsum('im,im->m', pt.conj(), pt))
        ny2 = np.real(np.einsum('im,im->m', ct.conj(), ct))
        Xc = eg.Xt @ ct
        ypsi = np.real(np.einsum('im,im->m', ct.conj(), Xc))
        npsi2 = np.real(np.einsum('im,im->m', ct.conj(), (eg.B.conj().T @ eg.Y @ eg.B) @ ct)) \
            if False else np.real(np.einsum('im,im->m', ct.conj(), eg.Yt @ ct))
        Ppsi_lo = np.real(np.einsum('im,im->m', Xc.conj(), Xc))
        ma = np.zeros((comp.u.size, x0.size), complex); mb = np.zeros_like(ma)
        ma[comp.n2:] = np.sqrt(2.0)*(Fa @ ct)
        mb[comp.n2:] = np.sqrt(2.0)*(Fb @ ct)
        corr = comp.proj_sq(ma, mb)
        Ppsi = npsi2 - corr
        wpsi = np.einsum('im,im->m', XeB[:, s:e], ct)
        wGy = s1*E - r*wpsi
        Gy2 = s1*s1*ny2 - 2*s1*r*ypsi + r*r*Ppsi
        z2 = kinf - 2*np.real(wGy) + Gy2
        b2 = k2.babs2(x0, eg.a, eg.r)
        res.setdefault('xi', []).append(x0)
        for k, v in dict(kinf=kinf, E=E, comp=cmpl, b2=b2, ny2=ny2, ypsi=ypsi,
                         npsi2=npsi2, Ppsi_lo=Ppsi_lo, Ppsi=Ppsi, z2=z2,
                         k2_lo=b2*E, k2_hi=b2*(E+np.maximum(z2, 0)/k2.G0)).items():
            res.setdefault(k, []).append(v)
        print(f"  eval {e}/{XI.size} {time.time()-t0:.0f}s  z2 range [{z2.min():.2e},{z2.max():.2e}]"
              f"  Ppsi-Ppsi_lo range [{(Ppsi-Ppsi_lo).min():.2e},{(Ppsi-Ppsi_lo).max():.2e}]", flush=True)
    R = {k: np.concatenate(v) for k, v in res.items()}
    np.savez(out, nodes=nodes, rank=eg.rank, gev=eg.gev, gram_err=eg.gram_error(),
             U=U, h=h, over=over, lo=lo, hi=hi, **R)
    print(f"saved {out} total {time.time()-t0:.0f}s", flush=True)

if __name__ == '__main__':
    a = sys.argv
    main(float(a[1]), float(a[2]), float(a[3]), float(a[4]), float(a[5]), a[6],
         ximax=float(a[7]) if len(a) > 7 else 700.0)
