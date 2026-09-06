"""Operator part of (6) on the extension grid xi = 600.5(0.5)3000, J=8 Nystrom."""
import sys, time, numpy as np
sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import core, dens
def run(J, N, out):
    t0=time.time()
    betas, cs = core.kernel_coeffs(2, J)
    u, w, A = core.build_A(N, betas, cs)
    lam, V = np.linalg.eigh(A)
    o=np.argsort(-np.abs(lam)); lam,V=lam[o],V[:,o]
    print(f"alpha_raw={np.abs(lam).max():.9f} eig {time.time()-t0:.0f}s",flush=True)
    vq, wq = dens.fine_grid(3010.0, betas.max())
    G = dens.build_G(u, betas, cs, vq, wq)
    print(f"v-nodes={vq.size} G {G.nbytes/1e9:.2f} GB {time.time()-t0:.0f}s",flush=True)
    sw=np.sqrt(w); logv=np.log(vq); vm=vq**-0.5
    XI=np.round(np.arange(600.5,3000.0001,0.5),4)
    keep=np.abs(lam)<1.0-1e-12; lk=lam[keep]; den=1.0-lk**2
    quad=np.zeros(XI.size); mix=np.zeros(XI.size,complex); un2=np.zeros(XI.size)
    for i,xi in enumerate(XI):
        f=(vm*np.exp(1j*xi*logv))/np.sqrt(2*np.pi)
        bn=V.T@(sw*(G@f)); bk=bn[keep]
        quad[i]=float(np.sum(np.abs(bk)**2/den).real)
        mix[i]=np.sum(lk*np.conj(bk)**2/den)
        un2[i]=float(np.sum(np.abs(bn)**2).real)
        if i%1000==0: print(f"xi={xi} {time.time()-t0:.0f}s",flush=True)
    np.savez(out, xi=XI, quad=quad, mix=mix, unorm2=un2, lam=lam, J=J, N=N)
    print(f"saved {out} {time.time()-t0:.0f}s",flush=True)
if __name__=='__main__':
    run(int(sys.argv[1]), int(sys.argv[2]), f'op_ext_J{sys.argv[1]}.npz')
