"""Operator part of (6) by Nystrom on GL nodes; NO rescaling, NO clipping.
Stores per-xi: <u,Zu> and <u,A Z ubar> over the modes with |lambda|<1 (exact lambda),
the top-K modes' lambda and b_n = <psi_n,u> for post-processing, and ||u||^2."""
import sys, time, numpy as np
sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import core, dens
KTOP = 10

def run(tag, p, J, N, ximax=610.0, out=None):
    t0 = time.time()
    betas, cs = core.kernel_coeffs(p, J)
    u, w, A = core.build_A(N, betas, cs)
    lam, V = np.linalg.eigh(A)
    o = np.argsort(-np.abs(lam)); lam, V = lam[o], V[:, o]
    print(f"[{tag}] N={N} beta_max={betas.max():.1f} alpha_raw={np.abs(lam).max():.9f} "
          f"eig {time.time()-t0:.0f}s", flush=True)
    vq, wq = dens.fine_grid(ximax, betas.max())
    G = dens.build_G(u, betas, cs, vq, wq)
    print(f"[{tag}] fine v-nodes={vq.size} G {G.nbytes/1e9:.2f} GB {time.time()-t0:.0f}s", flush=True)
    sw = np.sqrt(w); logv = np.log(vq); vm = vq**-0.5
    XI = np.round(np.arange(0.0, 600.0001, 0.25), 4)
    keep = np.abs(lam) < 1.0 - 1e-12
    lk = lam[keep]; den = 1.0 - lk**2
    quad = np.zeros(XI.size); mix = np.zeros(XI.size, complex)
    un2 = np.zeros(XI.size); BT = np.zeros((XI.size, KTOP), complex)
    for i, xi in enumerate(XI):
        f = (vm*np.exp(1j*xi*logv))/np.sqrt(2*np.pi)
        b = sw*(G @ f)
        bn = V.T @ b
        bk = bn[keep]
        quad[i] = float(np.sum(np.abs(bk)**2/den).real)
        mix[i] = np.sum(lk*np.conj(bk)**2/den)
        un2[i] = float(np.sum(np.abs(bn)**2).real)
        BT[i] = bn[:KTOP]
        if i % 600 == 0: print(f"[{tag}] xi={xi} {time.time()-t0:.0f}s", flush=True)
    np.savez(out, xi=XI, quad=quad, mix=mix, unorm2=un2, lam=lam, btop=BT,
             ndrop=int((~keep).sum()), J=J, N=N)
    print(f"[{tag}] saved {out} ndrop={int((~keep).sum())} total {time.time()-t0:.0f}s", flush=True)

if __name__ == '__main__':
    if sys.argv[1] == 'inf':
        run('inf', None, 0, 800, out='op_inf.npz')
    else:
        J = int(sys.argv[2]); N = int(sys.argv[3])
        run(f'two_J{J}', 2, J, N, out=f'op_two_J{J}.npz')
