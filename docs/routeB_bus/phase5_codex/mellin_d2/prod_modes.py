"""Mode-power sums for the monotone lower-bound sequence (judge's representation).

gamma = e^{i phi};  z = e^{-i phi/2} u_S(xi) = x + i y  (x,y real).
d_S = 2Re{gamma t_S} - 2<x,(I+A)^{-1}x> - 2<y,(I-A)^{-1}y>
    = ell - sum_{n>=0} ( <x,T_x^n x> + <y,T_y^n y> ),   T_x=(I-A)/2, T_y=(I+A)/2.
In the eigenbasis of A:  <x,T_x^n x> = sum_m x_m^2 ((1-lam_m)/2)^n,  likewise for y.
Stored per xi: Sx[n], Sy[n] for n = 0..NMAX, plus the closed-form total.
"""
import sys, time, numpy as np
sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import core, dens
NMAX = 200

def run(J, N, out, ximax=610.0, XI=None):
    t0=time.time()
    betas, cs = core.kernel_coeffs(2, J)
    u, w, A = core.build_A(N, betas, cs)
    lam, V = np.linalg.eigh(A)
    keep = np.abs(lam) < 1.0-1e-12
    lam, V = lam[keep], V[:, keep]
    print(f"[J{J}] alpha={np.abs(lam).max():.9f} dropped={int((~keep).sum())} eig {time.time()-t0:.0f}s", flush=True)
    vq, wq = dens.fine_grid(ximax, betas.max())
    G = dens.build_G(u, betas, cs, vq, wq)
    print(f"[J{J}] v-nodes={vq.size} {time.time()-t0:.0f}s", flush=True)
    sw=np.sqrt(w); logv=np.log(vq); vm=vq**-0.5
    if XI is None: XI=np.round(np.arange(0.0,600.0001,0.25),4)
    tx=(1.0-lam)/2.0; ty=(1.0+lam)/2.0
    Px=tx[:,None]**np.arange(NMAX+1)[None,:]      # (M, NMAX+1)
    Py=ty[:,None]**np.arange(NMAX+1)[None,:]
    Sx=np.zeros((XI.size,NMAX+1)); Sy=np.zeros((XI.size,NMAX+1))
    tot=np.zeros(XI.size); un2=np.zeros(XI.size)
    from scipy.special import loggamma
    blk=200
    for s in range(0,XI.size,blk):
        e=min(s+blk,XI.size); xs=XI[s:e]
        F=(vm[None,:]*np.exp(1j*np.outer(xs,logv)))/np.sqrt(2*np.pi)
        B=(F@G.T)*sw[None,:]                       # (blk, N) = u_S on nodes
        Bn=B@V                                     # (blk, M) coefficients b_n
        g=np.exp(-1j*xs*np.log(np.pi)+loggamma(0.25+0.5j*xs)-loggamma(0.25-0.5j*xs))
        for p in (2,):
            a_=np.log(p); r_=p**-0.5
            g=g*(1-r_*np.exp(1j*a_*xs))/(1-r_*np.exp(-1j*a_*xs))
        Z=Bn*np.sqrt(np.conj(g))[:,None]
        X2=Z.real**2; Y2=Z.imag**2
        Sx[s:e]=X2@Px; Sy[s:e]=Y2@Py
        tot[s:e]=(X2@(2.0/(1.0+lam)))+(Y2@(2.0/(1.0-lam)))
        un2[s:e]=X2.sum(1)+Y2.sum(1)
        if s % 1000 == 0: print(f"[J{J}] xi={xs[0]} {time.time()-t0:.0f}s", flush=True)
    np.savez(out, xi=XI, Sx=Sx, Sy=Sy, total=tot, unorm2=un2, lam=lam, J=J, N=N, NMAX=NMAX)
    print(f"[J{J}] saved {out} {time.time()-t0:.0f}s", flush=True)

if __name__=='__main__':
    J=int(sys.argv[1]); N=int(sys.argv[2]); run(J,N,f'modes_J{J}.npz')
