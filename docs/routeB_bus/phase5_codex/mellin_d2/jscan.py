import sys, time, numpy as np, mpmath as mp
sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import core, dens

def t_trunc(xi, p, J, dps=40):
    tot = mp.mpf(-1)/p*core.J_closed(2*mp.pi/p, -xi, dps)
    for j in range(J+1):
        tot += (1-mp.mpf(1)/p)*core.J_closed(2*mp.pi*mp.mpf(p)**j, -xi, dps)
    return complex(tot/mp.pi)

XIS = [4.0, 8.0, 16.0, 30.0, 60.0, 120.0]
r = 2**-0.5
th = np.linspace(0, 2*np.pi, 400001)
for J in [int(x) for x in sys.argv[1:]] or [4,5,6,7]:
    m = (1-r*r)*sum(r**j*np.exp(1j*j*th) for j in range(J+1)) - r*np.exp(-1j*th)
    sup = float(np.abs(m).max())
    betas, cs = core.kernel_coeffs(2, J)
    N = int(4*betas.max()); N = max(N, 800)
    t0 = time.time()
    u, w, A = core.build_A(N, betas, cs)
    lam, V = np.linalg.eigh(A)
    a0 = np.abs(lam).max()
    vq, wq = dens.fine_grid(130.0, betas.max())
    G = dens.build_G(u, betas, cs, vq, wq)
    sw = np.sqrt(w); logv = np.log(vq); vm = vq**-0.5
    print(f"\n=== J={J} N={N} beta_J={betas.max():.1f} sup|m_J|={sup:.6f} alpha_raw={a0:.6f} "
          f"vnodes={vq.size} build={time.time()-t0:.0f}s")
    for scale_name, sc in [("/sup|m_J|", sup), ("alpha->1-1e-4", a0/(1-1e-4))]:
        L = lam/sc; den = 1.0-L**2
        print(f"  scale {scale_name}: alpha={np.abs(L).max():.8f}  1/(1-a^2)={1/den.min():.4g}")
        for xi in XIS:
            f = (vm*np.exp(1j*xi*logv))/np.sqrt(2*np.pi)
            vt = sw*(G @ f)                 # = A^{(J)} f_xi  (the vector u_S)
            c = V.T @ vt / sc               # coefficients of u = A f  under scaled A
            quad = float(np.sum(np.abs(c)**2/den).real)
            mixed = np.sum(L*np.conj(c)**2/den)
            t = t_trunc(xi, 2, J)
            g = dens.gamma_S(np.array([xi]), (2,))[0]
            d = 2*np.real(g*(t+mixed)) - 2*quad
            print(f"    xi={xi:6.1f} d2={d:+.6f}  2Re(g t)={2*np.real(g*t):+.6f} "
                  f" 2Re(g mix)={2*np.real(g*mixed):+.6f}  -2quad={-2*quad:+.6f}")
