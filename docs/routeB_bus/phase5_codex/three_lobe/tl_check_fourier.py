"""Independent channel 2 (Fourier): archimedean part as (1/2pi) int q_inf conj(f_i^) f_j^,
q_inf(xi) = Re psi(1/4 + i xi/2) - log pi.  FFT + Simpson, float64.
Compared entrywise against the spatial route Arch = D - c_A G.  The Gram, recomputed
from the same transforms by Plancherel, is the convergence gauge (its exact value is known)."""
import sys, time
import numpy as np
from scipy.special import digamma
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe')

def phi_np(x, delta):
    w = 2*x/delta; s = 2.0/delta
    out = np.zeros((3,) + np.shape(x))
    m = np.abs(w) < 1
    ww = w[m]; d1 = 1 - ww*ww
    g  = np.exp(-1/d1)
    g1 = g*(-2*ww/d1**2)
    g2 = g*((4*ww*ww)/d1**4 - 2/d1**2 - 8*ww*ww/d1**3)
    out[0][m] = g; out[1][m] = g1*s; out[2][m] = g2*s*s - g/4
    return out

def transforms(delta, NPOW=25, samp=512):
    N = 1 << NPOW; dx = delta/samp; L = N*dx; x0 = delta
    idx = np.arange(int((x0-delta/2)/dx)-2, int((x0+delta/2)/dx)+3)
    xs = idx*dx - x0
    ph = phi_np(xs, delta)
    xi = 2*np.pi*np.arange(N//2+1)/L
    F = []
    for j in range(3):
        u = np.zeros(N); u[idx] = ph[j]
        F.append(np.fft.rfft(u)*dx)
        del u
    corr = np.exp(1j*xi*x0)
    F = [f*corr for f in F]
    return xi, F

def assemble(xi, F, centers, xi_max):
    dxi = xi[1]-xi[0]
    M = int(xi_max/dxi)
    if M % 2: M -= 1
    sl = slice(0, M+1)
    x = xi[sl]; Fs = [f[sl] for f in F]
    q = digamma(0.25 + 0.5j*x).real - np.log(np.pi)
    sw = np.ones(M+1); sw[1:-1:2] = 4; sw[2:-1:2] = 2; sw *= dxi/3
    A = np.zeros((9,9)); G = np.zeros((9,9))
    for p in range(3):
        for r in range(3):
            e = np.exp(1j*x*(centers[p]-centers[r]))
            for j in range(3):
                for k in range(3):
                    v = np.real(e*np.conj(Fs[j])*Fs[k])
                    A[3*p+j,3*r+k] = np.sum(sw*q*v)/np.pi
                    G[3*p+j,3*r+k] = np.sum(sw*v)/np.pi
    return A, G, x[-1]

if __name__ == '__main__':
    import mpmath as mp
    from tl_cache import get
    t0 = time.time()
    r = get(dps=50); P = r['P']
    delta = float(P['delta']); centers = [float(c) for c in P['centers']]
    Ar = np.array([[float(r['Arch'][i,j]) for j in range(9)] for i in range(9)])
    Gs = np.array([[float(r['G'][i,j])    for j in range(9)] for i in range(9)])
    sc = np.sqrt(np.outer(np.diag(Gs), np.diag(Gs)))
    xi, F = transforms(delta)
    print('grid: dxi=%.5f  Nyquist=%.0f  (%.1fs)' % (xi[1]-xi[0], xi[-1], time.time()-t0))
    for xm in (4000, 8000, 15000, 25000, 31000):
        A, G, xr = assemble(xi, F, centers, xm)
        print('xi_max %6.0f | arch dev(G-scaled) %.3e | gram dev(G-scaled) %.3e | %.0fs'
              % (xr, np.max(np.abs(A-Ar)/sc), np.max(np.abs(G-Gs)/sc), time.time()-t0))
    np.save('/home/chirurgie/.claude/jobs/4b35770d/tmp/three_lobe/arch_fourier.npy', A)
