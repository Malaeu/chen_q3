"""Window floor vs theta tail: does lambda_a track the cut-off mass of the null test Phi?

Single centre 0, half-width a, Legendre degrees < K, full Weil form Q (Arch + primes + pole), Gram G.
lambda_a = min generalised eigenvalue of (Q, G) on the window.
Phi(x) = sum_n (2 pi^2 n^4 e^{9x/2} - 3 pi n^2 e^{5x/2}) e^{-pi n^2 e^{2x}} (Titchmarsh 10.1; F_Phi(it) = Xi(t), Q[Phi] = 0).
T(a)   = int_{|x|>a} Phi^2 / int Phi^2            (relative tail mass)
R(a)   = Q[Phi 1_(-a,a)] / ||Phi 1_(-a,a)||^2      (Rayleigh of the cut null test on the Legendre space)
Compare d log lambda_a / da with d log T / da and d log R / da (finite differences on the grid).
DIAGNOSTIC_NEVER_A_PROOF, floating point.
"""
import sys, json, time
import numpy as np, scipy.linalg as sla
from scipy.integrate import quad
from numpy.polynomial import legendre as Lg
sys.path.insert(0, '/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre')
from sc_build import build

def Phi(x, N=8):
    x = np.asarray(x, float); s = np.zeros_like(x)
    for n in range(1, N+1):
        s += (2*np.pi**2*n**4*np.exp(4.5*x) - 3*np.pi*n**2*np.exp(2.5*x))*np.exp(-np.pi*n**2*np.exp(2*x))
    return s

def phi_even(x):
    """Phi is even (theta functional equation); evaluate the series on |x| >= 0 where 8 terms converge to double precision.
    (The series at negative arguments needs ~e^{-x} terms: Phi(-6) with 8 terms is garbage — bug of the first run.)"""
    return Phi(np.abs(np.asarray(x, float)))

def coeffs(a, K):
    """Legendre coefficients c_k of Phi on (-a,a): Phi(a u) ~ sum c_k P_k(u)."""
    x, w = np.polynomial.legendre.leggauss(K+40)
    f = phi_even(a*x)
    c = np.array([(2*k+1)/2*np.sum(w*f*Lg.legval(x, np.eye(K)[k])) for k in range(K)])
    return c

total = quad(lambda x: phi_even(x)**2, -6, 6, limit=400)[0]
def tail(a):
    return 2*quad(lambda x: phi_even(x)**2, a, 6, limit=400)[0]/total

grid = [float(v) for v in sys.argv[1].split(',')] if len(sys.argv) > 1 else [0.35,0.40,0.45,0.50,0.55,0.60,0.65,0.70,0.75,0.80]
K = int(sys.argv[2]) if len(sys.argv) > 2 else 36
TAG = sys.argv[3] if len(sys.argv) > 3 else ''
H = float(sys.argv[4]) if len(sys.argv) > 4 else 0.02
XI = float(sys.argv[5]) if len(sys.argv) > 5 else 20000.0
out = {}
mats = {}   # 2026-09-09, Proshka DISTANCE §9(c): keep Q, G, eigenpairs and the cut-Phi coefficients per a
for a in grid:
    t0 = time.time()
    R = build([0.0], K, h=H, XI=XI, delta=a, verbose=False)
    Q, G = R['Q'], R['G']
    ev, V = sla.eigh(Q, G)
    c = coeffs(a, K)
    ray = float(c@Q@c/(c@G@c))
    v0 = V[:,0]; ov = float(abs(v0@G@c)/np.sqrt((v0@G@v0)*(c@G@c)))
    T = tail(a)
    mats[f'{a:.2f}'] = dict(Q=Q, G=G, ev=ev, V=V, c=c)
    out[f'{a:.2f}'] = dict(a=a, K=K, h=H, XI=XI, lam1=float(ev[0]), lam2=float(ev[1]), lam3=float(ev[2]),
                           rayleigh_cutPhi=ray, tail_mass=T, overlap_ground_cutPhi=ov,
                           atoms=[n for n,_,_ in R['atoms']], secs=time.time()-t0)
    print(f"a={a:.2f} K={K} lam1={ev[0]:.4e} lam2={ev[1]:.4e} R(cutPhi)={ray:.4e} T={T:.4e} lam1/T={ev[0]/T:.4f} R/T={ray/T:.4f} ov={ov:.4f} atoms={out[f'{a:.2f}']['atoms']} {time.time()-t0:.0f}s", flush=True)
json.dump(out, open(f'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/window_derivative_K{K}{TAG}.json','w'), indent=1)
np.savez_compressed(f'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/window_derivative_K{K}{TAG}_matrices.npz', **{f'{k}_{m}': v for k, d in mats.items() for m, v in d.items()})
# finite-difference log-derivatives
keys = sorted(out, key=float)
print("\n a      dlog(lam1)/da   dlog(R)/da   dlog(T)/da   -2pi e^{2a}")
for i in range(1, len(keys)):
    p, q = out[keys[i-1]], out[keys[i]]; da = q['a']-p['a']; am = 0.5*(p['a']+q['a'])
    f = lambda k: (np.log(abs(q[k]))-np.log(abs(p[k])))/da
    print(f"{am:.3f}  {f('lam1'):12.3f}  {f('rayleigh_cutPhi'):12.3f}  {f('tail_mass'):12.3f}  {-2*np.pi*np.exp(2*am):12.3f}")
