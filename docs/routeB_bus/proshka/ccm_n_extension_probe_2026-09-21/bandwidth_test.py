"""Decisive: 0/4 packet at the LADDER bandwidth c = 2*pi*m, not c^2 = m.
Row vs cache direction at m=13 N=13, and Rayleigh a on K(13,13).
Cache reference: a = 4.22609145762e-16 (reproduced earlier on this K)."""
import json, sys, time
import mpmath as mp
sys.path.insert(0, '/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/ccm_n_extension_probe_2026-09-21')
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
mp.mp.dps = 160
import probe_n_extension as gk
from probe_n_extension import even_spheroidal

M, N = 13, 13
c2 = (2 * mp.pi * M) ** 2
KMODES, J = 130, 80
t0 = time.time()
chis, rows = even_spheroidal(c2, KMODES)
print(f"c^2={mp.nstr(c2,8)} chi0={mp.nstr(chis[0],12)} chi4={mp.nstr(chis[2],12)}  ({time.time()-t0:.0f}s)", flush=True)
def packet(idx):
    d = rows[idx]; p = max(range(len(d)), key=lambda i: abs(d[i])); d = [z/d[p] for z in d]
    return [((-1)**k) * d[k] for k in range(J)]
a0, a4 = packet(0), packet(2)
print("tail |a0[J-1]/max|:", mp.nstr(abs(a0[J-1]), 5), " |a4[J-1]/max|:", mp.nstr(abs(a4[J-1]), 5), flush=True)
q = gk.q_source_row_legendre(M, N, a0, a4)
print(f"row built ({time.time()-t0:.0f}s)", flush=True)

CACHE=('/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/ACTIVE/requests/'
       'routeB_twolevel_spectral_ladder/out/portable_k_coeffs_lambda_sq_13_N_13.json')
raw = json.load(open(CACHE))['coefficients']
cache_c = [mp.mpc(z['re'], z['im']) for z in raw]
def unit_c(v):
    n = mp.sqrt(mp.fsum(abs(z)**2 for z in v)); return [z/n for z in v]
qc, cc = unit_c(q), unit_c(cache_c)
dot = abs(mp.fsum(mp.conj(cc[i]) * qc[i] for i in range(len(qc))))
print(f"|<cache, row>| complex = {mp.nstr(dot, 20)}   1-|cos| = {mp.nstr(1-dot, 6)}", flush=True)
print(f"{'n':>4s} {'cache re':>16s} {'row re':>16s} {'cache im':>12s} {'row im':>12s}")
for i in (0, 6, 12, 13, 14, 20, 26):
    print(f"{i-N:>4d} {mp.nstr(mp.re(cc[i]),10):>16s} {mp.nstr(mp.re(qc[i]),10):>16s} {mp.nstr(mp.im(cc[i]),4):>12s} {mp.nstr(mp.im(qc[i]),4):>12s}")

mp.mp.dps = 60
K = gk.build_K(M, N)
Kn = mp.matrix(K.rows)
for i in range(K.rows):
    for j in range(K.rows): Kn[i,j] = mp.re(K[i,j])
def rayleigh(vec, label):
    v = mp.matrix(len(vec),1)
    for i,z in enumerate(vec): v[i] = mp.re(z)
    v = v/mp.sqrt(mp.fsum(v[i]**2 for i in range(v.rows)))
    a = (v.T*Kn*v)[0]; r = Kn*v - a*v
    print(f"{label:28s} a={mp.nstr(a,12):>18s}  |r|={mp.nstr(mp.sqrt(mp.fsum(r[i]**2 for i in range(r.rows))),8)}", flush=True)
rayleigh(cache_c, "CACHE row")
rayleigh(q, "0/4 packet at c=2*pi*m")
print(f"total {time.time()-t0:.0f}s")
