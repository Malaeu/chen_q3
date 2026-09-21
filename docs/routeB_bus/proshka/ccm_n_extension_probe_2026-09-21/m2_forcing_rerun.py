"""Grok's forcing kill (eta rises with N at m=2) was run at c^2=m=2. Rerun at the
ladder bandwidth c = 2*pi*m = 4*pi (c^2 = 157.9). Does eta still rise?"""
import sys, time
import mpmath as mp
sys.path.insert(0, '/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/ccm_n_extension_probe_2026-09-21')
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
mp.mp.dps = 120
import probe_n_extension as gk
from probe_n_extension import even_spheroidal
M = 2; c2 = (2*mp.pi*M)**2; J = 60
chis, rows = even_spheroidal(c2, 100)
def packet(idx):
    d = rows[idx]; p = max(range(len(d)), key=lambda i: abs(d[i])); d = [z/d[p] for z in d]
    return [((-1)**k)*d[k] for k in range(J)]
a0, a4 = packet(0), packet(2)
print(f"m={M} c^2={mp.nstr(c2,8)} chi0={mp.nstr(chis[0],10)} chi4={mp.nstr(chis[2],10)} tail={mp.nstr(abs(a0[J-1]),4)}", flush=True)
mp.mp.dps = 40
etas = []
for N in (1, 2, 3, 4, 6, 8, 12):
    q = gk.q_source_row_legendre(M, N, a0, a4)
    K = gk.build_K(M, N)
    mm = gk.measures(K, q)
    etas.append(mm['eta'])
    print(f"N={N} dim={mm['dim']} a={mp.nstr(mm['a'],8)} eta={mp.nstr(mm['eta'],8)} beta={mp.nstr(mm['beta'],8)} gap={mp.nstr(mm['gap'],8)} e={mp.nstr(mm['excess'],8)} Delta-2e={mp.nstr(mm['sufficient'],8)}", flush=True)
print("ETA_SEQUENCE", [float(e) for e in etas], "STRICTLY_FALLING", all(etas[i+1] < etas[i] for i in range(len(etas)-1)))
