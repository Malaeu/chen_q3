"""t_S(xi) on the extension grid xi = 600.5(0.5)3000."""
import sys, numpy as np, mpmath as mp
from multiprocessing import Pool
sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import core
JU = 55
XI = np.round(np.arange(600.5, 3000.0001, 0.5), 4)
def t_two(xi):
    xi=float(xi); p=2
    tot = mp.mpf(-1)/p*core.J_closed(2*mp.pi/p, -xi, 40)
    for j in range(JU+1):
        tot += (1-mp.mpf(1)/p)*core.J_closed(2*mp.pi*mp.mpf(p)**j, -xi, 40)
    return complex(tot/mp.pi)
def t_inf(xi):
    return complex(core.J_closed(2*mp.pi, -float(xi), 40)/mp.pi)
if __name__=='__main__':
    with Pool(22) as P:
        ti=np.array(P.map(t_inf, XI, chunksize=8)); print('t_inf ext done',flush=True)
        t2=np.array(P.map(t_two, XI, chunksize=4))
    np.savez('t_tables_ext.npz', xi=XI, t_inf=ti, t_2=t2)
    print('saved',XI.size,flush=True)
