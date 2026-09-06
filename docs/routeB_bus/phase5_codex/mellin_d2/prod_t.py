"""t_S(xi) on the production grid from the closed forms (verdict (10)); parallel."""
import sys, numpy as np, mpmath as mp
from multiprocessing import Pool
sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import core

JU = 55
XI = np.round(np.arange(0.0, 600.0001, 0.25), 4)

def t_inf(xi):
    return complex(core.J_closed(2*mp.pi, -float(xi), 40)/mp.pi)

def t_two(xi):
    xi = float(xi); p = 2
    tot = mp.mpf(-1)/p*core.J_closed(2*mp.pi/p, -xi, 40)
    for j in range(JU+1):
        tot += (1-mp.mpf(1)/p)*core.J_closed(2*mp.pi*mp.mpf(p)**j, -xi, 40)
    return complex(tot/mp.pi)

def tail_bound(xi):
    """Tail of the scalar series beyond J_U, SCALARFLOOR verdict (32) with the PROVED uniform
    constant 256 of Theorem 4 (31): |J(beta,xi)| <= 256 beta^{-1/2} (1 + log beta).
    History: the first version used parent (13) with the shape constant set to 1. That constant is
    FALSE: J(beta,0) ~ beta^{-1/2}[Gamma(1/2)cos(pi/4) log beta + 4.43], so |J| sqrt(beta)/(1+log beta)
    tends to 1.2533 at xi = 0 (1.33 at beta_56); the stored bound 3.499e-8 was 0.75x the true
    truncation error at xi = 0 (checked 2026-09-07 by summation and by asymptotics). The bound is
    uniform in xi; the argument is kept for interface compatibility."""
    r = 2**-0.5; a = np.log(2.0)
    bJ1 = 2*np.pi*2.0**(JU+1)
    return (128/(np.pi*np.sqrt(2*np.pi)))*r**(JU+1)*((1+np.log(bJ1))/(1-r) + a*r/(1-r)**2)

if __name__ == '__main__':
    with Pool(22) as P:
        ti = np.array(P.map(t_inf, XI, chunksize=8))
        print('t_inf done', flush=True)
        t2 = np.array(P.map(t_two, XI, chunksize=4))
    np.savez('t_tables.npz', xi=XI, t_inf=ti, t_2=t2,
             tail=np.array([tail_bound(x) for x in XI]))
    print('saved', XI.size, 'max tail bound', max(tail_bound(x) for x in XI))
