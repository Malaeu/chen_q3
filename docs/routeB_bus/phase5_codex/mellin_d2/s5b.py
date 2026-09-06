"""S5 with component breakdown and error budget."""
import sys; sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import numpy as np, dens
a=np.log(2.0); H=1.6434228127646e8
C=np.load('/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/density_fine_N4096.npy')
T=np.load('t_tables.npz'); xi=T['xi']; Di=np.load('d_inf.npz')
W=(1-np.cos(a*xi))*C[4]/H
mass=2*np.trapz(W,xi); tail=2*np.pi-mass
def I(f): return 2*np.trapz(W*f,xi)
g2=dens.gamma_S(xi,(2,))
print(f"phase-marginal mass on |xi|<=600: {mass:.6f} of 2pi={2*np.pi:.6f}; missing {tail:.6f}")
rows={}
for J in [6,7,8]:
    try: O=np.load(f'op_two_J{J}.npz')
    except Exception: continue
    lead=2*np.real(g2*T['t_2']); mixt=2*np.real(g2*O['mix']); qt=-2*O['quad']
    d=lead+mixt+qt
    rows[J]=dict(m=-I(d), lead=-I(lead), mix=-I(mixt), quad=-I(qt), d=d,
                 sup=np.abs(d[xi>=500]).max(), un2=O['unorm2'])
    print(f"\nJ={J}:  m(h) = -int W_h d_2 = {-I(d):+.6f}")
    print(f"    from 2Re(g t_2)      : {-I(lead):+.6f}")
    print(f"    from 2Re(g <u,AZu*>) : {-I(mixt):+.6f}")
    print(f"    from -2<u,Zu>        : {-I(qt):+.6f}   (always >= 0)")
    print(f"    int W_h (d_2-d_inf)  : {I(d-Di['d']):+.6f}   B(h)=w+that = {a/np.sqrt(2)+I(d-Di['d']):+.6f}")
    print(f"    sup|d_2| on [500,600]= {rows[J]['sup']:.4e} -> |tail(|xi|>600)| <= {tail*rows[J]['sup']:.4e}")
print(f"\nA(h) = -int W_h d_inf = {-I(Di['d']):+.6f};  w = a/sqrt2 = {a/np.sqrt(2):+.6f}")
Js=sorted(rows)
if len(Js)>1:
    print("J-spread of m(h):", " ".join(f"J{Js[k]}-J{Js[k-1]}={rows[Js[k]]['m']-rows[Js[k-1]]['m']:+.5f}" for k in range(1,len(Js))))
