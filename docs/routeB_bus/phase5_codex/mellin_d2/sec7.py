"""Section 7: full-range m(h) with the analytic hhat, the exact floor, and the
polynomial pole-null tests h_k."""
import sys; sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import numpy as np, dens, tests
a=np.log(2.0); DM=0.020866
T1=np.load('t_tables.npz'); T2=np.load('t_tables_ext.npz')
xi=np.concatenate([T1['xi'],T2['xi']]); t2=np.concatenate([T1['t_2'],T2['t_2']])
g2=dens.gamma_S(xi,(2,)); lead=2*np.real(g2*t2)
n1=T1['xi'].size
def load(J, ext=True):
    O=np.load(f'op_two_J{J}.npz')
    q=O['quad']; m=O['mix']
    if ext:
        E=np.load(f'op_ext_J{J}.npz')
        q=np.concatenate([q,E['quad']]); m=np.concatenate([m,E['mix']])
    else:
        q=np.concatenate([q,np.zeros(xi.size-n1)]); m=np.concatenate([m,np.zeros(xi.size-n1,complex)])
    return lead+2*np.real(g2*m)-2*q
def Wof(kind,k=None):
    if kind=='bump':
        return (1-np.cos(a*xi))*tests.hhat2(xi,'bump')/1.6434228127646e8
    return tests.Wpoly(xi,k)
def integ(W,f,hi=None):
    m=np.ones(xi.size,bool) if hi is None else xi<=hi
    return 2*np.trapz((W*f)[m],xi[m])
def report(name,W,ds,cut):
    print(f"\n--- {name} ---")
    print(f"  phase mass 2*int W = {2*np.trapz(W,xi):.6f}  (2pi = {2*np.pi:.6f}, deficit {2*np.pi-2*np.trapz(W,xi):.6f})")
    for J,d in ds.items():
        print(f"  J={J}: m(h) = {-integ(W,d):+.6f}   (|xi|<=600 only: {-integ(W,d,600):+.6f})")
    print(f"  FLOOR  -int W 2Re(g2 t2) = {-integ(W,lead):+.6f}   (|xi|<=600: {-integ(W,lead,600):+.6f})")
    Js=sorted(ds); 
    if len(Js)>1: print(f"  J-spread: "+" ".join(f"J{Js[i]}-J{Js[i-1]}={-integ(W,ds[Js[i]])+integ(W,ds[Js[i-1]]):+.6f}" for i in range(1,len(Js))))
    mm=-integ(W,ds[Js[-1]])
    print(f"  vs delta_M = {DM}:  m - delta_M = {mm-DM:+.6f}  -> false factor {'SURVIVES' if mm>DM else 'DIES'} on this test")
    print(f"  fraction of W-mass below xi={cut}: {np.trapz(W[xi<=cut],xi[xi<=cut])/np.trapz(W,xi):.5f}")
if __name__=='__main__':
    ext = len(sys.argv)>1 and sys.argv[1]=='ext'
    ds={J:load(J,ext) for J in (7,8)}
    report("frozen h  (C^inf bump, delta0=(log3-log2)/8)", Wof('bump'), ds, 600)
    for k in (2,4):
        report(f"pole-null h_k, k={k}", Wof('poly',k), ds, 150)
