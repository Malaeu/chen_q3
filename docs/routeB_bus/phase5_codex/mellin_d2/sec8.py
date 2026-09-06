"""Section 8: monotone lower bounds M_N = B_0 + sum_{n<=N} C_n."""
import sys; sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import numpy as np, dens, tests
a=np.log(2.0); DM=0.020866
T1=np.load('t_tables.npz'); T2=np.load('t_tables_ext.npz')
xi=np.concatenate([T1['xi'],T2['xi']]); t2=np.concatenate([T1['t_2'],T2['t_2']])
g2=dens.gamma_S(xi,(2,)); lead=2*np.real(g2*t2)
xm=T1['xi']; nm=xm.size                                   # mode grid [0,600]
E=np.load('op_ext_cheap_J8.npz')
gx=dens.gamma_S(xi[nm:],(2,))
tot_ext=2*np.interp(xi[nm:],E['xi'],E['quad'])-2*np.real(gx*(
        np.interp(xi[nm:],E['xi'],E['mix'].real)+1j*np.interp(xi[nm:],E['xi'],E['mix'].imag)))
MOD={J:np.load(f'modes_J{J}.npz') for J in (7,8)}
NS=[0,1,2,5,10,20,50,100,200]
def Wfull(kind,k=None):
    return ((1-np.cos(a*xi))*tests.hhat2(xi,'bump')/1.6434228127646e8) if kind=='bump' else tests.Wpoly(xi,k)
def run(name,W):
    print(f"\n### {name}")
    B0=-2*np.trapz(W*lead,xi)
    ext=2*np.trapz(W[nm:]*tot_ext,xi[nm:])
    print(f"  B_0 = -int W_h 2Re(gamma_2 t_2)  (full range, exact scalars) = {B0:+.6f}")
    print(f"  contribution of |xi|>600 (all n, from quad/mix)             = {ext:+.6f}")
    rows={}
    for J in (7,8):
        M=MOD[J]; S=M['Sx']+M['Sy']; c=np.cumsum(S,axis=1)
        Cn=np.array([2*np.trapz(W[:nm]*S[:,n],xm) for n in range(S.shape[1])])
        full=2*np.trapz(W[:nm]*M['total'],xm)
        rows[J]=dict(Cn=Cn,full=full,MN=[B0+Cn[:n+1].sum()+ext for n in NS],
                     m=B0+full+ext)
    print(f"  C_0 = int W ||u_2||^2 : J=7 {rows[7]['Cn'][0]:+.6f}   J=8 {rows[8]['Cn'][0]:+.6f}")
    print(f"  m(h) (all n)          : J=7 {rows[7]['m']:+.6f}   J=8 {rows[8]['m']:+.6f}")
    print("   N    M_N(J=8)     M_N(J=7)    spread     frac of m    M_N > delta_M?")
    cross=None
    for i,n in enumerate(NS):
        m8=rows[8]['MN'][i]; m7=rows[7]['MN'][i]
        ok = m8>DM and m7>DM
        if cross is None and ok: cross=n
        print(f"  {n:4d}  {m8:+.6f}   {m7:+.6f}   {m8-m7:+.2e}   {m8/rows[8]['m']:.5f}     {'YES' if ok else 'no'}")
    print(f"  -> M_N exceeds delta_M={DM} first at N = {cross}" if cross is not None else
          f"  -> M_N never exceeds delta_M={DM} up to N={NS[-1]} (limit m={rows[8]['m']:+.6f})")
if __name__=='__main__':
    run("frozen h (C^inf bump)", Wfull('bump'))
    run("h_2 = (d^2-1/4) eta_2", Wfull('poly',2))
    run("h_4 = (d^2-1/4) eta_4", Wfull('poly',4))
