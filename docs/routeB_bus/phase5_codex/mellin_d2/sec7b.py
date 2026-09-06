"""Section 7 final: full-range m(h) with analytic hhat + operator extension to xi=3000."""
import sys; sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import numpy as np, dens, tests
a=np.log(2.0); DM=0.020866
T1=np.load('t_tables.npz'); T2=np.load('t_tables_ext.npz')
xi=np.concatenate([T1['xi'],T2['xi']]); t2=np.concatenate([T1['t_2'],T2['t_2']])
g2=dens.gamma_S(xi,(2,)); lead=2*np.real(g2*t2); n1=T1['xi'].size
E=np.load('op_ext_cheap_J8.npz')
# validation of the cheap grid on the overlap [400,600]
O8=np.load('op_two_J8.npz')
ov=(E['xi']>=400)&(E['xi']<=600)
idx=np.searchsorted(O8['xi'],E['xi'][ov])
print("overlap check [400,600] cheap vs accurate (J=8):")
print(f"  max |dquad| = {np.abs(E['quad'][ov]-O8['quad'][idx]).max():.3e}  (typ quad {O8['quad'][idx].mean():.3e})")
print(f"  max |dmix|  = {np.abs(E['mix'][ov]-O8['mix'][idx]).max():.3e}")
def dfull(J):
    O=np.load(f'op_two_J{J}.npz')
    q=np.interp(xi,np.concatenate([O['xi'],E['xi'][E['xi']>600]]),
                   np.concatenate([O['quad'],E['quad'][E['xi']>600]]))
    mr=np.interp(xi,np.concatenate([O['xi'],E['xi'][E['xi']>600]]),
                    np.concatenate([O['mix'].real,E['mix'].real[E['xi']>600]]))
    mi=np.interp(xi,np.concatenate([O['xi'],E['xi'][E['xi']>600]]),
                    np.concatenate([O['mix'].imag,E['mix'].imag[E['xi']>600]]))
    return lead+2*np.real(g2*(mr+1j*mi))-2*q
ds={J:dfull(J) for J in (7,8)}
def Wof(kind,k=None):
    return ((1-np.cos(a*xi))*tests.hhat2(xi,'bump')/1.6434228127646e8) if kind=='bump' else tests.Wpoly(xi,k)
def integ(W,f,hi=None):
    m=np.ones(xi.size,bool) if hi is None else xi<=hi
    return 2*np.trapz((W*f)[m],xi[m])
print()
for name,W,cut in [("frozen h (C^inf bump)",Wof('bump'),600),
                   ("h_2 = (d^2-1/4)(1-(x/d0)^2)^2",Wof('poly',2),150),
                   ("h_4 = (d^2-1/4)(1-(x/d0)^2)^4",Wof('poly',4),150)]:
    mass=2*np.trapz(W,xi); defc=2*np.pi-mass
    print(f"--- {name} ---")
    print(f"  2*int_0^3000 W = {mass:.6f}  deficit vs 2pi = {defc:.6f} ({100*defc/(2*np.pi):.4f}%)")
    for J in (7,8): print(f"  J={J}: m = {-integ(W,ds[J]):+.6f}  (|xi|<=600 part {-integ(W,ds[J],600):+.6f})")
    print(f"  spread J8-J7 = {-integ(W,ds[8])+integ(W,ds[7]):+.6f}")
    print(f"  FLOOR -int W 2Re(g2 t2) (full range) = {-integ(W,lead):+.6f}")
    mm=-integ(W,ds[8])
    sup=np.abs(ds[8][xi>2500]).max()
    print(f"  tail bound beyond 3000: |{defc:.4f} * sup|d_2|| <= {defc*sup:.2e}  (sup|d_2| on [2500,3000] = {sup:.3e})")
    print(f"  W-mass below xi={cut}: {np.trapz(W[xi<=cut],xi[xi<=cut])/np.trapz(W,xi):.5f};  below 16: {np.trapz(W[xi<=16],xi[xi<=16])/np.trapz(W,xi):.5f}")
    print(f"  m - delta_M(={DM}) = {mm-DM:+.6f}  ->  {'m > delta_M' if mm>DM else 'm < delta_M'}\n")
