import sys; sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import numpy as np, dens
a=np.log(2.0); r=2**-0.5; H=1.6434228127646e8
C=np.load('/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/density_fine_N4096.npy')
T=np.load('t_tables.npz'); xi=T['xi']; Di=np.load('d_inf.npz')
g2=dens.gamma_S(xi,(2,)); q2=dens.q_S(xi,(2,))
O={J:np.load(f'op_two_J{J}.npz') for J in (6,7,8)}
d={J:2*np.real(g2*(T['t_2']+O[J]['mix']))-2*O[J]['quad'] for J in O}
lead=2*np.real(g2*T['t_2'])
W=(1-np.cos(a*xi))*C[4]/H; I=lambda f: 2*np.trapz(W*f,xi)
print("=== A: d tables ===")
print("  xi      d_inf(xi)        d_2(xi) J=8      d_2 J=7        d_2 J=6      2Re(g2 t_2)")
for x in [0,0.5,1,2,5,10,16,20,30,40,60,80,120,200,400,600]:
    i=int(round(x/0.25))
    print(f"{x:7.1f} {Di['d'][i]:+.8e} {d[8][i]:+.8e} {d[7][i]:+.6e} {d[6][i]:+.6e} {lead[i]:+.6e}")
print("\n=== B: m(h) ===")
for J in (6,7,8): print(f"  J={J}: m = {-I(d[J]):+.6f}")
seq=[-I(d[J]) for J in (6,7,8)]; inc=np.diff(seq); rat=inc[1]/inc[0]
print(f"  increments {inc[0]:+.5f} {inc[1]:+.5f} ratio {rat:.3f} -> geometric limit {seq[-1]+inc[1]*rat/(1-rat):+.6f}")
print(f"  lower bound from the exact scalar alone (-int W 2Re(g2 t_2)) = {-I(lead):+.6f}")
print(f"  A(h) = -int W d_inf = {-I(Di['d']):+.6f}   w = {a/np.sqrt(2):+.6f}   B(h)(J=8) = {a/np.sqrt(2)+I(d[8]-Di['d']):+.6f}")
print(f"  carrier reproduction: A={I(C[1]-C[2]):+.6f} B={I(C[3]-C[2]):+.6f} m={a/np.sqrt(2)+I(C[1]-C[2])-I(C[3]-C[2]):+.6f}")
print("\n=== C: cumulative convergence of m (J=8) and of the leading part ===")
cum=lambda y: -2*np.concatenate([[0],np.cumsum((W[1:]*y[1:]+W[:-1]*y[:-1])/2*np.diff(xi))])
c8=cum(d[8]); cl=cum(lead)
for X in [100,200,300,400,500,550,600]:
    i=int(X/0.25); print(f"   X={X:4d}  m(<=X)={c8[i]:+.6f}   lead-only={cl[i]:+.6f}")
print("   last four 50-blocks of m:", np.round(np.diff([c8[int(X/0.25)] for X in [400,450,500,550,600]]),6))
print("   last four 50-blocks of lead:", np.round(np.diff([cl[int(X/0.25)] for X in [400,450,500,550,600]]),6))
print(f"   missing phase mass beyond 600 (Lemma 5): {2*np.pi-2*np.trapz(W,xi):.6f}")
print(f"   sup|d_2| on [500,600] = {np.abs(d[8][xi>=500]).max():.4e}; crude tail bound +-{(2*np.pi-2*np.trapz(W,xi))*np.abs(d[8][xi>=500]).max():.4f}")
print("\n=== D: sign / shape of d_2 ===")
for lo,hi in [(16,120),(120,300),(300,600),(16,600)]:
    m=(xi>=lo)&(xi<=hi); print(f"   [{lo},{hi}]: fraction d_2<0 = {(d[8][m]<0).mean():.3f}, mean={d[8][m].mean():+.5f}, max={d[8][m].max():+.5f}, min={d[8][m].min():+.5f}")
k2=q2/(2*np.pi)+d[8]
print(f"   k_2 min = {k2.min():+.6f} at xi={xi[k2.argmin()]}; k_2(J=7) min={(q2/(2*np.pi)+d[7]).min():+.6f}; (J=6) {(q2/(2*np.pi)+d[6]).min():+.6f}")
