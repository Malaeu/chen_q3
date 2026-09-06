"""Validations (iv) Theorem 4 exponent for d_2 and (v) first cosine coefficient of k_2-k_inf."""
import sys; sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import numpy as np
a=np.log(2.0); r=2**-0.5
D=np.load('d_two.npz'); xi=D['xi']
key='d_J8' if 'd_J8' in D else ('d_J7' if 'd_J7' in D else 'd_J6')
d2=D[key]; dinf=D['dinf']
print("using", key)
def slope(y,lo,hi,win=40):
    m=(xi>=lo)&(xi<=hi); e=np.abs(y[m])
    run=np.array([e[max(0,i-win):i+win].max() for i in range(e.size)])
    return np.polyfit(np.log(xi[m]),np.log(np.maximum(e,1e-18)),1)[0], np.polyfit(np.log(xi[m]),np.log(run),1)[0]
for lo,hi in [(60,600),(100,600),(200,600)]:
    s1,s2=slope(d2,lo,hi); print(f"  d_2 log-log slope on [{lo},{hi}]: raw={s1:+.4f} envelope={s2:+.4f}   (Thm 4: -1/2)")
    s1,s2=slope(d2-dinf,lo,hi); print(f"  d_2-d_inf                    : raw={s1:+.4f} envelope={s2:+.4f}")
# (v) first cosine coefficient of k_2 - k_inf over complete periods 2pi/a
k2mk = (D['q2']-D['qinf'])/(2*np.pi) + (d2-dinf)
P=2*np.pi/a
print(f"\n  period 2pi/a = {P:.6f};  target -a r/pi = {-a*r/np.pi:.6f}")
print("  X      #periods   c1(cos)      c1(sin)")
for X in [50,100,200,300,400,500,600]:
    n=int(X/P); lo=0.0; hi=n*P
    m=(xi>=lo)&(xi<=hi)
    x=xi[m]; y=k2mk[m]
    c1=2*np.trapz(y*np.cos(a*x),x)/(hi-lo)
    s1=2*np.trapz(y*np.sin(a*x),x)/(hi-lo)
    print(f"  {hi:7.2f}  {n:5d}   {c1:+.6f}   {s1:+.6f}")
# same for a window starting at 100 (drop the low-xi transient)
print("  windows [X0, X0+n*P]:")
for X0 in [50,100,200]:
    for X1 in [300,600]:
        n=int((X1-X0)/P); hi=X0+n*P
        m=(xi>=X0)&(xi<=hi); x=xi[m]; y=k2mk[m]
        c1=2*np.trapz(y*np.cos(a*x),x)/(hi-X0); s1=2*np.trapz(y*np.sin(a*x),x)/(hi-X0)
        print(f"  [{X0},{hi:.2f}] n={n:3d}  c1={c1:+.6f}  s1={s1:+.6f}")
