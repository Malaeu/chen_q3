import numpy as np, importlib.util, os
_sp=importlib.util.spec_from_file_location('ww',os.path.join(os.path.dirname(os.path.abspath(__file__)),'weil_window_judge_2026-11-06.py'))
ww=importlib.util.module_from_spec(_sp); _sp.loader.exec_module(ww)
ww.K=20
ts=np.linspace(0,60,6001)
def vhat(c,a):
    u,w=np.polynomial.legendre.leggauss(600); y=a*u; w=a*w
    v=c@ww.basis(y,a); return np.abs(np.exp(1j*np.outer(ts,y))@(w*v))
rows=[]; s1=s2=True; s3n=s3d=0
print(" m    | dir | eig W_inf | gamma* | cos(g*log2) cos(g*log3) | P2      P3      | sgn match")
for m in [3.5,4,5,6,8,10,13]:
    a,G,A,P,Vp,Vm,nodes=ww.forms(m)
    C=np.vstack([Vp,Vm]); _,_,Vt=np.linalg.svd(C); Q=Vt[2:].T
    Gk,Ak=(Q.T@X@Q for X in (G,A)); Li=np.linalg.inv(np.linalg.cholesky(Gk))
    ev,U=np.linalg.eigh(Li@Ak@Li.T)
    F2=ww.F_at(np.log(2),a); F3=ww.F_at(np.log(3),a)
    P2m=np.log(2)/np.sqrt(2)*(F2+F2.T); P3m=np.log(3)/np.sqrt(3)*(F3+F3.T)
    for i in np.where(ev<0)[0]:
        c=Q@(Li.T@U[:,i]); p2=c@P2m@c; p3=c@P3m@c
        h=vhat(c,a); g=ts[np.argmax(h)]
        c2,c3=np.cos(g*np.log(2)),np.cos(g*np.log(3))
        mt=[np.sign(p2)==np.sign(c2), np.sign(p3)==np.sign(c3)]; s3n+=sum(mt); s3d+=2
        if i==0:
            s1 &= p2<0; s2 &= np.sign(p2)!=np.sign(p3)
        print(f"{m:5.1f} | {i:3d} | {ev[i]:+.3f} | {g:6.2f} | {c2:+.2f} {c3:+.2f} | {p2:+.4f} {p3:+.4f} | {mt}")
print(f"S1(p2<0 on most neg, all m)={s1}  S2(opposite signs on most neg, all m)={s2}  S3 match={s3n}/{s3d}={s3n/s3d:.0%}")
