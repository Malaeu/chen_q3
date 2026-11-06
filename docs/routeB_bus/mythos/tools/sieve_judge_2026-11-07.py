import numpy as np, importlib.util, os
_sp=importlib.util.spec_from_file_location('ww',os.path.join(os.path.dirname(os.path.abspath(__file__)),'weil_window_judge_2026-11-06.py'))
ww=importlib.util.module_from_spec(_sp); _sp.loader.exec_module(ww)
from numpy.polynomial.legendre import leggauss
ww.K=20
s4=s5=True
print(" m  | W_inf  | Prime   | M=dens.model | Prime-M (fluct) | Pole | f>0 nodes / f<0 nodes")
for m in [4,5,6,8,10,13]:
    a,G,A,P,Vp,Vm,nodes=ww.forms(m)
    C=np.vstack([Vp,Vm]); _,_,Vt=np.linalg.svd(C); Q=Vt[2:].T
    Gk,Ak=(Q.T@X@Q for X in (G,A)); Li=np.linalg.inv(np.linalg.cholesky(Gk))
    ev,U=np.linalg.eigh(Li@Ak@Li.T); c=Q@(Li.T@U[:,0])
    # f(x)=sum_jk c_j c_k f_jk(x); density model M = int f(x) e^{|x|/2} dx over [-2a,2a]
    xs,wx=leggauss(300); xs=a*(xs+1); wx=a*wx     # x in (0,2a)
    fx=np.array([c@ww.F_at(x,a)@c for x in xs])  # f(x); f(-x)=f(x) for real quadratic (symmetric)
    M=2*np.sum(wx*fx*np.exp(xs/2))
    pr=c@P@c; wi=c@A@c; pole=2*(c@Vp)*(c@Vm)
    sg=[ (n, np.sign(c@ww.F_at(np.log(n),a)@c)) for n in nodes]
    pos=[n for n,s in sg if s>0]; neg=[n for n,s in sg if s<0]
    s4 &= abs(M)<=0.3*abs(pr); s5 &= np.sign(pr-M)==np.sign(pr)
    print(f"{m:3d} | {wi:+.3f} | {pr:+.4f} | {M:+.4f}      | {pr-M:+.4f}         | {pole:+.0e} | {pos} / {neg}")
print("S4:",s4," S5:",s5)
