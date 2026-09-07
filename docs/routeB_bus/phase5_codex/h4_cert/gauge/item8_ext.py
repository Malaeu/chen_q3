# BONUS/DIAGNOSTIC (never a proof): the object in (20),  p(xi) + FT(chi R)(xi)
import numpy as np
from scipy.special import sici
a=np.log(2.0); d0=a/4; delta=(np.log(3)-np.log(2))/8; c=np.cosh(a/2)-1.0
JM=70
def Lv(z):
    z=np.asarray(z,float); out=np.ones_like(z); nz=z!=0
    s,_=sici(z[nz]); out[nz]=s/z[nz]; return out
ms=np.arange(-1,JM+1); cs=np.where(ms==-1,-0.5,0.5)
two_k_cache={}
def K_ell(t):
    tot=0.0; et=np.exp(t); em=np.exp(-t)
    for jj,mj in enumerate(ms):
        b=2*np.pi*2.0**float(mj); k=(ms-mj).astype(float); tk=np.exp2(k)
        tot+= cs[jj]*np.sum(cs*( np.exp(t/2)*(Lv(b*(tk-et))+Lv(b*(tk+et)))
                                +np.exp(-t/2)*(Lv(b*(tk-em))+Lv(b*(tk+em))) ))
    return tot/np.pi
def K_T(t): return -2*np.pi*(K_ell(t)-0.5*K_ell(t+a)-0.5*K_ell(t-a))
def Sfun(t):
    j=np.arange(0,JM+1); return np.sum(Lv(2*np.pi*2.0**j*abs(t)))
def R(t): return K_T(t)-c*Sfun(t)
def chi(t):
    x=(np.abs(t)-2*delta)/(d0-2*delta)
    x=np.clip(x,0,1); return 1-(10*x**3-15*x**4+6*x**5)
# graded grid on (0,d0]
g=np.concatenate([np.geomspace(1e-9,1e-3,400),np.linspace(1e-3,d0,4000)[1:]])
Rv=np.array([R(t) for t in g]); Cv=chi(g); f=Cv*Rv
print("R(t) on (0,d0]: min %.6f max %.6f ;  ||chi R||_1 (full line) = %.6f"%(Rv.min(),Rv.max(),2*np.trapezoid(np.abs(f),g)))
def FTchiR(xi):
    return 2*np.trapezoid(f*np.cos(xi*g),g)     # even
def p(T,JMp=200):
    j=np.arange(0,JMp); b=2*np.pi*2.0**j; m=b>abs(T)
    return c*np.pi*np.sum(np.log(b[m]/abs(T))/b[m]) if abs(T)>0 else np.inf
xis=np.concatenate([np.linspace(0.05,5,60),np.linspace(5,200,400),np.geomspace(200,5000,200)])
vals=np.array([p(x)+FTchiR(x) for x in xis])
pv=np.array([p(x) for x in xis]); fv=vals-pv
i=np.argmin(vals)
print("min of p+FT(chi R) over xi in [0.05,5000]: %.6e at xi=%.3f   (p=%.6e, FT=%.6e)"%(vals[i],xis[i],pv[i],fv[i]))
neg=xis[vals<0]
print("negative set:", "EMPTY" if neg.size==0 else f"{neg.min():.3f} .. {neg.max():.3f}  ({neg.size} of {xis.size} grid pts)")
for x in [1,2,3,5,8,12,20,30,50,100,200,500,1000]:
    print(f"  xi={x:6.0f}: p={p(x):+.6e}  FT(chiR)={FTchiR(x):+.6e}  sum={p(x)+FTchiR(x):+.6e}")
