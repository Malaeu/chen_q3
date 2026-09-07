# DIAGNOSTIC: pole-gauge freedom. On H00 the difference kernels e^{±(x-y)/2} = e^{±x/2} e^{∓y/2} are rank-one in the pole
# directions, hence invisible. So K_T may be replaced by K_T + 2*alpha*cosh(t/2) (R even) without changing the compressed form.
import numpy as np
exec(open('item8_ext.py').read().split("# graded grid")[0])   # reuse Lv, K_ell, K_T, Sfun, R, chi, constants
g=np.concatenate([np.geomspace(1e-9,1e-3,300),np.linspace(1e-3,d0,2500)[1:]])
Rv=np.array([R(t) for t in g]); Cv=chi(g)
print("R on (0,d0]: min %.5f max %.5f  R(2delta)=%.5f  R(1e-6)=%.5f"%(Rv.min(),Rv.max(),np.interp(2*delta,g,Rv),Rv[0]))
def p(T,JMp=200):
    j=np.arange(0,JMp); b=2*np.pi*2.0**j; m=b>abs(T)
    return c*np.pi*np.sum(np.log(b[m]/abs(T))/b[m])
xis=np.concatenate([np.linspace(0.05,5,60),np.linspace(5,200,400),np.geomspace(200,5000,150)])
def scan(alpha,label):
    f=Cv*(Rv+2*alpha*np.cosh(g/2))
    FT=lambda xi: 2*np.trapezoid(f*np.cos(xi*g),g)
    vals=np.array([p(x)+FT(x) for x in xis]); i=np.argmin(vals); neg=xis[vals<0]
    print(f"{label}: alpha={alpha:+.5f}  ||chi R_g||_1={2*np.trapezoid(np.abs(f),g):.5f}  min(p+FT)={vals[i]:+.4e} at xi={xis[i]:.2f}  negative set: "+("EMPTY" if neg.size==0 else f"{neg.min():.2f}..{neg.max():.2f} ({neg.size} pts)"))
    return vals
scan(0.0,"no gauge     ")
# least-squares alpha on the window |t|<=2delta (where chi=1): minimize int (R + 2 alpha cosh)^2
w=g<=2*delta; ch=2*np.cosh(g[w]/2); alpha_ls=-np.sum(Rv[w]*ch)/np.sum(ch*ch)
scan(alpha_ls,"LS on window ")
# alpha making the mean over the whole chi-window zero
alpha_m=-np.trapezoid(Cv*Rv,g)/np.trapezoid(Cv*2*np.cosh(g/2),g)
scan(alpha_m,"mean-zero chi")
for al in np.linspace(alpha_ls-0.05,alpha_ls+0.05,5): scan(al,"sweep        ")
