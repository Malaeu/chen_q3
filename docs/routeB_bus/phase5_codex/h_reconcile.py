import mpmath as mp
mp.mp.dps=20
a=mp.log(2); d0=(mp.log(3)-mp.log(2))/8
Z=mp.quad(lambda s: mp.exp(-1/(1-s*s)),[-1,1])
def eta(x):
    s=x/d0
    return mp.exp(-1/(1-s*s))/(Z*d0) if abs(s)<1 else mp.mpf(0)
def h(x):  # (d^2 - 1/4) eta_d0
    if abs(x)>=d0: return mp.mpf(0)
    return mp.diff(eta,x,2)-eta(x)/4
H=mp.quad(lambda x: h(x)**2,[-d0,0,d0])
Ap=mp.quad(lambda x: h(x)*mp.exp(x/2),[-d0,0,d0]); Am=mp.quad(lambda x: h(x)*mp.exp(-x/2),[-d0,0,d0])
print("H=||h||^2 =",mp.nstr(H,12)," A+(h)=",mp.nstr(Ap,3)," A-(h)=",mp.nstr(Am,3),flush=True)
# J_a(h) by (5): (1/H) sum_j e^{-(2j+1/2)a} |int h e^{(2j+1/2)x}|^2
J=sum(mp.exp(-(2*j+mp.mpf(1)/2)*a)*mp.quad(lambda x: h(x)*mp.exp((2*j+mp.mpf(1)/2)*x),[-d0,0,d0])**2 for j in range(0,6))/H
print("J_a(h) =",mp.nstr(J,10),flush=True)
# D(h)/H via direct t-integration: D = int_0^inf a(t) ||h(.+t)-h||^2 dt ; ||h(.+t)-h||^2 = 2H - 2C_h(t)
def Ch(t):
    if t>=2*d0: return mp.mpf(0)
    return mp.quad(lambda x: h(x)*h(x+t),[-d0,-d0+ (2*d0-t) if False else 0,d0-t]) if t<2*d0 else mp.mpf(0)
def Ch2(t):
    lo=-d0; hi=d0-t
    if hi<=lo: return mp.mpf(0)
    return mp.quad(lambda x: h(x)*h(x+t),[lo,(lo+hi)/2,hi])
aw=lambda t: mp.exp(-t/2)/(1-mp.exp(-2*t))
D_h=mp.quad(lambda t: aw(t)*(2*H-2*Ch2(t)),[0,d0,2*d0]) + mp.quad(lambda t: aw(t)*2*H,[2*d0,mp.inf])
print("D(h)/H =",mp.nstr(D_h/H,10),"  D(h)/H - c_A =",mp.nstr(D_h/H-(mp.euler+mp.log(8*mp.pi)+mp.pi/2),10),flush=True)
w=a/mp.sqrt(2)
for th,name in ((0,'v+'),(mp.pi,'v-'),(mp.pi/2,'vi')):
    c=mp.cos(th)
    Dv=D_h/H-J*c
    L2=Dv-(mp.euler+mp.log(8*mp.pi)+mp.pi/2)-2*w*c/2
    print(f"{name}: D(v)={mp.nstr(Dv,10)}  C_v(a)={mp.nstr(c/2,4)}  L_2(v)=D-c_A-2w C_v = {mp.nstr(L2,10)}",flush=True)
