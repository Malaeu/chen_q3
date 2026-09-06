import sys, numpy as np, mpmath as mp, time
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/semitab_B')
from ops import SemiLocal
a=np.log(2.0); d0=(np.log(3)-np.log(2))/8; cA=float(mp.euler+mp.log(8*mp.pi)+mp.pi/2)
def q_inf(xi): return float(mp.re(mp.digamma(mp.mpf(1)/4+1j*mp.mpf(xi)/2))-mp.log(mp.pi))   # = 2∫a(t)(1-cos ξt)dt - c_A
# h = (d^2 - 1/4) eta_{d0}, eta normalized to integral 1; hhat(xi) = (-(xi^2) - 1/4) etahat(xi)
xs=np.linspace(-d0,d0,20001); s=xs/d0
eta=np.where(np.abs(s)<1,np.exp(-1/np.maximum(1-s*s,1e-300)),0.0); Z=np.trapz(eta,xs); eta/=Z
def hhat(xi): return (-(xi**2)-0.25)*np.trapz(eta*np.exp(-1j*xi*xs),xs)
H=None
def build_S(sl,pr):
    n=sl.M.n; P=np.zeros((n,n)); P[pr['idxP'],pr['idxP']]=1.0; Q=pr['W']@pr['W'].T
    al,XI,ZETA,s=pr['alpha'],pr['XI'],pr['ZETA'],pr['s']
    D=(XI*(al**2))@XI.T+(XI*(al*s))@ZETA.T+(ZETA*(al*s))@XI.T-(ZETA*(al**2))@ZETA.T
    return np.eye(n)-P-Q+D
xis=np.concatenate([np.linspace(0,40,161),np.linspace(41,120,80),np.linspace(125,300,36)])
for N in (2048,4096):
    t0=time.time()
    out={}
    for tag,sem in (('arch',False),('semi',True)):
        sl=SemiLocal(N,semilocal=sem,verbose=False); pr=sl.pair(1.0,tol=1e-8); S=build_S(sl,pr)
        M=sl.M; u=M.u; w=M.w
        ks=[]
        for xi in xis:
            c=np.zeros(M.n,dtype=complex); c[1:]=np.sqrt(w[1:])*u[1:]**(-0.5+1j*xi)/np.sqrt(2*np.pi)
            ks.append(float(np.real(np.vdot(c,S@c))))
        out[tag]=np.array(ks); del sl,S
    q=np.array([q_inf(x) for x in xis])/(2*np.pi)
    print(f"\n=== N={N}  (U_max={np.sqrt(N/2):.1f}, log-range width {np.log(np.sqrt(N/2))-np.log(1/np.sqrt(2*N)):.2f})  time {time.time()-t0:.0f}s")
    print("  xi    q_inf/2pi    k_arch     k_semi    q/2pi-k_semi")
    for i in range(0,len(xis),8):
        print(f"{xis[i]:6.1f} {q[i]:+9.4f} {out['arch'][i]:9.4f} {out['semi'][i]:9.4f} {q[i]-out['semi'][i]:+9.4f}")
    # sign map: where q/2pi - k_semi < 0
    neg=xis[(q-out['semi'])<0]
    print("  q/2pi - k_semi < 0 on xi in:", (f"[{neg.min():.1f}, {neg.max():.1f}] ({len(neg)} grid pts)" if len(neg) else "nowhere"))
    # (12) check with h=(d^2-1/4)eta_{d0}: L2(v-) via q, n2(v-) via k, m = L2 - n2 ; also compare L2 with 3.927236
    hh=np.array([abs(hhat(x))**2 for x in xis]); Hn=np.trapz(hh,xis)/(2*np.pi)   # Parseval: ∫|ĥ|²dξ = 2π H  (ξ≥0 half → factor 2)
    Hn*=2
    wgt=(1-np.cos(a*xis))*hh
    L2=np.log(2)/np.sqrt(2)+ 2*np.trapz(wgt*q,xis)/Hn*(1)   # both half-lines: factor 2; note (1/2π) already in q
    n2=2*np.trapz(wgt*out['semi'],xis)/Hn
    print(f"  h=(d^2-1/4)eta: H(from |hhat|^2)={Hn:.4e}  L2(v-) via q_inf = {L2:.6f} (mpmath exact 3.927236)   n2(v-) via k_semi = {n2:.6f} (B diag 3.5877)   m = L2-n2 = {L2-n2:+.4f} (B diag +0.340)")
    sys.stdout.flush()
