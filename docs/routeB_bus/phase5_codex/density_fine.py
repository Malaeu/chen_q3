import sys, numpy as np, mpmath as mp, time
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/semitab_B')
from ops import SemiLocal
a=np.log(2.0); d0=(np.log(3)-np.log(2))/8
def q_inf(xi): return float(mp.re(mp.digamma(mp.mpf(1)/4+1j*mp.mpf(xi)/2))-mp.log(mp.pi))
xs=np.linspace(-d0,d0,40001); s=xs/d0
eta=np.where(np.abs(s)<1,np.exp(-1/np.maximum(1-s*s,1e-300)),0.0); Z=np.trapz(eta,xs); eta/=Z
xis=np.arange(0,600.001,0.25)
etah=np.array([np.trapz(eta*np.exp(-1j*x*xs),xs) for x in xis]); hh=np.abs((-(xis**2)-0.25)*etah)**2
H_exact=1.6434228127646e8
Hn=2*np.trapz(hh,xis)/(2*np.pi)
print(f"Parseval: H from |hhat|^2 grid = {Hn:.6e}  vs exact 1.643423e8  (ratio {Hn/H_exact:.5f})",flush=True)
q=np.array([q_inf(x) for x in xis])/(2*np.pi)
wgt=(1-np.cos(a*xis))*hh
w=np.log(2)/np.sqrt(2)
L2=w+2*np.trapz(wgt*q,xis)/H_exact
print(f"L2(v-) = w + (1/2piH)∫(1-cos a xi)|hhat|^2 q  = {L2:.6f}   (mpmath exact 3.927236)",flush=True)
def build_S(sl,pr):
    n=sl.M.n; P=np.zeros((n,n)); P[pr['idxP'],pr['idxP']]=1.0; Q=pr['W']@pr['W'].T
    al,XI,ZETA,s=pr['alpha'],pr['XI'],pr['ZETA'],pr['s']
    D=(XI*(al**2))@XI.T+(XI*(al*s))@ZETA.T+(ZETA*(al*s))@XI.T-(ZETA*(al**2))@ZETA.T
    return np.eye(n)-P-Q+D
for N in (4096,):
    t0=time.time(); res={}
    for tag,sem in (('arch',False),('semi',True)):
        sl=SemiLocal(N,semilocal=sem,verbose=False); pr=sl.pair(1.0,tol=1e-8); S=build_S(sl,pr); M=sl.M
        C=np.zeros((M.n,len(xis)),dtype=complex)
        C[1:,:]=np.sqrt(M.w[1:])[:,None]*np.exp((-0.5+1j*xis[None,:])*np.log(M.u[1:])[:,None])/np.sqrt(2*np.pi)
        SC=S@C; res[tag]=np.real(np.sum(np.conj(C)*SC,axis=0)); del sl,S,C,SC
    n2=2*np.trapz(wgt*res['semi'],xis)/H_exact; ninf=2*np.trapz(wgt*res['arch'],xis)/H_exact
    print(f"N={N} ({time.time()-t0:.0f}s): n2(v-) via k_semi = {n2:.6f} (B diag 3.5877)  n_inf(v-) via k_arch = {ninf:.6f}   m(h) = L2 - n2 = {L2-n2:+.4f} (B diag +0.340)")
    # resonance structure: local maxima of k_semi vs odd multiples of pi/a
    ks=res['semi']; pk=[xis[i] for i in range(1,len(xis)-1) if ks[i]>ks[i-1] and ks[i]>ks[i+1] and ks[i]>0.05 and xis[i]<80]
    print("  local maxima of k_semi (xi<80):",np.round(pk,2))
    print("  odd multiples of pi/log2:",np.round([(2*k+1)*np.pi/a for k in range(9)],2))
    print("  zeros of (1-cos a xi) at 2pi k/log2:",np.round([2*np.pi*k/a for k in range(1,9)],2))
    # integrand sign contributions
    dq=q-ks; pos=2*np.trapz(np.where(dq>0,wgt*dq,0),xis)/H_exact; neg=2*np.trapz(np.where(dq<0,wgt*dq,0),xis)/H_exact
    print(f"  split of the (12) integral: positive part {pos:+.4f}, negative part {neg:+.4f}, w = {w:.4f}")
    np.save('/home/chirurgie/.claude/jobs/4b35770d/tmp/density_fine_N4096.npy',np.vstack([xis,q,res['arch'],res['semi'],hh]))
