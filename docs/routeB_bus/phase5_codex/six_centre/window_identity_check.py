"""Direct check of the reformulation  lambda_a = min_w Q[v_out + w] / ||v_in - w||^2  (WINDOW_TAIL_DERIVATIVE_PROBE 2026-09-09, reading 2).
Three contiguous blocks (centres -2a, 0, 2a; half-width a) so that Phi's tail lives in the basis (Phi(3a) negligible for a >= 0.5).
Left side uses the tail blocks; right side uses block 0 only: different inputs. Also checks Q(Phi, .) = 0 on the Legendre closure.
DIAGNOSTIC_NEVER_A_PROOF."""
import sys, json, time, numpy as np, scipy.linalg as sla
from numpy.polynomial import legendre as Lg
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre')
from sc_build import build
def Phi(x, N=8):
    x=np.abs(np.asarray(x,float)); s=np.zeros_like(x)
    for n in range(1,N+1): s+=(2*np.pi**2*n**4*np.exp(4.5*x)-3*np.pi*n**2*np.exp(2.5*x))*np.exp(-np.pi*n**2*np.exp(2*x))
    return s
def coeffs(center,a,K):
    x,w=np.polynomial.legendre.leggauss(K+40); f=Phi(center+a*x)
    return np.array([(2*k+1)/2*np.sum(w*f*Lg.legval(x,np.eye(K)[k])) for k in range(K)])
out={}
for a in [float(v) for v in sys.argv[1].split(',')]:
    K=int(sys.argv[2]); t0=time.time()
    xs=[-2*a,0.0,2*a]; R=build(xs,K,delta=a,verbose=False); Q,G=R['Q'],R['G']; N=3*K
    v=np.concatenate([coeffs(c,a,K) for c in xs]); vin=np.zeros(N); vin[K:2*K]=v[K:2*K]; vout=v-vin
    ev,V=sla.eigh(Q[K:2*K,K:2*K],G[K:2*K,K:2*K]); lam=ev[0]; f=np.zeros(N); f[K:2*K]=V[:,0]
    # scale f to the cut-Phi normalisation is unnecessary: identity is homogeneous in f once w = vin - f
    w=vin-f
    lhs=float((vout+w)@Q@(vout+w)); rhs=float(lam*((vin-w)@G@(vin-w))); rhs2=float(f@Q@f)
    QPhi=float(v@Q@v); nPhi=float(v@G@v)
    cross=Q[K:2*K,:]@v; crossn=float(np.max(np.abs(cross))); Qnorm=float(np.max(np.abs(Q[K:2*K,K:2*K])))
    out[f'{a:.2f}']=dict(a=a,K=K,lambda_a=float(lam),lhs_Q_vout_plus_w=lhs,rhs_lambda_norm=rhs,rhs_Qf=rhs2,rel_err=abs(lhs-rhs)/abs(rhs),
        Q_Phi_over_norm=QPhi/nPhi,max_cross_Q_Phi_w=crossn,Q_block_scale=Qnorm,Q_vout=float(vout@Q@vout),tail_mass_rel=float((vout@G@vout)/nPhi),secs=time.time()-t0)
    print(f"a={a} K={K} lam={lam:.4e} | Q[vout+w]={lhs:.4e} lam*||vin-w||^2={rhs:.4e} (Q[f]={rhs2:.4e}) rel.err={abs(lhs-rhs)/abs(rhs):.2e} | Q[Phi]/||Phi||^2={QPhi/nPhi:.2e} max|Q(Phi,e_j)|={crossn:.2e} (Q scale {Qnorm:.2e}) | Q[vout]/||Phi||^2={vout@Q@vout/nPhi:.3e} T={(vout@G@vout)/nPhi:.3e} {time.time()-t0:.0f}s",flush=True)
json.dump(out,open(f'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/six_centre/out/window_identity_K{K}.json','w'),indent=1)
