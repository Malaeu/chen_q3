"""Six-centre full-width assembly of the Weil form (C1) on Legendre profiles.

Class: v = sum_i U_{x_i} h_i, h_i supported on (-delta, delta) (full width ell = 2 delta,
delta = (log3 - log2)/8), h_i = polynomials of degree < K (Legendre basis P_k(x/delta)),
both TOTAL pole moments imposed (M_+ = M_- = 0  <=>  M_c = M_s = 0).

Archimedean part by the Fourier symbol (independent of the spatial three_lobe build):
  D(f) - c_A ||f||^2 = (1/2pi) int |f^|^2 Omega,  Omega(xi) = Re psi(1/4 + i xi/2) - log pi,
  f^ of P_k(x/delta) on |x|<delta  = 2 delta (-i)^k j_k(xi delta)   (spherical Bessel).
Prime part EXACT (polynomial overlaps).  Pole part by quadrature of P_k * cosh/sinh.

Outputs per centre set:  class floor (generalised eigenvalues of Q vs the physical Gram
on the constraint kernel), the mean sector (degree-0 profiles: kernel of the 2 x m moment
matrix), its most adverse PRIME direction with Arch/Prime/Pole on it, and the scalar
compensation test (35): lambda_min(B+ , G) vs lambda_max(-A- , G) with
  B+ = D + 2|M_c|^2 ,  A- = -c_A||.||^2 - primes - 2|M_s|^2   (INVARIANT (34)).
DIAGNOSTIC_NEVER_A_PROOF.  Convergence gauge: rerun with --h 0.01 --XI 40000.
"""
import sys, json, time, argparse, math
import numpy as np
from scipy.special import spherical_jn, digamma
from scipy.integrate import quad
from numpy.polynomial import legendre as Lg, polynomial as Pn
import scipy.linalg as sla

PR = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]
def Lam(n):
    for p in PR:
        m,e=n,0
        while m%p==0: m//=p; e+=1
        if e and m==1: return np.log(p)
    return 0.0

def overlap(k,l,sig,delta):
    """int P_k(y/delta) P_l((y-sig)/delta) dy over the support overlap (exact: Gauss-Legendre with k+l+8 nodes, legval is stable)."""
    s=sig/delta
    if abs(s)>=2: return 0.0
    lo,hi=max(-1,-1+s),min(1,1+s)
    n=k+l+8
    x,w=np.polynomial.legendre.leggauss(n)
    u=0.5*(hi-lo)*x+0.5*(hi+lo); wu=0.5*(hi-lo)*w
    ck=np.zeros(k+1); ck[k]=1; cl=np.zeros(l+1); cl[l]=1
    return delta*np.sum(wu*Lg.legval(u,ck)*Lg.legval(u-s,cl))

def build(xs,K,h=0.02,XI=20000.0,verbose=True,no_offsets=False,delta=None):
    t0=time.time()
    a=np.log(2); b=np.log(3)
    if delta is None: delta=(b-a)/8
    ell=2*delta
    m=len(xs); N=m*K
    cA=np.euler_gamma+np.log(8*np.pi)+np.pi/2
    xi=np.arange(0,XI+h,h); xi[0]=1e-12
    Om=np.real(digamma(0.25+1j*xi/2))-np.log(np.pi)
    J=np.array([spherical_jn(k,xi*delta) for k in range(K)])
    w=np.ones(len(xi)); w[1:-1:2]=4; w[2:-1:2]=2; w*=h/3
    base={}
    for k in range(K):
        for l in range(k,K):
            base[(k,l)]=J[k]*J[l]*Om*w
    Arch=np.zeros((N,N))
    tail_c={}
    # Tail beyond XI of int j_k(xi d) j_l(xi d) Omega(xi) e^{i xi D}: j_k j_l ~ [cos((k-l)pi/2) - cos(2 xi d - (k+l)pi/2)]/(2 xi^2 d^2).
    # Non-oscillatory pieces survive only for D = 0 (first term) and |D| = 2 delta (second term beats against e^{i xi D});
    # the |D| = 2 delta case is the adjacent-block tail (~6e-5 at XI = 20000) that was uncorrected until 2026-09-09.
    tail_int=quad(lambda z: 1/(2*(z*delta)**2)*(np.real(digamma(0.25+1j*z/2))-np.log(np.pi)),XI,1e9,limit=200)[0]
    tail_adj={}
    for k in range(K):
        for l in range(K):
            c=np.cos((k-l)*np.pi/2)
            tail_c[(k,l)]=2*c*tail_int if abs(c)>1e-12 else 0.0
            phi=(k+l)*np.pi/2
            tail_adj[(k,l)]=(-0.5*np.cos(phi)*2*tail_int, -0.5*np.sin(phi)*2*tail_int)   # (re part for k+l even, im part x sgn(D) for k+l odd)
    for i in range(m):
        for j in range(m):
            D=xs[i]-xs[j]; cosD=np.cos(xi*D); sinD=np.sin(xi*D)
            for k in range(K):
                for l in range(K):
                    bs=base[(min(k,l),max(k,l))]; s=(-1)**(k+l)
                    re=np.sum(bs*cosD)*(1+s); im=np.sum(bs*sinD)*(1-s)
                    val=(2*delta**2/np.pi)*(1j**k)*((-1j)**l)*(re+1j*im)
                    if abs(D)<1e-14: val+=(2*delta**2/np.pi)*(1j**k)*((-1j)**l)*tail_c[(k,l)]
                    elif abs(abs(D)-2*delta)<1e-12:
                        tr,ti=tail_adj[(k,l)]
                        val+=(2*delta**2/np.pi)*(1j**k)*((-1j)**l)*(tr if s==1 else 1j*np.sign(D)*ti)
                    Arch[i*K+k,j*K+l]=np.real(val)
    Arch=(Arch+Arch.T)/2
    if verbose: print('  arch %.1fs'%(time.time()-t0),flush=True)
    G=np.zeros((N,N))
    for i in range(m):
        for j in range(m):
            sig=xs[j]-xs[i]
            if abs(sig)>=ell: continue
            for k in range(K):
                for l in range(K):
                    G[i*K+k,j*K+l]=overlap(k,l,sig,delta)
    # primes: Prime(f,g) = - sum_n w_n [<f,U_{log n} g> + <f,U_{-log n} g>]
    P=np.zeros((N,N)); atoms=[]
    nmax=int(np.exp(xs[-1]-xs[0]+ell))+2
    PRL=[p for p in range(2,nmax+2) if all(p%q for q in range(2,int(p**0.5)+1))]
    global PR; PR=PRL
    for n in range(2,nmax+1):
        lam=Lam(n)
        if lam==0: continue
        wn=lam/np.sqrt(n); ln=np.log(n); hits=[]
        for i in range(m):
            for j in range(m):
                for tau in (ln,-ln):
                    sig=xs[j]+tau-xs[i]
                    if abs(sig)>=ell: continue
                    if no_offsets and abs(sig)>1e-9: continue
                    hits.append((i,j,round(sig,6)))
                    for k in range(K):
                        for l in range(K):
                            P[i*K+k,j*K+l]-=wn*overlap(k,l,sig,delta)
        if hits: atoms.append((n,float(wn),hits))
    # poles
    Mc=np.zeros(N); Ms=np.zeros(N)
    for i in range(m):
        for k in range(K):
            c=np.zeros(k+1); c[k]=1
            Mc[i*K+k]=quad(lambda u: Lg.legval(u,c)*np.cosh((xs[i]+delta*u)/2)*delta,-1,1)[0]
            Ms[i*K+k]=quad(lambda u: Lg.legval(u,c)*np.sinh((xs[i]+delta*u)/2)*delta,-1,1)[0]
    Pole=2*np.outer(Mc,Mc)-2*np.outer(Ms,Ms)
    Q=Arch+P+Pole
    if verbose: print('  total %.1fs'%(time.time()-t0),flush=True)
    return dict(xs=xs,K=K,delta=delta,ell=ell,cA=cA,Arch=Arch,G=G,P=P,Mc=Mc,Ms=Ms,Pole=Pole,Q=Q,atoms=atoms)

def kernel(rows):
    U,S,Vt=np.linalg.svd(rows); r=int(np.sum(S>1e-12*S[0])); return Vt[r:].T

def analyse(R,label):
    Q,G,P,Arch,Pole,Mc,Ms,cA=R['Q'],R['G'],R['P'],R['Arch'],R['Pole'],R['Mc'],R['Ms'],R['cA']
    m=len(R['xs']); K=R['K']; N=m*K
    out={'label':label,'centres':[float(x) for x in R['xs']],'K':K,'dim':N}
    out['atoms']=[(n,wn,hits) for n,wn,hits in R['atoms']]
    ns=kernel(np.vstack([Mc,Ms]))
    ev=sla.eigh(ns.T@Q@ns,ns.T@G@ns,eigvals_only=True)
    out['class_floor']=float(ev[0]); out['class_spectrum_head']=[float(x) for x in ev[:6]]
    # unconstrained
    ev0=sla.eigh(Q,G,eigvals_only=True); out['unconstrained_min']=float(ev0[0])
    # mean sector: degree 0 only
    idx=[i*K for i in range(m)]
    Q0,G0,P0,A0,Po0=Q[np.ix_(idx,idx)],G[np.ix_(idx,idx)],P[np.ix_(idx,idx)],Arch[np.ix_(idx,idx)],Pole[np.ix_(idx,idx)]
    ns0=kernel(np.vstack([Mc[idx],Ms[idx]]))
    evm,vm=sla.eigh(ns0.T@Q0@ns0,ns0.T@G0@ns0)
    out['mean_sector_dim']=ns0.shape[1]; out['mean_sector_Q_floor']=float(evm[0])
    # most adverse PRIME direction on the mean kernel
    evp,vp=sla.eigh(ns0.T@P0@ns0,ns0.T@G0@ns0)
    z=ns0@vp[:,0]; nz=z@G0@z
    out['adverse_prime_dir']=[float(x) for x in z/np.sqrt(np.max(np.abs(z))**2)]
    out['adverse_prime_per_unit_norm']=float(z@P0@z/nz)
    out['on_adverse: Arch,Prime,Pole,Q per unit norm']=[float(z@M@z/nz) for M in (A0,P0,Po0,Q0)]
    out['on_adverse: D per unit norm']=float(z@A0@z/nz+cA)
    # compensation test (35) on the constraint kernel of the full class
    Dm=Arch+cA*G; Bp=Dm+2*np.outer(Mc,Mc); Am=-cA*G+P-2*np.outer(Ms,Ms)
    lb=sla.eigh(ns.T@Bp@ns,ns.T@G@ns,eigvals_only=True)[0]
    la=sla.eigh(ns.T@(-Am)@ns,ns.T@G@ns,eigvals_only=True)[-1]
    out['(35) lambda_min(B+)']=float(lb); out['(35) lambda_max(-A-)']=float(la); out['(35) holds']=bool(lb>=la)
    # same on mean sector
    lb0=sla.eigh(ns0.T@(A0+cA*G0+2*np.outer(Mc[idx],Mc[idx]))@ns0,ns0.T@G0@ns0,eigvals_only=True)[0]
    la0=sla.eigh(ns0.T@(cA*G0-P0+2*np.outer(Ms[idx],Ms[idx]))@ns0,ns0.T@G0@ns0,eigvals_only=True)[-1]
    out['(35) mean sector: lambda_min(B+), lambda_max(-A-)']=[float(lb0),float(la0)]
    return out

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--set',default='6'); ap.add_argument('--K',type=int,default=4)
    ap.add_argument('--h',type=float,default=0.02); ap.add_argument('--XI',type=float,default=20000.0)
    ap.add_argument('--no-offsets',action='store_true'); ap.add_argument('--width',default='fixed',help='fixed | lin | sqrt : delta = delta0*(logP/log3)^pow'); ap.add_argument('--K0',type=int,default=0); ap.add_argument('--out',default='/home/chirurgie/.claude/jobs/4b35770d/tmp/six_centre')
    a=ap.parse_args()
    sets={'3':[2,3],'4':[2,3,5],'5':[2,3,5,7],'6':[2,3,5,7,11],'7':[2,3,5,7,11,13],'8':[2,3,5,7,11,13,17],'10':[2,3,5,7,11,13,17,19,23],'12':[2,3,5,7,11,13,17,19,23,29,31],'14':[2,3,5,7,11,13,17,19,23,29,31,37,41],'16':[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]}
    xs=[0.0]+[np.log(p) for p in sets[a.set]]
    d0=(np.log(3)-np.log(2))/8; n=xs[-1]; n0=np.log(3)
    delta={'fixed':d0,'lin':d0*n/n0,'sqrt':d0*np.sqrt(n/n0)}[a.width]
    R=build(xs,a.K,a.h,a.XI,no_offsets=a.no_offsets,delta=delta)
    res=analyse(R,f'centres={a.set} K={a.K} h={a.h} XI={a.XI} width={a.width} delta={delta:.5f}')
    fn=f"{a.out}/sc_{a.set}_K{a.K}_h{a.h}_XI{int(a.XI)}{'_nooff' if a.no_offsets else ''}{'' if a.width=='fixed' else '_'+a.width}.json"
    json.dump(res,open(fn,'w'),indent=1,default=str)
    np.savez(fn.replace('.json','.npz'),**{k:v for k,v in R.items() if isinstance(v,np.ndarray)})
    for k,v in res.items():
        if k!='atoms': print(k,':',v)
    print('atoms:'); [print('  ',n,'w=%.5f'%wn,hits) for n,wn,hits in res['atoms']]
