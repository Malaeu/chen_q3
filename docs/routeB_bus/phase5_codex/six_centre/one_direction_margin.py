"""Proshka's one-direction implementation (5) of the D24 target, tested numerically on source-defined directions.
For a direction d in K_a (G-orthogonal to p = cut-Phi/||.||): u = Q[d], B = Q(d,p), J = |B|^2/u (recovered energy),
residual quotient q(d) = (r - J)/(1 + |B/u|^2 ||d||^2) = Rayleigh of p - (B/u) d  (upper bound for lambda_1).
Directions: cut-offs of the radical family g_k = (d^2 - 1/4) d^k Phi (even k), the cut of x^2 Phi, and the numerical
optimum y = C^{-1} b (reference, J = b*C^{-1}b). Source: window_derivative_K36_vec_matrices.npz. DIAGNOSTIC_NEVER_A_PROOF."""
import numpy as np, json, sys
import scipy.linalg as sla
from numpy.polynomial import legendre as Lg
z=np.load(sys.argv[1])
def Phi(x,N=8):
    x=np.abs(np.asarray(x,float)); s=np.zeros_like(x)
    for n in range(1,N+1): s+=(2*np.pi**2*n**4*np.exp(4.5*x)-3*np.pi*n**2*np.exp(2.5*x))*np.exp(-np.pi*n**2*np.exp(2*x))
    return s
# Exact derivatives of the theta series: each term is P(y) e^{alpha x} e^{-pi n^2 y}, y = e^{2x};
# d/dx [P(y) e^{alpha x} e^{-pi n^2 y}] = [2 y P'(y) + alpha P(y) - 2 pi n^2 y P(y)] e^{alpha x} e^{-pi n^2 y}.
def Phi_deriv(x, k, N=8):
    x=np.abs(np.asarray(x,float)); y=np.exp(2*x); s=np.zeros_like(x)
    sgn = 1.0  # Phi even: odd derivatives at negative x flip sign, but we only use even k here
    for n in range(1,N+1):
        for alpha,c0 in ((4.5, 2*np.pi**2*n**4), (2.5, -3*np.pi*n**2)):
            P=np.array([c0])                      # polynomial in y, ascending powers
            for _ in range(k):
                dP=np.polynomial.polynomial.polyder(P) if len(P)>1 else np.array([0.0])
                term1=np.concatenate([[0.0],2*dP])   # 2 y P'(y)
                term2=alpha*P
                term3=np.concatenate([[0.0],-2*np.pi*n*n*P])  # -2 pi n^2 y P
                L=max(len(term1),len(term2),len(term3)); P=np.zeros(L)
                for tt in (term1,term2,term3): P[:len(tt)]+=tt
            s+=np.polynomial.polynomial.polyval(y,P)*np.exp(alpha*x)*np.exp(-np.pi*n*n*y)
    return s
def g_k(k):
    return lambda x: Phi_deriv(x,k+2)-0.25*Phi_deriv(x,k)
def coeffs(fun,a):
    x,w=np.polynomial.legendre.leggauss(K+40); f=fun(a*x)
    return np.array([(2*k+1)/2*np.sum(w*f*Lg.legval(x,np.eye(K)[k])) for k in range(K)])
cands={f'g{k}':g_k(k) for k in (0,2,4,6,8,10,12)}
cands.update({'x2Phi':lambda x: x*x*Phi(x),'x4Phi':lambda x: x**4*Phi(x)})
SPANS={'span_g0-4':['g0','g2','g4'],'span_g0-8':['g0','g2','g4','g6','g8'],'span_g0-12':['g0','g2','g4','g6','g8','g10','g12'],'span_all':list(cands)}
out={}
keys=sorted({k.rsplit('_',1)[0] for k in z.files}, key=float)
print(" a     T          lam1        r=Q[p]     | direction : u=Q[d]     B=Q(d,p)    J=|B|^2/u   1-J/r      q(d)=Rayleigh(p-zd)  q/lam1")
for a in keys:
    Q=z[f'{a}_Q']; G=z[f'{a}_G']; c=z[f'{a}_c']; lam1=float(z[f'{a}_ev'][0]); af=float(a)
    K=Q.shape[0]
    if Q.shape != (K,K) or G.shape != (K,K) or c.shape != (K,):
        raise ValueError(f'inconsistent matrix/coefficient shapes at a={a}')
    L=sla.cholesky(G,lower=True)
    A=sla.solve_triangular(L,Q,lower=True)
    A=sla.solve_triangular(L,A.T,lower=True).T
    floating_scale=float(np.finfo(float).eps*max(1.0,np.linalg.norm(A,2)))
    p=c/np.sqrt(c@G@c); r=float(p@Q@p)
    # tail mass for reference
    from scipy.integrate import quad
    I=quad(lambda x:Phi(x)**2,-6,6,limit=400)[0]; T=2*quad(lambda x:Phi(x)**2,af,6,limit=400)[0]/I
    row={}
    for name,fun in cands.items():
        if name not in ('g0','g2','g12','x2Phi'): 
            d=coeffs(fun,af); d=d-(p@G@d)*p; d=d/np.sqrt(d@G@d); u=float(d@Q@d); B=float(d@Q@p); J=B*B/u if u>0 else float('nan'); zc=B/u if u>0 else float('nan'); q=(r-J)/(1+zc*zc) if u>0 else float('nan'); row[name]=dict(u=u,B=B,J=J,one_minus_J_over_r=1-J/r if u>0 else None,q=q,q_over_lam1=q/lam1 if u>0 else None); continue
        d=coeffs(fun,af); d=d-(p@G@d)*p            # G-orthogonalise against p
        d=d/np.sqrt(d@G@d)
        u=float(d@Q@d); B=float(d@Q@p); J=B*B/u if u>0 else float('nan')
        zc=B/u if u>0 else float('nan'); q=(r-J)/(1+zc*zc) if u>0 else float('nan')
        row[name]=dict(u=u,B=B,J=J,one_minus_J_over_r=1-J/r if u>0 else None,q=q,q_over_lam1=q/lam1 if u>0 else None)
        print(f"{a}  {T:.3e}  {lam1:.3e}  {r:.3e}  | {name:6s}: {u:.3e}  {B:+.3e}  {J:.3e}  {1-J/r if u>0 else float('nan'):.3e}  {q:.3e}          {q/lam1 if u>0 else float('nan'):.3e}")
    for sname,members in SPANS.items():
        Dm=np.column_stack([coeffs(cands[m],af) for m in members]); Dm=Dm-np.outer(p,(p@G@Dm))
        Dm=Dm/np.sqrt(np.einsum('ij,jk,ki->i',Dm.T,G,Dm))[None,:]   # unit G-norm columns (conditioning)
        Cs=Dm.T@Q@Dm; bs=Dm.T@Q@p; Gs=Dm.T@G@Dm
        ce=np.linalg.eigvalsh(Cs)
        condition=float(np.linalg.cond(Cs))
        residual=float('inf'); qdirect=float('nan'); discrepancy=float('inf')
        try:
            ys=np.linalg.solve(Cs,bs); J5=float(bs@ys); q5=(r-J5)/(1+float(ys@Gs@ys))
            residual=float(np.linalg.norm(Cs@ys-bs)/(np.linalg.norm(Cs,2)*np.linalg.norm(ys)+np.linalg.norm(bs)))
            trial=p-Dm@ys
            qdirect=float(trial@Q@trial/(trial@G@trial))
            discrepancy=abs(qdirect-q5)
        except np.linalg.LinAlgError:
            J5=q5=float('nan')
        qscale=max(floating_scale,discrepancy)
        resolved=bool(np.isfinite(qdirect) and condition*np.finfo(float).eps<=1e-3 and residual<=1e-10 and lam1>qscale)
        row[sname]=dict(J=J5,one_minus_J_over_r=1-J5/r,q=q5,q_over_lam1=q5/lam1,C_min_eig=float(ce[0]),q_direct=qdirect,q_cancel=q5,direct_cancel_discrepancy=discrepancy,floating_scale=floating_scale,q_diagnostic_scale=qscale,C_condition=condition,solve_relative_residual=residual,local_status='RESOLVED_DIAGNOSTIC_ONLY' if resolved else 'UNRESOLVED')
        print(f"{a}  {sname:11s}: J={J5:.3e}  1-J/r={1-J5/r:.3e}  q={q5:.3e}  q/lam1={q5/lam1:.3e}  minEig(C)={ce[0]:.2e}")
    out[a]=dict(T=T,lam1=lam1,r=r,K=K,floating_scale=floating_scale,dirs=row)
json.dump(out,open(sys.argv[1].replace('_matrices.npz','_one_direction.json'),'w'),indent=1)
