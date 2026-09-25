"""DIAGNOSTIC ONLY. Literal full K and Q5 Gaussian plane, R3 full quartic.
Sources: CCMFiniteWeilSourceMatrixN1.lean:40-101; NULLPLANE verdict Q5;
FULL_SCALAR_SIGN_CHAIN verdict R3. No certified quadrature/tail enclosure.
"""
import argparse,json,time
from functools import lru_cache
import mpmath as mp
import rectangle_probe as rp

def matrix_K(m):
    L=mp.log(m); modes=list(range(-m,m+1)); K=mp.zeros(len(modes))
    def q(x,n,j):
        if n==j: return 2*(L-x)/L*mp.cos(2*mp.pi*n*x/L)
        return (mp.sin(2*mp.pi*j*x/L)-mp.sin(2*mp.pi*n*x/L))/(mp.pi*(n-j))
    def mang(k):
        for p in range(2,k+1):
            if any(p%d==0 for d in range(2,int(p**.5)+1)): continue
            a=p
            while a<k: a*=p
            if a==k:return mp.log(p)
        return mp.mpf(0)
    grid=[L*k/8 for k in range(9)]
    # Linearity of the off-diagonal sine difference reduces quadrature to O(m) moments.
    moments={0:mp.mpf(0)};diagonals={}
    for n in range(m+1):
        omega=2*mp.pi*n/L
        if n:
            sn=mp.quad(lambda x:omega/2 if not x else mp.exp(x/2)*mp.sin(omega*x)/(2*mp.sinh(x)),grid)
            moments[n]=sn;moments[-n]=-sn
        diagonals[n]=mp.quad(lambda x:mp.mpf('0.5')-1/L if not x else (mp.exp(x/2)*q(x,n,n)-2)/(2*mp.sinh(x)),grid)
    constant=mp.euler+mp.log(4*mp.pi*mp.tanh(L/2))
    for i,n in enumerate(modes):
      for j in range(i,len(modes)):
        v=modes[j]
        w02=32*L*mp.sinh(L/4)**2*(L**2-16*mp.pi**2*v*n)/((L**2+16*mp.pi**2*v*v)*(L**2+16*mp.pi**2*n*n))
        wr=constant+diagonals[abs(n)] if n==v else (moments[v]-moments[n])/(mp.pi*(n-v))
        prime=mp.fsum(mang(k)/mp.sqrt(k)*q(mp.log(k),n,v) for k in range(2,m+1))
        K[i,j]=K[j,i]=w02-wr-prime
    return K

def gaussian_plane(m):
    L=mp.log(m); b=L/2
    # Fixed truncation is diagnostic; choose far beyond precision at t=-b.
    cutoff=int(mp.ceil(mp.sqrt(m*(mp.mp.dps+20)*mp.log(10)/mp.pi)))+3
    @lru_cache(maxsize=None)
    def G_cached(t, precision):
        u=mp.exp(t)
        return mp.exp(t/2)*mp.fsum((24*mp.pi*(r*u)**2-16*mp.pi**2*(r*u)**4)*mp.exp(-mp.pi*(r*u)**2) for r in range(1,cutoff+1))
    def G(t):
        return G_cached(t,mp.mp.prec)
    # G is exactly even; evaluate direct formula for consistency as well.
    gp=mp.diff(G,b)
    bpos=[(-1)**n*2/mp.sqrt(L)*mp.quad(lambda t:G(t)*mp.cos(2*mp.pi*n*t/L),[0,b/2,b]) for n in range(m+1)]
    bs=mp.matrix([bpos[abs(n)] for n in range(-m,m+1)])
    ds=mp.matrix([-(2*mp.pi*n/L)**2*bs[n+m]+2*gp/mp.sqrt(L) for n in range(-m,m+1)])
    V=mp.matrix([[bs[i],ds[i]] for i in range(2*m+1)])
    Pi=V*(V.T*V)**-1*V.T
    return Pi,abs(G(-b)-G(b)),cutoff

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--m',type=int,default=2);ap.add_argument('--dps',type=int,default=70);a=ap.parse_args();mp.mp.dps=a.dps
    # Adapt to rp public APIs after its creation.
    rp._mp_kernel=lru_cache(maxsize=None)(rp._mp_kernel)  # one fixed precision per process
    m=a.m;t=time.time(); intervals=rp.bracket(m);print('brackets ready',flush=True)
    c0=sum(intervals[0])/2;c4=sum(intervals[4])/2
    P0=rp.recurrence(m,c0)[0];P4=rp.recurrence(m,c4)[0]
    F=rp.F_matrix(m);z=F*mp.matrix([(-1)**k*(P0[k]-P4[k]) for k in range(1,6*m)])
    K=matrix_K(m);Pi,evenerr,cut=gaussian_plane(m)
    X2=mp.re((z.H*z)[0]);p=Pi*z;Y2=mp.re((p.H*p)[0]);theta=mp.re(mp.fsum((Pi*K*Pi)[i,i] for i in range(2*m+1)))
    qform=lambda v:mp.re((v.H*K*v)[0])
    pc=Y2*(qform(z)-theta*X2)+X2*qform(p)
    az=qform(z)/X2; av=theta-qform(p)/Y2
    norm=lambda v:mp.sqrt(mp.re((v.H*v)[0]))
    result={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':m,'dps':a.dps,'central_quartic':mp.nstr(pc,30),'norm_z':mp.nstr(mp.sqrt(X2),30),'norm_Pi_z':mp.nstr(mp.sqrt(Y2),30),'central_trial_rayleigh':mp.nstr(az,30),'central_competitor_rayleigh':mp.nstr(av,30),'central_tau':mp.nstr(av-az,30),'quartic_identity_error':mp.nstr(abs(pc-X2*Y2*(az-av)),8),'projection_error':mp.nstr(mp.norm(Pi*Pi-Pi),8),'gaussian_parity_error':mp.nstr(evenerr,8),'gaussian_terms':cut,'seconds':time.time()-t}
    gamma=mp.norm(K);frob=mp.norm(F)
    half={i:(intervals[i][1]-intervals[i][0])/2 for i in (0,4)}
    rb={i:rp.r6_bounds(m,intervals[i]) for i in (0,4)}
    V={i:frob*rp._norm(rb[i][1][1:]) for i in (0,4)}
    J={i:frob*rp._norm(rb[i][2][1:]) for i in (0,4)}
    sens=mp.fsum(half[i]*V[i] for i in (0,4));R=mp.sqrt(X2)+sens;y=mp.sqrt(Y2)-sens
    grad={}
    for idx,center,sign in ((0,c0,1),(4,c4,-1)):
        dp=rp.recurrence(m,center)[1]
        zi=F*mp.matrix([sign*(-1)**k*dp[k] for k in range(1,6*m)])
        ai=2*mp.re((zi.H*p)[0]);bi=2*mp.re((zi.H*(K*z-theta*z))[0]);ci=2*mp.re((zi.H*z)[0]);di=2*mp.re((zi.H*Pi*K*p)[0])
        grad[idx]=ai*(qform(z)-theta*X2)+Y2*bi+ci*qform(p)+X2*di
    drect=mp.fsum(half[i]*abs(grad[i]) for i in (0,4))
    drect+=mp.fsum(half[i]*half[j]*(48*gamma*R**2*V[i]*V[j]+(16*gamma*R**3*J[i] if i==j else 0))/2 for i in (0,4) for j in (0,4))
    ktail=5*m-1
    etail=mp.sqrt(m*(mp.sqrt(m)-1/mp.sqrt(m)))*mp.mpf(2)**(-m)*mp.fsum(abs(P[ktail])+half[i]*rb[i][1][ktail] for i,P in ((0,P0),(4,P4)))
    budget=2*gamma*etail*(2*R+etail)+4*gamma*R**2*etail/y if y>0 else mp.inf
    result.update({key:mp.nstr(value,30) for key,value in {'Gamma_Frobenius':gamma,'sensitivity':sens,'R':R,'y_minus':y,'D_rect':drect,'normalized_tail_eta_upper':etail,'R_squared_Bhat':R**2*budget,'D_plus':pc-drect-R**2*budget,'D_minus':-pc-drect-R**2*budget}.items()})
    canonical_gamma=2*mp.sqrt(m)+4*mp.sqrt(m)*mp.log(m)+9+(20*mp.pi*m+20*m+10)/mp.log(m)
    result.update({key:mp.nstr(value,30) for key,value in {'canonical_Gamma':canonical_gamma,'canonical_R_squared_Bhat':R**2*budget*canonical_gamma/gamma,'D_minus_canonical_B':-pc-drect-R**2*budget*canonical_gamma/gamma}.items()})
    result['D_plus_minus_scope']='Sharper Frobenius remainder; D_minus_canonical_B preserves the original analytic budget.'
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
