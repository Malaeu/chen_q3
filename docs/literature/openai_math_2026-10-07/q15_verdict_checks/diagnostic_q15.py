"""Noninterval finite CCM identity diagnostics. No spectral or cofinal certificate."""
from pathlib import Path
from collections import Counter
import hashlib,json
import mpmath as mp
mp.mp.dps=50
ROOT=Path(__file__).resolve().parent

def factor(n):
    out=Counter(); p=2
    while p*p<=n:
        while n%p==0:out[p]+=1;n//=p
        p+=1
    if n>1:out[n]+=1
    return out

def mu(n):
    q=factor(n)
    return 0 if any(e>1 for e in q.values()) else (-1)**len(q)

def mang(n):
    q=factor(n)
    return mp.log(next(iter(q))) if len(q)==1 else mp.mpf(0)

def nu(n,U):return sum(mu(d) for d in range(U+1,n+1) if n%d==0)
def inn(x,y):return sum(mp.conj(x[i])*y[i] for i in range(len(x)))
def mx(A):return max(abs(v) for v in A)
def rel(A,B):return mx(A-B)/(1+mx(A)+mx(B))
rows=[]
for m,M,U,V in [(16,2,2,2),(64,3,2,3),(125,4,3,4)]:
    L=mp.log(m);js=list(range(-M,M+1)); d=len(js)
    w=[2*mp.pi*j/L for j in js]
    C=mp.matrix(d,3)
    for i in range(d):
        C[i,0]=1/mp.sqrt(d)
        C[i,1]=1/(mp.sqrt(L)*(mp.mpf('.5')-1j*w[i]))
        C[i,2]=1/(mp.sqrt(L)*(mp.mpf('.5')+1j*w[i]))
    P=mp.eye(d)-C*(C.H*C)**-1*C.H
    v=mp.matrix([mp.mpc((j+M+1)**2,(-1)**j*(j+M+2)) for j in js]);c=P*v;c/=mp.sqrt(inn(c,c))
    kernels={}
    for n in range(1,m+1):
        s=mp.log(n);Q=mp.matrix(d)
        for r,j in enumerate(js):
            for t,k in enumerate(js):
                Q[r,t]=2*(1-s/L)*mp.cos(w[r]*s) if j==k else (mp.sin(w[t]*s)-mp.sin(w[r]*s))/(mp.pi*(j-k))
        kernels[n]=P*Q*P
    S=mp.matrix(d);I=mp.matrix(d);J=mp.matrix(d);K=mp.matrix(d);II0=mp.matrix(d)
    for n in range(1,m+1):
        an=kernels[n]/mp.sqrt(n)
        S+=mang(n)*an
        if n<=V:J+=mang(n)*an
        for a in range(1,n+1):
            if n%a:continue
            k=n//a
            if a<=U:
                I+=mu(a)*mp.log(k)*an
                for b in range(2,min(V,k)+1):
                    if k%b==0:K+=mu(a)*mang(b)*an
            else:
                bv=sum(mang(b) for b in range(V+1,k+1) if k%b==0)
                II0+=mu(a)*bv*an
    II=mp.matrix(d);H=[];alpha=[];caps=[]
    for a in range(U+1,m//(V+1)+1):
        aa=nu(a,U)/mp.sqrt(a)
        if not aa:continue
        Ha=mp.matrix(d);cap=mp.mpf(0)
        for b in range(V+1,m//a+1):
            lb=mang(b)/mp.sqrt(b)
            Ha+=lb*kernels[a*b];cap+=lb
        if not cap:continue
        H.append(Ha);alpha.append(aa);caps.append(cap);II+=aa*Ha
    vec=[Ha*c for Ha in H]
    vecsum=mp.matrix(d,1)
    for aa,z in zip(alpha,vec):vecsum+=aa*z
    fullmixed=sum(alpha[i]*alpha[j]*inn(vec[i],vec[j]) for i in range(len(H)) for j in range(len(H)))
    omitted=sum(alpha[i]**2*inn(vec[i],vec[i]) for i in range(len(H)))
    cert=2*sum(abs(aa)*b for aa,b in zip(alpha,caps))
    tau=[abs(aa)/b for aa,b in zip(alpha,caps)]
    Z=sum(aa**2/t for aa,t in zip(alpha,tau))
    energy=sum(t*inn(z,z) for t,z in zip(tau,vec))
    gaps=[rel(S,I+J-K+II),rel(II,II0),abs(fullmixed-inn(vecsum,vecsum))/(1+abs(fullmixed))]
    assert max(gaps)<mp.mpf('1e-43')
    assert mx(C.H*c)<mp.mpf('1e-43')
    assert mp.re(Z*energy-inn(vecsum,vecsum))>-mp.mpf('1e-40')
    assert abs(fullmixed-omitted)>mp.mpf('1e-12')
    def f(t):return sum(c[j]*mp.exp(1j*w[j]*t) for j in range(d))/mp.sqrt(L)
    n=3;s=mp.log(n)
    overlap=2*mp.re(mp.quad(lambda t:mp.conj(f(t))*f(t+s),[0,L-s]))
    sourceform=mp.re(inn(c,kernels[n]*c))
    err=abs(overlap-sourceform)
    assert err<mp.mpf('1e-43')
    rows.append({'m':m,'M':M,'U':U,'V':V,
       'schedule':'FINITE_KERNEL_IDENTITY_DIAGNOSTIC_NOT_LATE_FIXED_SMALL_EPSILON',
       'constraint_residual':mp.nstr(mx(C.H*c),10),
       'max_reassembly_residual':mp.nstr(max(gaps),10),
       'autocorrelation_residual':mp.nstr(err,10),
       'missing_cross_detected':True,
       'certificate':mp.nstr(cert,15),
       'chosen_Rayleigh_II':mp.nstr(mp.re(inn(c,II*c)),15),
       'weight': 'same normalized rank-one W=c c* everywhere'})
out={'status':'PASS_NONINTERVAL_NOT_SPECTRAL_OR_ASYMPTOTIC','mpmath':mp.__version__,
     'decimal_digits':mp.mp.dps,'cases':len(rows),'rows':rows,
     'full_CCM_spectra_computed':False,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
