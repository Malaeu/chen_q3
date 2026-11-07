"""Consistency judge for Proshka K: flux F(X)=P(X)-P(2X)/2, P(X)=X^-2 sum_{X<=k<2X} S(k)^2,
S(k)=sum_{k/2<n<=k}(1_prime(n) log n - 1). Planted world: add derivative of a fake zero term
to the prime density: weight w(n) = 1_p log n + 2*Re(n^{rho-1}) with rho=beta+i*gamma (off-line)."""
import numpy as np, sys, time
J=int(sys.argv[1]) if len(sys.argv)>1 else 24
M=2**(J+2)+2
t0=time.time()
sieve=np.ones(M,dtype=bool); sieve[:2]=False
for p in range(2,int(M**0.5)+1):
    if sieve[p]: sieve[p*p::p]=False
n=np.arange(M,dtype=np.float64)
def run(w,label):
    a=np.concatenate([[0.0],np.cumsum(w[1:]-1.0)])     # A(k)=sum_{1<=n<=k}(w(n)-1)
    k=np.arange(M); S=a-a[k//2]
    S2=np.concatenate([[0.0],np.cumsum(S[1:]**2)])
    P=lambda X: (S2[2*X-1]-S2[X-1])/X**2
    print(f"--- {label}")
    print(" j    P(2^j)      F(2^j)      R_j")
    R=[]
    for j in range(8,J+1):
        X=2**j; F=P(X)-0.5*P(2*X); r=F/(np.sqrt(P(2*X))+1); R.append(r)
        print(f"{j:3d} {P(X):10.4f} {F:+11.4f} {r:+8.3f}")
    return np.array(R)
w=np.where(sieve,np.log(np.maximum(n,1)),0.0)
R_true=run(w,"true primes")
beta,gamma=0.8,20.0
with np.errstate(divide='ignore',invalid='ignore'):
    fake=2*np.real(np.where(n>0,(n+0j)**(complex(beta,gamma)-1),0))
R_fake=run(w-fake,f"planted zero beta={beta}, gamma={gamma}")
lo,hi=slice(2,8),slice(12,None)
print(f"true : max|R| j=10..15 {np.abs(R_true[lo]).max():.3f}  j=20..{J} {np.abs(R_true[hi]).max():.3f}")
print(f"fake : max R   j=10..15 {R_fake[lo].max():.3f}  j=20..{J} {R_fake[hi].max():.3f}  ratio {R_fake[hi].max()/max(R_fake[lo].max(),1e-9):.1f}")
print(f"time {time.time()-t0:.0f}s")
