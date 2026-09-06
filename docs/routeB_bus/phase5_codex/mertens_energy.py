import numpy as np, math, time
t0=time.time()
X=50_000_000
mu=np.ones(X+1,dtype=np.int8); mu[0]=0
isprime=np.ones(X+1,dtype=bool); isprime[:2]=False
for p in range(2,int(X**0.5)+1):
    if isprime[p]:
        isprime[p*p::p]=False
        mu[p::p]*=-1
        mu[p*p::p*p]=0
# remaining primes > sqrt(X) handled by mu[p::p]*=-1 loop above only for p<=sqrt: fix large primes
for p in np.nonzero(isprime[int(X**0.5)+1:])[0]+int(X**0.5)+1:
    mu[p::p]*=-1
M=np.cumsum(mu.astype(np.int64))
n=np.arange(1,X+1,dtype=np.float64)
g=(M[1:]/np.sqrt(n))**2   # (M(x)/sqrt x)^2 at integers
# integral over [1,X] of (M(x)/sqrt x)^2 dx/x ~ sum g(n)/n  (M constant on [n,n+1))
cum=np.cumsum(g/n)
C=2+0.5772156649015329-math.log(4*math.pi)
print("2+gamma-log(4pi) =",round(C,6))
for Xk in (10**4,10**5,10**6,10**7,X):
    print(f"X={Xk:>9d}  mean of (M/sqrt x)^2 over log-scale = {cum[Xk-1]/math.log(Xk):.5f}   M(X)/sqrt X = {M[Xk]/math.sqrt(Xk):+.4f}")
print("time",round(time.time()-t0,1),"s")
