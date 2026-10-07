"""Exact local checks; not a certificate for an infinite sum or RH."""
from fractions import Fraction as F
from itertools import product

# Sparse polynomial over Q in Q,v,w,d.
class P:
    def __init__(self, x=0):
        self.c = x if isinstance(x, dict) else {(0,0,0,0): F(x)}
        self.c = {k:v for k,v in self.c.items() if v}
    def __add__(self, y):
        y = y if isinstance(y,P) else P(y)
        z=self.c.copy()
        for k,v in y.c.items(): z[k]=z.get(k,0)+v
        return P(z)
    __radd__=__add__
    def __neg__(self): return P({k:-v for k,v in self.c.items()})
    def __sub__(self,y): return self+-y if isinstance(y,P) else self+(-P(y))
    def __rsub__(self,y): return P(y)+-self
    def __mul__(self,y):
        y=y if isinstance(y,P) else P(y);z={}
        for a,x in self.c.items():
            for b,v in y.c.items():
                k=tuple(i+j for i,j in zip(a,b));z[k]=z.get(k,0)+x*v
        return P(z)
    __rmul__=__mul__
Q,v,w,d=[P({tuple(int(i==j) for i in range(4)):F(1)}) for j in range(4)]
pnum=1+(w-d)*(1-v)-d*(Q-1)*w*v
astarnum=-(1-v)-(Q-1)*w*v # Pstar/d times (1-v)
anum=-(1+w+w*w)*(1-v)+d*w*(1-v)+(-Q*w+(Q-1)*d*w*w)*v
assert not (anum-(astarnum-w*pnum)).c

# Z[t]/(t^2-t+1), pairs of integer coefficients.
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]+x[1]*y[1])
def conj(x): return (x[0]+x[1],-x[1])
zero=(0,0);one=(1,0);phases=[one]
for _ in range(5): phases.append(mul(phases[-1],(0,1)))
def T(A,B,j,phase,Q):
    c=phase if j==0 else zero
    L=one if j==1 else (-(Q-1),0) if j>=2 else zero
    return {(0,0):one,(1,0):neg(conj(c)),(0,1):c,(1,1):L}.get((A,B),zero)
def D(A,B,j,phase,Q):
    c=phase if j==0 else zero
    L=one if j==1 else (-(Q-1),0) if j>=2 else zero
    return {(1,0):neg(conj(c)),(1,1):add(L,neg(one)),(1,2):neg(c),(2,1):conj(c),(2,2):neg(L)}.get((A,B),zero)
def branch(A,B,j,phase,Q,r):
    if r==0: return T(A,B,j,phase,Q) if A==1 and B in (0,1) else zero
    return neg(T(A-1,B-1,j,phase,Q)) if A in (1,2) and B in (1,2) else zero
count=0
for Qn,A,B,j,ph in product((7,13,19),range(4),range(4),(0,1,2,6),phases):
    assert D(A,B,j,ph,Qn)==add(branch(A,B,j,ph,Qn,0),branch(A,B,j,ph,Qn,1));count+=1
assert D(1,1,1,one,7)==zero and branch(1,1,1,one,7,0)==one
cells=list(product(((1,0),(1,1),(1,2),(2,1),(2,2)),(0,1,2,6),phases))
pairs=0
for (ab,j,ph),(cd,k,ps) in product(cells,repeat=2):
    full=zero
    for r,t in product((0,1),repeat=2):
        full=add(full,mul(branch(*ab,j,ph,7,r),branch(*cd,k,ps,13,t)))
    assert full==mul(D(*ab,j,ph,7),D(*cd,k,ps,13));pairs+=1
print(f'PASS: polynomial identity (16); {count} exact local checks; {pairs} full two-slot subset checks; planted missing-rescaled-term error detected.')
print('Scope: algebraic checks only; finite Fourier/CRT, analytic residue and infinite bounds require separate proofs.')
