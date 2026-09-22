from fractions import Fraction as F

def add(a,b):
 c=dict(a)
 for k,v in b.items(): c[k]=c.get(k,F(0))+v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for i,x in a.items():
  for j,y in b.items(): c[i+j]=c.get(i+j,F(0))+x*y
 return {k:v for k,v in c.items() if v}
def sc(a,c):return {k:v*c for k,v in a.items() if v*c}
def der(a):return {k-1:k*v for k,v in a.items() if k}
def A(p,n):return add(add(sc(der(der(p)),-1),mul({1:F(4)},der(p))),sc(p,-4*n))
def T(p):return add(add(mul({2:F(1)},der(der(p))),mul({1:F(2),3:F(-4)},der(p))),mul({4:F(4),2:F(-6)},p))
def solve(mat):
 n=len(mat)
 for j in range(n):
  i=next(i for i in range(j,n) if mat[i][j])
  mat[j],mat[i]=mat[i],mat[j];c=mat[j][j];mat[j]=[x/c for x in mat[j]]
  for i in range(n):
   if i!=j:
    c=mat[i][j];mat[i]=[a-c*b for a,b in zip(mat[i],mat[j])]
 return [row[-1] for row in mat]
for n,p in [(0,{0:F(1)}),(4,{0:F(3),2:F(-24),4:F(16)})]:
 beta=-F((2*n+1)**2+5,8)
 powers=list(range(0,n+5,2));rhs=add(sc(p,beta),sc(T(p),-1))
 # Free multiple of P fixed by Q(0)=0; omit highest identically-zero equation.
 rows=[[A({d:F(1)},n).get(k,F(0)) for d in powers]+[rhs.get(k,F(0))] for k in powers[:-1]]
 rows.append([F(d==0) for d in powers]+[F(0)])
 q=dict(zip(powers,solve(rows)))
 assert A(q,n)==rhs
 residual=add(T(q),sc(q,-beta))
 assert q[0]==0
 print('n=',n,'beta=',beta,'P=',p,'Q=',q,'R=',residual)
 print('EXACT: (L_m-(pi*(4*n+2)+beta/m)) exp(-t²)*(P+Q/(pi*m)) = exp(-t²)*R/(pi*m²)')
