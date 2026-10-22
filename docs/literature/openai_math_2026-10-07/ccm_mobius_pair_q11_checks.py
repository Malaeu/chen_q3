from collections import defaultdict

def fac(n):
 d={};p=2
 while p*p<=n:
  while n%p==0:d[p]=d.get(p,0)+1;n//=p
  p+=1
 if n>1:d[n]=d.get(n,0)+1
 return d

def mu(n):
 d=fac(n);return 0 if any(x>1 for x in d.values()) else (-1)**len(d)
def add(dst,n,k,c):
 for p,e in fac(k).items():dst[n,p]+=c*e

def clean(a):return {k:v for k,v in a.items() if v}
def merge(*aa):
 d=defaultdict(int)
 for a in aa:
  for k,v in a.items():d[k]+=v
 return clean(d)
checks=0;miss_upper=False;miss_threshold=False
for m in range(4,81):
 for R in range(2,m):
  src=defaultdict(int);common=defaultdict(int);upper=defaultdict(int);threshold=defaultdict(int)
  for d in range(R+1,m+1):
   for k in range(1,m//d+1):add(src,d*k,k,mu(d))
  for d in range(1,m+1,2):
   if d>R:
    for k in range(1,m//(2*d)+1):
     add(common,d*k,k,mu(d));add(common,2*d*k,k,-mu(d))
    for k in range(m//(2*d)+1,m//d+1):add(upper,d*k,k,mu(d))
   elif 2*d>R:
    for k in range(1,m//(2*d)+1):add(threshold,2*d*k,k,-mu(d))
  assert clean(src)==merge(common,upper,threshold);checks+=1
  miss_upper|=clean(src)!=merge(common,threshold)
  miss_threshold|=clean(src)!=merge(common,upper)
assert miss_upper and miss_threshold
print('PASS',checks,'full formal-log source identities; both omitted-strip plants detected')
