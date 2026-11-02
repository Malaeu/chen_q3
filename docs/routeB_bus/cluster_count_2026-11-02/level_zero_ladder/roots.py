"""Exact-rational polynomial isolation seeds, independently refined physical Fourier roots.
Numerical roots of approximate eigenvectors; no mathematical completeness certificate.
"""
from pathlib import Path
import json,csv,sys,hashlib,time
import mpmath as mp
import sympy as sp
OUT=Path(__file__).resolve().parent

def write(rows,name):
 if not rows:return
 with (OUT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
def run(m,dps=180,order=160):
 mp.mp.dps=dps;p=OUT/f'cell_m{m}_dps{dps}_gl{order}.json';data=json.loads(p.read_text());L=mp.log(m);b=L/2;omega=2*mp.pi/L
 V=mp.matrix(data['V']);ev=list(map(mp.mpf,data['lambda_']));indices=[i for i,x in enumerate(ev) if x>=mp.mpf(m)**-8]
 x=sp.Symbol('x');products=[]
 for n in range(m+1):
  pol=sp.Poly(1,x)
  for k in range(m+1):
   if k!=n:pol*=sp.Poly(x-sp.Rational(k*k,m*m),x)
  products.append(pol)
 def sincprime(z):return (z*mp.cos(z)-mp.sin(z))/(z*z) if z else mp.mpf(0)
 def F(c,t,derivative=False):
  if derivative:return mp.fsum(c[n]*(-1)**n*b*b/mp.sqrt(L)*(sincprime((t-n*omega)*b)+sincprime((t+n*omega)*b)) for n in range(m+1))
  return mp.fsum(c[n]*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-n*omega)*b)+mp.sinc((t+n*omega)*b)) for n in range(m+1))
 def fast(c,t):
  if min(abs(t-k*omega) for k in range(m+1))<mp.mpf('1e-30'):return F(c,t)
  return 2*t*mp.sin(t*b)/mp.sqrt(L)*mp.fsum(c[n]/(t*t-(n*omega)**2) for n in range(m+1))
 rows=[];checks=[];start=time.monotonic()
 for i in indices:
  c=[V[n,i]*(1 if n==0 else mp.sqrt(2)) for n in range(m+1)]
  pol=sum((sp.Rational(mp.nstr(c[n],100))*products[n] for n in range(m+1)),sp.Poly(0,x))
  intervals=sp.polys.polytools.intervals(pol,eps=sp.Rational(1,10**35));positive=[];maxres=mp.mpf(0)
  for (lo,hi),mult in intervals:
   if hi<=0:continue
   cv=lambda q:mp.mpf(str(q.p))/mp.mpf(str(q.q))
   seed=m*omega*mp.sqrt((cv(lo)+cv(hi))/2)
   root=mp.findroot(lambda t:F(c,t),seed,df=lambda t:F(c,t,True),solver='newton',tol=mp.mpf('1e-125'),maxsteps=40)
   if root<=0 or abs(root-seed)>mp.mpf('1e-20')*max(1,abs(seed)):raise ValueError(('seed drift',m,i,str(seed),str(root)))
   residual=abs(F(c,root));maxres=max(maxres,residual);positive.append(root)
   rows.append(dict(m=m,i=i,t_root=mp.nstr(root,125),kind='off_lattice',polynomial_multiplicity=mult,direct_F_residual=mp.nstr(residual,30),normalized_residual=mp.nstr(residual/mp.sqrt(L),30),source_dps=dps))
  for k in range(m+1,int(mp.ceil(120/omega))+2):
   root=k*omega;residual=abs(F(c,root));positive.append(root)
   rows.append(dict(m=m,i=i,t_root=mp.nstr(root,125),kind='structural_exterior',polynomial_multiplicity=0,direct_F_residual=mp.nstr(residual,30),normalized_residual=mp.nstr(residual/mp.sqrt(L),30),source_dps=dps))
  # Independent uniform-frequency sign scan, avoiding lattice by irrational offset.
  step=mp.mpf('0.05');grid=[mp.mpf('0.013')+step*k for k in range(2401)];values=[fast(c,t) for t in grid]
  brackets=[(a,z) for a,z,u,v in zip(grid,grid[1:],values,values[1:]) if u*v<0]
  unmatched=[(mp.nstr(a,20),mp.nstr(z,20)) for a,z in brackets if not any(a<=r<=z for r in positive)]
  checks.append(dict(m=m,i=i,rational_polynomial_real_root_count=len(intervals),polynomial_degree=pol.degree(),real_root_multiplicity=sum(mult for _,mult in intervals),positive_y_root_count=sum(lo>0 for (lo,hi),mult in intervals),negative_y_root_count=sum(hi<0 for (lo,hi),mult in intervals),nonreal_y_root_count=pol.degree()-sum(mult for _,mult in intervals),positive_off_lattice_count=sum(r['i']==i and r['kind']=='off_lattice' for r in rows),sign_scan_crossings=len(brackets),unmatched_sign_brackets=unmatched,max_direct_root_residual=mp.nstr(maxres,40),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),polynomial_coefficient_digits=100,sign_scan_step='0.05',scope='Exact isolation for rounded polynomial; physical direct-root refinement and sign scan are numerical checks, not an interval certificate'))
  write(rows,f'root_results_m{m}_dps{dps}.csv');(OUT/f'root_results_m{m}_dps{dps}.json').write_text(json.dumps(checks,indent=2)+'\n')
  print(m,i,len(positive),len(unmatched),round(time.monotonic()-start,2),flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
