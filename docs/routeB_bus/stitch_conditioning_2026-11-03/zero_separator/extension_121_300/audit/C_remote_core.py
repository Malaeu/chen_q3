"""Raw physical evaluation rows and high-precision conditioning, finite only."""
from pathlib import Path
import csv,json,sys,time,math
import mpmath as mp
P=Path(__file__).resolve().parent;BUS=P.parents[1]
sys.path.insert(0,str(BUS/'capacity_matrix_2026-11-02'))
from capacity import Erow
ZPATH=BUS/'capacity_matrix_2026-11-02/zeros.csv';DPATH=BUS/'fake_worlds_2026-11-02/dh_zeros.json'

def events(world):
 if world in ('zeta','plant'):
  out=[dict(gamma=r['gamma'],imag='0',kind='line',multiplicity=1) for r in csv.DictReader(ZPATH.open())]
 else:
  z=json.loads(DPATH.read_text());out=[dict(gamma=r['gamma'],imag='0',kind='line',multiplicity=1) for r in z['critical_line_zeros']]
  out += [dict(gamma=r['gamma'],imag=str(mp.mpf(r['sigma_right'])-mp.mpf('.5')),kind='quartet',multiplicity=1) for r in z['off_line_pairs']]
 if world=='plant':out.append(dict(gamma=mp.nstr(2*mp.pi/mp.log(2),mp.mp.dps),imag='.25',kind='quartet',multiplicity=1))
 return sorted(out,key=lambda z:mp.mpf(z['gamma']))

def rows_for(world,m,T):
 rs=[];labels=[];heights=[];metric=[]
 for e in events(world):
  g=mp.mpf(e['gamma'])
  if not g<T:continue
  heights.append(g)
  if e['kind']=='line':
   rs.append(Erow(g,m));labels.append(dict(**e,component='real-line'));metric.append(2*e['multiplicity'])
  else:
   row=Erow(g+mp.j*mp.mpf(e['imag']),m)
   for component,sign in [('real',1),('imag',-1)]:
    rs.append([(mp.re(x) if component=='real' else mp.im(x)) for x in row]);labels.append(dict(**e,component=component));metric.append(sign*4*e['multiplicity'])
 return mp.matrix(rs),labels,heights,metric

def solve_chol(L,b):
 n=L.rows;y=[mp.mpf(0)]*n;x=[mp.mpf(0)]*n
 for i in range(n):y[i]=(b[i]-mp.fsum(L[i,j]*y[j] for j in range(i)))/L[i,i]
 for i in range(n-1,-1,-1):x[i]=(y[i]-mp.fsum(L[j,i]*x[j] for j in range(i+1,n)))/L[i,i]
 return mp.matrix(x)

def sigma_min(E,target='1e-30',maxiter=100):
 start=time.monotonic();wide=E.rows<=E.cols;H=E*E.T if wide else E.T*E
 L=mp.cholesky(H);n=H.rows;v=mp.matrix([mp.mpf((i*37+11)%97-48)/97 for i in range(n)]);v/=mp.norm(v)
 last=None;converged=False
 for it in range(maxiter):
  y=solve_chol(L,v);v=y/mp.norm(y)
  image=E.T*v if wide else E*v;lam=mp.fdot(image,image)
  residual=mp.norm(H*v-lam*v);relative=residual/abs(lam)
  change=abs(lam-last)/abs(lam) if last else mp.inf
  if relative<mp.mpf(target) and change<mp.mpf(target):converged=True;break
  last=lam
 if not converged:raise ArithmeticError(f'inverse iteration unresolved: rel={relative}')
 sm=mp.sqrt(lam);left=v if wide else E*v/sm
 return dict(sigma=sm,squared=lam,left=left,iterations=it+1,relative_residual=relative,relative_change=change,seconds=time.monotonic()-start,min_chol=min(L[i,i] for i in range(n)))

def row_basis(E,guard_digits=55):
 """MP modified Gram-Schmidt with two reorthogonalization passes."""
 start=time.monotonic();basis=[];check=[];d=E.cols
 for i in range(E.rows):
  if len(basis)==d:break
  v=[E[i,j] for j in range(d)];norm0=mp.sqrt(mp.fsum(x*x for x in v))
  for repeat in range(2):
   for u in basis:
    dot=mp.fsum(v[j]*u[j] for j in range(d));v=[v[j]-dot*u[j] for j in range(d)]
  norm=mp.sqrt(mp.fsum(x*x for x in v))
  if norm<mp.mpf(10)**(-guard_digits)*max(1,norm0):raise ArithmeticError(f'row rank unresolved {i}, norm={norm}')
  basis.append([x/norm for x in v]);check.append(norm)
 return mp.matrix(basis),dict(seconds=time.monotonic()-start,min_residual_row_norm=min(check))

def cutoff(m,c):
 L=mp.log(m);return (1+mp.mpf(c)*(1+mp.log(L))/L)*2*mp.pi*m/L
