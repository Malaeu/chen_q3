"""DIAGNOSTIC_NEVER_A_PROOF: DH literal even carrier, odd gamma factor, no pole."""
from pathlib import Path
import sys,json,csv,time
import mpmath as mp
OUT=Path(__file__).resolve().parent

def coeffs(M,mpmode=True):
 t=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
 a=[mp.mpf(0),mp.mpf(1),t,-t,mp.mpf(-1)]
 b=[mp.mpf(0)]*(M+1)
 for n in range(2,M+1):b[n]=a[n%5]*mp.log(n)-mp.fsum(b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0)
 return a,b

def build_mp(m,dps=80,order=96):
 mp.mp.dps=dps;L=mp.log(m);N=m;_,b=coeffs(m)
 gn,gw=mp.gauss_quadrature(order,'legendre');nodes=[((mp.mpf(p)+(x+1)/2)/8,w/16) for p in range(8) for x,w in zip(gn,gw)]
 sinmom=[mp.mpf(0)]*(N+1);diag=[mp.mpf(0)]*(N+1);primeS=[mp.mpf(0)]*(N+1);primeD=[mp.mpf(0)]*(N+1)
 for y,w in nodes:
  x=L*y;j=mp.exp(-mp.mpf('1.5')*x)/(-mp.expm1(-2*x));wt=L*w*j
  co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(N+1):
   sinmom[n]+=wt*sn
   diag[n]+=wt*(2*y+2*(1-y)*(1-cn)+(sn/(mp.pi*n) if n else 0))
   cn,sn=cn*co-sn*si,sn*co+cn*si
 for k in range(2,m):
  y=mp.log(k)/L;weight=b[k]/mp.sqrt(k);co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(N+1):
   primeS[n]+=weight*sn;primeD[n]+=weight*(2*(1-y)*cn-(sn/(mp.pi*n) if n else 0))
   cn,sn=cn*co-sn*si,sn*co+cn*si
 c=mp.log(5/mp.pi)+mp.digamma(mp.mpf('.75'));a=mp.exp(-L/2);tail=mp.atanh(a)-mp.atan(a)
 beta=[sinmom[i]+primeS[i] for i in range(N+1)];ds=[mp.mpf(1)]+[mp.sqrt(2)]*N;A=mp.zeros(N+1)
 for i in range(N+1):
  A[i,i]=c+diag[i]+2*tail-primeD[i]
  for k in range(i+1,N+1):A[i,k]=A[k,i]=ds[i]*ds[k]/mp.pi*(i*beta[i]-k*beta[k])/(i*i-k*k)
 return A,{'L':L,'constant':c,'arch_tail_integral':tail,'tan_theta':(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1),'b':[x for x in b]}

def run_mp(m,dps=80,order=96):
 start=time.monotonic();A,meta=build_mp(m,dps,order);ev=mp.eigsy(A,eigvals_only=True)
 fmt=lambda x:mp.nstr(x,dps)
 out={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':'Davenport-Heilbronn','m':m,'N':m,'dps':dps,'order':order,'A':[[fmt(x) for x in A[i,:]] for i in range(m+1)],'lambda_':[fmt(x) for x in ev],'minimum_lambda':fmt(ev[0]),'negative_count':sum(x<0 for x in ev),'basis':'e0=1/sqrtL; en=sqrt(2/L)*(-1)^n cos(2pi n x/L), zero outside','no_pole':True,'coefficient_recurrence':'b_n=a_n log n - sum_{d|n,1<d<n} b_d a_(n/d)','metadata':{k:[fmt(y) for y in v] if isinstance(v,list) else fmt(v) for k,v in meta.items()},'seconds':time.monotonic()-start}
 (OUT/'matrix_cells'/f'dh_m{m}_dps{dps}_gl{order}.json').write_text(json.dumps(out,indent=2)+'\n');print('MP DONE',m,dps,fmt(ev[0]),out['seconds'],flush=True)
 return out

def float_scan():
 import numpy as np
 from scipy.linalg import eigvalsh
 from scipy.special import digamma
 mp.mp.dps=80;_,bb=coeffs(120);b=np.array([float(x) for x in bb]);z,w=np.polynomial.legendre.leggauss(64)
 y=np.concatenate([(p+(z+1)/2)/8 for p in range(8)]);weights=np.tile(w/16,8)
 c=np.log(5/np.pi)+digamma(.75);rows=[]
 for m in range(2,121):
  L=np.log(m);n=np.arange(m+1);sn=np.sin(2*np.pi*n[:,None]*y);j=np.exp(-1.5*L*y)/(-np.expm1(-2*L*y));sm=sn@(L*weights*j)
  sinepart=np.zeros_like(sn);sinepart[1:]=sn[1:]/(np.pi*n[1:,None]);di=(2*y+4*(1-y)*np.sin(np.pi*n[:,None]*y)**2+sinepart)@(L*weights*j)
  ks=np.arange(2,m);ss=np.log(ks)/L;ww=b[ks]/np.sqrt(ks);ps=np.sin(2*np.pi*n[:,None]*ss)
  psum=ps@ww;pd=2*(1-ss)*np.cos(2*np.pi*n[:,None]*ss);pd[1:]-=ps[1:]/(np.pi*n[1:,None]);pdiag=pd@ww
  beta=sm+psum;ds=np.ones(m+1)*np.sqrt(2);ds[0]=1;den=n[:,None]**2-n[None,:]**2
  np.fill_diagonal(den,1);A=ds[:,None]*ds[None,:]/np.pi*(n[:,None]*beta[:,None]-n[None,:]*beta[None,:])/den
  tail=np.arctanh(np.exp(-L/2))-np.arctan(np.exp(-L/2));np.fill_diagonal(A,c+di+2*tail-pdiag)
  ev=eigvalsh(A);np.savez_compressed(OUT/'matrix_cells'/f'dh_float_m{m}.npz',A=A,lambda_=ev,L=L,m=m);scale=max(abs(ev[0]),abs(ev[-1]),1.);row={'m':m,'requested_range':m>=20,'float_lambda_min':ev[0],'float_lambda_max':ev[-1],'float_negative_count':int(sum(ev<0)),'resolved_negative_heuristic':ev[0]<-1e-10*scale,'classification':'resolved_negative_diagnostic' if ev[0]<-1e-10*scale else 'sign_unresolved_float64','dps':'float64','order':64};rows.append(row)
  if m in (2,3,4,5,6,8,12,16,20,40,60,80,100,120):print(row,flush=True)
 with (OUT/'spectrum.csv').open('w',newline='') as f:
  writer=csv.DictWriter(f,fieldnames=rows[0]);writer.writeheader();writer.writerows(rows)
 print('FIRST NEGATIVE',next((r['m'] for r in rows if r['resolved_negative_heuristic']),None),flush=True)
def run_inertia(m,dps=160,order=128):
 start=time.monotonic();A,meta=build_mp(m,dps,order);n=m+1;LL=mp.eye(n);D=[]
 for j in range(n):
  pivot=A[j,j]-mp.fsum(LL[j,k]**2*D[k] for k in range(j));D.append(pivot)
  if not pivot:raise ArithmeticError('zero LDL pivot; use eigensolver')
  for i in range(j+1,n):LL[i,j]=(A[i,j]-mp.fsum(LL[i,k]*LL[j,k]*D[k] for k in range(j)))/pivot
 residual=mp.norm(A-LL*mp.diag(D)*LL.T)
 fmt=lambda x:mp.nstr(x,dps)
 out={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':m,'dps':dps,'order':order,'method':'unpivoted symmetric LDL; nonzero pivots; inertia diagnostic','positive_pivots':sum(x>0 for x in D),'negative_pivots':sum(x<0 for x in D),'pivots':[fmt(x) for x in D],'minimum_absolute_pivot':fmt(min(abs(x) for x in D)),'LDL_residual':fmt(residual),'matrix_norm':fmt(mp.norm(A)),'seconds':time.monotonic()-start}
 (OUT/'matrix_cells'/f'dh_inertia_m{m}_dps{dps}_gl{order}.json').write_text(json.dumps(out,indent=2)+'\n');print('INERTIA',m,dps,out['negative_pivots'],out['seconds'],flush=True)
 return out

def finalize():
 mp.mp.dps=160
 path=OUT/'spectrum.csv';rows=list(csv.DictReader(path.open()));validation=[]
 for row in rows:
  m=int(row['m']);available=[]
  for p in (OUT/'matrix_cells').glob(f'dh_m{m}_dps*_gl*.json'):
   z=json.loads(p.read_text());available.append(z)
  preferred=max(available,key=lambda z:z['dps']) if available else None
  row['preferred_minimum_lambda']=preferred['minimum_lambda'] if preferred else row['float_lambda_min']
  row['preferred_precision']=preferred['dps'] if preferred else 'float64'
  row['mp_negative_count']=preferred['negative_count'] if preferred else ''
  row['mp_negative_count_precision_stable']=(len({a['negative_count'] for a in available})==1) if len(available)>1 else ''
  ip=OUT/'matrix_cells'/f'dh_inertia_m{m}_dps160_gl128.json'
  row['inertia160_negative_count']=json.loads(ip.read_text())['negative_pivots'] if ip.exists() else ''
  row['sign_evidence']='mp_spectrum' if preferred else ('resolved_negative_float_diagnostic' if row['resolved_negative_heuristic']=='True' else 'unresolved_float_sign')
  if len(available)>1:
   low=min(available,key=lambda z:z['dps']);high=max(available,key=lambda z:z['dps']);a=mp.mpf(low['minimum_lambda']);b=mp.mpf(high['minimum_lambda']);D=mp.matrix(low['A'])-mp.matrix(high['A'])
   validation.append({'m':m,'low_dps':low['dps'],'high_dps':high['dps'],'minimum_lambda_low':low['minimum_lambda'],'minimum_lambda_high':high['minimum_lambda'],'minimum_lambda_relative_change':mp.nstr(abs(a-b)/abs(b),100),'max_matrix_entry_difference':mp.nstr(max(abs(x) for x in D),100),'negative_counts_match':low['negative_count']==high['negative_count']})
 with path.open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 (OUT/'matrix_cells'/'dh_validation.json').write_text(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','comparisons':validation,'first_requested_range_negative':next(int(r['m']) for r in rows if int(r['m'])>=20 and mp.mpf(r['preferred_minimum_lambda'])<0 and r['sign_evidence']!='unresolved_float_sign')},indent=2)+'\n')
 print('finalized',len(validation),flush=True)

if __name__=='__main__':
 if sys.argv[1]=='float':float_scan()
 elif sys.argv[1]=='finalize':finalize()
 elif sys.argv[1]=='inertia':run_inertia(*map(int,sys.argv[2:]))
 else:run_mp(*map(int,sys.argv[1:]))
