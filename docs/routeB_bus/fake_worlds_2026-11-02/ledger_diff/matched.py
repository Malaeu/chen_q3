"""DIAGNOSTIC_NEVER_A_PROOF: matched real-constraint cardinalities and complement minima."""
from pathlib import Path
import sys,json,csv,hashlib,time
import mpmath as mp
OUT=Path(__file__).resolve().parent;FAKE=OUT.parent;BASE=FAKE.parent;CELLS=OUT/'matched_cells'
sys.path.insert(0,str(FAKE));sys.path.insert(0,str(BASE/'capacity_matrix_2026-11-02'));sys.path.insert(0,str(BASE/'phase_space_V'))
from dh_quiet import rows as dh_rows
from capacity import Erow
from v_forms import mangoldt
ZPATH=BASE/'capacity_matrix_2026-11-02/zeros.csv';DPATH=FAKE/'dh_zeros.json'
TARGETS={20:8,40:18,55:27,60:29,80:41,120:64}

def serial(x):
 if isinstance(x,mp.matrix):return [[mp.nstr(x[i,j],120) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,mp.mpf):return mp.nstr(x,120)
 if isinstance(x,list):return [serial(y) for y in x]
 if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
 return x

def build_zeta(m,dps=120,order=128):
 mp.mp.dps=dps;L=mp.log(m);d=m+1;gn,gw=mp.gauss_quadrature(order,'legendre')
 nodes=[((mp.mpf(p)+(x+1)/2)/8,w/16) for p in range(8) for x,w in zip(gn,gw)]
 sm=[mp.mpf(0)]*d;di=[mp.mpf(0)]*d;ps=[mp.mpf(0)]*d;pd=[mp.mpf(0)]*d
 for y,w in nodes:
  x=L*y;wt=L*w*mp.exp(-x/2)/(-mp.expm1(-2*x));co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(d):
   sm[n]+=wt*sn;di[n]+=wt*(2*y+2*(1-y)*(1-cn)+(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 for k in range(2,m):
  vm=mangoldt(k)
  if not vm:continue
  y=mp.log(k)/L;wt=vm/mp.sqrt(k);co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(d):
   ps[n]+=wt*sn;pd[n]+=wt*(2*(1-y)*cn-(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;beta=[sm[i]+ps[i] for i in range(d)];c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2;a=mp.exp(-L/2);tail=mp.atanh(a)+mp.atan(a);A=mp.zeros(d)
 pole=mp.matrix([4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(d)])
 for i in range(d):
  A[i,i]=c+di[i]+2*tail-pd[i]
  for j in range(i+1,d):A[i,j]=A[j,i]=ds[i]*ds[j]/mp.pi*(i*beta[i]-j*beta[j])/(i*i-j*j)
 return A+pole*pole.T

def load_source(world,m,dps=120):
 mp.mp.dps=dps;cache=CELLS/f'source_{world}_m{m}.json'
 if cache.exists():
  z=json.loads(cache.read_text());return mp.matrix(z['A']),list(map(mp.mpf,z['full_eigenvalues'])),z['provenance']
 path=None
 if world=='dh':path=FAKE/'matrix_cells'/f'dh_m{m}_dps120_gl128.json'
 elif m==20:path=BASE/'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local/core_m20_dps180_gl160.json'
 elif m==40:path=BASE/'cluster_count_2026-11-02/level_zero_ladder/cell_m40_dps180_gl160.json'
 if path:
  s=json.loads(path.read_text());A=mp.matrix(s['A']);ev=list(map(mp.mpf,s['lambda_']));prov={'source':str(path.relative_to(BASE)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'source_dps':s['dps']}
 else:
  A=build_zeta(m,dps,128);ev=list(mp.eigsy(A,eigvals_only=True));prov={'source':'fresh literal zeta jump form, all Mangoldt powers, original pole','source_dps':dps,'order':128,'implementation_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 cache.write_text(json.dumps(serial({'status':'DIAGNOSTIC_NEVER_A_PROOF','world':world,'m':m,'A':A,'full_eigenvalues':ev,'provenance':prov}),indent=2)+'\n')
 return A,ev,prov

def constraints(world,m,q):
 L=mp.log(m);Omega=2*mp.pi*m/L;baseline=mp.mpf('1.1')*Omega
 if world=='zeta':
  zeros=[mp.mpf(r['gamma']) for r in csv.DictReader(ZPATH.open())];baselineq=sum(g<baseline for g in zeros);assert baselineq==TARGETS[m]
  T=baseline if q==baselineq else (zeros[q-1]+zeros[q])/2
  return mp.matrix([Erow(g,m) for g in zeros[:q]]),[1]*q,[{'gamma':str(g),'kind':'line'} for g in zeros[:q]],T,baselineq,'zeta_kappa_1p1_baseline' if q==baselineq else 'additional_adjacent_cardinality_bracket'
 z=json.loads(DPATH.read_text());events=sorted([(mp.mpf(a['gamma']),1) for a in z['critical_line_zeros']]+[(mp.mpf(a['gamma']),2) for a in z['off_line_pairs']]);count=0
 for i,(g,n) in enumerate(events[:-1]):
  count+=n
  if count==q:
   T=(g+events[i+1][0])/2;E,signs,labels=dh_rows(z,m,T);assert E.rows==q
   return E,signs,labels,T,TARGETS[m],'matched_midpoint' if q==TARGETS[m] else 'DH_adjacent_cardinality_bracket_exact_q64_impossible'
 raise ValueError(f'no DH height cutoff realizes q={q}')

def run(world,m,q):
 mp.mp.dps=120;start=time.monotonic();A,ae,prov=load_source(world,m);E,signs,labels,T,qbase,branch=constraints(world,m,q);d=m+1
 left,s,right=mp.svd_r(E,full_matrices=True);rank=min(q,d);assert all(x>0 for x in s);U=right[:rank,:].T;Q=right[rank:,:].T;r=d-rank
 AQ=A*Q;de=mp.eigsy(AQ.T*AQ,eigvals_only=True);delta=mp.sqrt(max(mp.mpf(0),de[len(de)-1])) if r else mp.mpf(0)
 C=U.T*A*U;ce,Y=mp.eigsy(C);y=Y[:,0];f=U*y;pivot=max(range(d),key=lambda i:abs(f[i]))
 if f[pivot]<0:f=-f;y=-y
 mu=delta*mp.mpf('1.000001');count=sum(v<mu for v in ae);svres=mp.norm(E-left[:,:rank]*mp.diag(s)*right[:rank,:])
 data={'status':'DIAGNOSTIC_NEVER_A_PROOF','source_base':'d268313','world':world,'m':m,'N':m,'dps':120,'q':q,'rank':rank,'dim_J':r,'baseline_zeta_q':qbase,'branch':branch,'cutoff_mode':'matched','T':T,'effective_kappa':T/(2*mp.pi*m/mp.log(m)),'A':A,'full_eigenvalues':ae,'E':E,'row_signs':signs,'row_labels':labels,'U':U,'Q':Q,'singular_values':list(s),'sigma_min':s[rank-1],'sigma_min_squared':s[rank-1]**2,'twice_sigma_squared':2*s[rank-1]**2,'delta':delta,'adaptive_mu':mu,'count_delta_plus':count,'count_minus_dim':count-r,'lambda_r':ae[r],'complement_eigenvalues':list(ce),'complement_minimum':ce[0],'complement_y':list(y),'complement_f':list(f),'complement_rayleigh':mp.fdot(f,A*f),'complement_norm':mp.norm(f),'complement_eigen_residual':mp.norm(C*y-ce[0]*y),'SVD_residual':svres,'sigma_over_SVD_residual':s[rank-1]/svres if svres else None,'E_Q_residual':mp.norm(E*Q),'Q_orthogonality_residual':mp.norm(Q.T*Q-mp.eye(r)),'U_orthogonality_residual':mp.norm(U.T*U-mp.eye(rank)),'U_Q_residual':mp.norm(U.T*Q),'source_provenance':prov,'zero_source_sha256':hashlib.sha256((ZPATH if world=='zeta' else DPATH).read_bytes()).hexdigest(),'full_spectrum_tiny_signs_not_certified':True,'seconds':time.monotonic()-start}
 p=CELLS/f'{world}_m{m}_q{q}.json';p.write_text(json.dumps(serial(data),indent=2)+'\n');print('MATCHED',world,m,q,'delta',mp.nstr(delta,10),'complement',mp.nstr(ce[0],10),flush=True)
 return data

def run_native_dh(m):
 mp.mp.dps=120;start=time.monotonic();A,ae,prov=load_source('dh',m);T=mp.mpf('1.1')*2*mp.pi*m/mp.log(m);z=json.loads(DPATH.read_text());E,signs,labels=dh_rows(z,m,T);q=E.rows;d=m+1;r=d-q
 prior=FAKE/f'quiet_m{m}_k11.json'
 if prior.exists():
  old=json.loads(prior.read_text());cache=old['cache'][str(q)];Qold=mp.matrix(cache['Q']);orth,R=mp.qr(Qold);Q=orth[:,:r];U=orth[:,r:];ss=list(map(mp.mpf,cache['singular_values']));svres=mp.mpf(cache['SVD_residual']);kernel_method='saved native Q, reorthogonalized by full QR; complement from remaining QR columns';kernel_prov={'source':prior.name,'sha256':hashlib.sha256(prior.read_bytes()).hexdigest(),'source_dps':old['dps']}
 else:
  left,ss,right=mp.svd_r(E,full_matrices=True);Q=right[q:,:].T;U=right[:q,:].T;svres=mp.norm(E-left*mp.diag(ss)*right[:q,:]);kernel_method='fresh raw E SVD';kernel_prov={'source':DPATH.name,'sha256':hashlib.sha256(DPATH.read_bytes()).hexdigest()}
 AQ=A*Q;de=mp.eigsy(AQ.T*AQ,eigvals_only=True);delta=mp.sqrt(max(mp.mpf(0),de[len(de)-1]));C=U.T*A*U;ce,Y=mp.eigsy(C);y=Y[:,0];f=U*y;pivot=max(range(d),key=lambda i:abs(f[i]))
 if f[pivot]<0:f=-f;y=-y
 mu=delta*mp.mpf('1.000001');count=sum(v<mu for v in ae)
 data={'status':'DIAGNOSTIC_NEVER_A_PROOF','source_base':'d268313','world':'dh','m':m,'N':m,'dps':120,'q':q,'rank':q,'dim_J':r,'baseline_zeta_q':TARGETS[m],'branch':'DH_native_kappa1p1_additional_ledger_only','cutoff_mode':'native_kappa1p1','T':T,'effective_kappa':mp.mpf('1.1'),'A':A,'full_eigenvalues':ae,'E':E,'row_signs':signs,'row_labels':labels,'U':U,'Q':Q,'singular_values':list(ss),'sigma_min':ss[q-1],'sigma_min_squared':ss[q-1]**2,'twice_sigma_squared':2*ss[q-1]**2,'delta':delta,'adaptive_mu':mu,'count_delta_plus':count,'count_minus_dim':count-r,'lambda_r':ae[r],'complement_eigenvalues':list(ce),'complement_minimum':ce[0],'complement_y':list(y),'complement_f':list(f),'complement_rayleigh':mp.fdot(f,A*f),'complement_norm':mp.norm(f),'complement_eigen_residual':mp.norm(C*y-ce[0]*y),'SVD_residual':svres,'sigma_over_SVD_residual':ss[q-1]/svres if svres else None,'E_Q_residual':mp.norm(E*Q),'Q_orthogonality_residual':mp.norm(Q.T*Q-mp.eye(r)),'U_orthogonality_residual':mp.norm(U.T*U-mp.eye(q)),'U_Q_residual':mp.norm(U.T*Q),'source_provenance':prov,'kernel_method':kernel_method,'kernel_source_provenance':kernel_prov,'zero_source_sha256':hashlib.sha256(DPATH.read_bytes()).hexdigest(),'full_spectrum_tiny_signs_not_certified':True,'seconds':time.monotonic()-start}
 p=CELLS/f'dh_m{m}_q{q}_native.json';p.write_text(json.dumps(serial(data),indent=2)+'\n');print('NATIVE',m,q,'complement',mp.nstr(ce[0],14),flush=True);return data

def aggregate():
 rows=[]
 for p in sorted(CELLS.glob('*_m*_q*.json')):
  if p.name.endswith('_native.json'):continue
  d=json.loads(p.read_text());keys=['world','m','N','q','rank','dim_J','baseline_zeta_q','branch','T','effective_kappa','sigma_min','sigma_min_squared','twice_sigma_squared','delta','adaptive_mu','count_delta_plus','count_minus_dim','lambda_r','complement_minimum','complement_rayleigh','complement_norm','SVD_residual','E_Q_residual','seconds'];rows.append({k:d[k] for k in keys}|{'cutoff_mode':d.get('cutoff_mode','matched'),'scope':'additional_m55_for_PartB' if d['m']==55 else 'PartA'})
 with (OUT/'matched.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
if __name__=='__main__':
 if sys.argv[1]=='aggregate':aggregate()
 elif sys.argv[1]=='native':run_native_dh(int(sys.argv[2]))
 else:run(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]))
