"""DIAGNOSTIC_NEVER_A_PROOF: direct-SVD quiet kernels, literal even carriers."""
from pathlib import Path
import sys,json,csv,hashlib,time
import mpmath as mp
OUT=Path(__file__).resolve().parent;BASE=OUT.parent
sys.path.insert(0,str(BASE/'capacity_matrix_2026-11-02'))
from capacity import Erow
SOURCES={16:'cell_m16_dps180_gl160.json',24:'cell_m24_dps180_gl160.json',32:'cell_m32_dps160_gl128.json',40:'cell_m40_dps180_gl160.json'}
ZERO=BASE/'capacity_matrix_2026-11-02/zeros.csv'

def ser(x):
 if isinstance(x,mp.matrix):return [[mp.nstr(x[i,j],195) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,mp.mpf):return mp.nstr(x,195)
 if isinstance(x,dict):return {k:ser(v) for k,v in x.items()}
 if isinstance(x,list):return [ser(v) for v in x]
 return x

def compute(m):
 start=time.monotonic();mp.mp.dps=200
 path=BASE/'cluster_count_2026-11-02/level_zero_ladder'/SOURCES[m]
 source=json.loads(path.read_text());A=mp.matrix(source['A']);ae=list(map(mp.mpf,source['lambda_']));d=m+1;L=mp.log(m);omega=2*mp.pi*m/L
 zeros=[mp.mpf(r['gamma']) for r in csv.DictReader(ZERO.open())]
 samples=[(j,1+mp.mpf(j)/50) for j in range(21)]
 qs=sorted({sum(g<k*omega for g in zeros) for j,k in samples});cache={}
 for q in qs:
  E=mp.matrix([Erow(g,m) for g in zeros[:q]]);norms=[mp.norm(E[i,:]) for i in range(q)];R=mp.matrix([[E[i,j]/norms[i] for j in range(d)] for i in range(q)])
  U,s,Vt=mp.svd_r(R,full_matrices=True)
  assert len(s)==q and all(x>0 for x in s),'SVD rank not resolved'
  Q=Vt[q:,:].T;AQ=A*Q;compressed=Q.T*AQ
  de=mp.eigsy(AQ.T*AQ,eigvals_only=True);be=mp.eigsy(compressed,eigvals_only=True)
  delta=mp.sqrt(max(mp.mpf(0),de[len(de)-1]));beta=max(abs(x) for x in be)
  svres=mp.norm(R-U*mp.diag(s)*Vt[:q,:]);orth=mp.norm(Q.T*Q-mp.eye(d-q))
  cache[str(q)]={'q':q,'rank':q,'dimension':d-q,'rank_method':'full row-scaled SVD; all computed row singular values positive, no cutoff or truncation','Q':Q,'row_norms':norms,'row_scaled_singular_values':list(s),'row_scaled_condition':s[0]/s[len(s)-1],'row_scaled_sigma_min':s[len(s)-1],'SVD_residual':svres,'sigma_min_over_SVD_residual':s[len(s)-1]/svres if svres else None,'Q_orthogonality_residual':orth,'raw_E_Q_residual':mp.norm(E*Q),'row_scaled_E_Q_residual':mp.norm(R*Q),'delta':delta,'beta':beta,'compressed_eigenvalues':list(be),'last_included_zero':zeros[q-1],'first_excluded_zero':zeros[q]}
  print('quiet',m,q,'delta',mp.nstr(delta,10),flush=True)
 rows=[]
 for j,k in samples:
  T=k*omega;q=sum(g<T for g in zeros);c=cache[str(q)];dim=d-q;asym=m*(1-k+k*(1+mp.log(L)-mp.log(k))/L)
  r={'m':m,'N':m,'j':j,'kappa':k,'L':L,'Omega':omega,'T':T,'positive_zero_count_strict':q,'rank':c['rank'],'dimension':dim,'exact_dimension_d_minus_zero_count':d-q,'asymptotic_dimension':asym,'dimension_minus_asymptotic':dim-asym,'delta':c['delta'],'beta':c['beta'],'row_scaled_condition':c['row_scaled_condition'],'nearest_zero_distance':min(abs(g-T) for g in zeros)}
  for B in (2,4):
   mu=mp.mpf(m)**(-B);count=sum(x<mu for x in ae);r.update({f'mu_B{B}':mu,f'signed_count_B{B}':count,f'count_minus_dimension_B{B}':count-dim,f'delta_lt_mu_B{B}':c['delta']<mu,f'count_equals_dimension_B{B}':count==dim,f'delta_minus_mu_B{B}':c['delta']-mu})
  rows.append(r)
 result={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':m,'N':m,'dimension':d,'working_dps':200,'source_dps':source['dps'],'source_order':source['order'],'source_sha256':{str(path.relative_to(BASE)):hashlib.sha256(path.read_bytes()).hexdigest(),'zeros.csv':hashlib.sha256(ZERO.read_bytes()).hexdigest(),'capacity.py':hashlib.sha256((BASE/'capacity_matrix_2026-11-02/capacity.py').read_bytes()).hexdigest()},'basis':'literal even basis n=0..m includes constant mode; E is positive-zero physical Fourier sampling','A_eigenvalues':ae,'cache':cache,'rows':rows,'seconds':time.monotonic()-start}
 (OUT/f'cell_m{m}.json').write_text(json.dumps(ser(result),indent=2)+'\n');print('complete',m,flush=True)

def aggregate():
 rows=[]
 for m in (16,24,32,40):rows.extend(json.loads((OUT/f'cell_m{m}.json').read_text())['rows'])
 with (OUT/'scan.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
if __name__=='__main__':
 if sys.argv[1]=='aggregate':aggregate()
 else:compute(int(sys.argv[1]))
