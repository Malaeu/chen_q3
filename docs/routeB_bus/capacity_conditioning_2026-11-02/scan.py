"""DIAGNOSTIC_NEVER_A_PROOF: raw positive-zero capacity conditioning."""
from pathlib import Path
import sys,json,csv,time,hashlib
import mpmath as mp
OUT=Path(__file__).resolve().parent;BASE=OUT.parent
sys.path.insert(0,str(BASE/'phase_space_V'))
sys.path.insert(0,str(BASE/'capacity_matrix_2026-11-02'))
from v_forms import build_forms
from capacity import Erow
ZERO=BASE/'capacity_matrix_2026-11-02/zeros.csv'

def serial(x,dps):
 if isinstance(x,mp.matrix):return [[mp.nstr(x[i,j],dps) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,mp.mpf):return mp.nstr(x,dps)
 if isinstance(x,list):return [serial(v,dps) for v in x]
 if isinstance(x,dict):return {k:serial(v,dps) for k,v in x.items()}
 return x

def run(m,dps=100,order=128):
 start=time.monotonic();mp.mp.dps=dps;L=mp.log(m);dim=m+1;Omega=2*mp.pi*m/L
 zeros=[mp.mpf(r['gamma']) for r in csv.DictReader(ZERO.open())]
 kappas=[1+mp.mpf(j)/50 for j in range(21)];qmap={}
 for k in kappas:qmap.setdefault(sum(g<k*Omega for g in zeros),[]).append(k)
 for q in range(min(qmap),max(qmap)+1):qmap.setdefault(q,[])
 quiet_path=BASE/f'quiet_space_kappa_2026-11-02/cell_m{m}.json';quiet=None;provenance={}
 if m in (16,24,32,40) and quiet_path.exists():
  quiet=json.loads(quiet_path.read_text());ae=list(map(mp.mpf,quiet['A_eigenvalues']));A=None
  provenance[str(quiet_path.relative_to(BASE))]=hashlib.sha256(quiet_path.read_bytes()).hexdigest()
 elif m==20:
  p=BASE/'lowcluster_2026-11-02/core_m20_dps100_gl128.json';saved=json.loads(p.read_text());A=mp.matrix(saved['A']);ae=list(map(mp.mpf,saved['lambda_']));provenance[str(p.relative_to(BASE))]=hashlib.sha256(p.read_bytes()).hexdigest()
 else:
  forms=build_forms(m,m,dps,order);A=forms['K'];ae=list(mp.eigsy(A,eigvals_only=True));p=BASE/'phase_space_V/v_forms.py';provenance[str(p.relative_to(BASE))]=hashlib.sha256(p.read_bytes()).hexdigest()
  old=BASE/f'cluster_count_2026-11-02/spectra_m{m}_dps100_gl128.json'
  if old.exists():
   oldev=list(map(mp.mpf,json.loads(old.read_text())['lambda']));provenance['previous_spectrum_max_absolute_difference']=mp.nstr(max(abs(a-b) for a,b in zip(ae,oldev)),dps)
 passing=[];all_sectors=[]
 for q,ks in sorted(qmap.items()):
  E=mp.matrix([Erow(g,m) for g in zeros[:q]]);left,s,right=mp.svd_r(E,full_matrices=True);r=dim-q
  assert len(s)==q and all(x>0 for x in s),'raw row rank unresolved'
  Q=right[q:,:].T
  if quiet is not None:delta=mp.mpf(quiet['cache'][str(q)]['delta'])
  else:
   ev=mp.eigsy((A*Q).T*(A*Q),eigvals_only=True);delta=mp.sqrt(max(mp.mpf(0),ev[len(ev)-1]))
  mu=delta*mp.mpf('1.000001');count=sum(x<mu for x in ae);saturates=count==r
  common={'m':m,'q':q,'r':r,'kappas':ks,'continuous_kappa_left':max(mp.mpf(1),zeros[q-1]/Omega),'continuous_left_included':zeros[q-1]<Omega,'continuous_kappa_right':min(mp.mpf('1.4'),zeros[q]/Omega),'continuous_right_included':True,'delta':delta,'adaptive_mu':mu,'signed_count':count,'count_minus_r':count-r,'saturates':saturates,'lambda_r':ae[r],'lambda_r_over_delta':ae[r]/delta,'lambda_r_minus_delta':ae[r]-delta,'lambda_r_minus_mu':ae[r]-mu,'minimum_raw_singular_value':s[q-1],'raw_condition':s[0]/s[q-1]}
  all_sectors.append(common)
  if not saturates:continue
  U=right[:q,:].T;F=E*U;weak=left[:,q-1];weakright=right[q-1,:].T
  pivot=max(range(q),key=lambda i:abs(weak[i]))
  if weak[pivot]<0:weak=-weak;weakright=-weakright
  mass=[abs(x)**2 for x in weak];pair=max(range(q-1),key=lambda i:mass[i]+mass[i+1]);gaps=[]
  for i in range(q):
   prev=zeros[i]-zeros[i-1] if i else None;nextgap=zeros[i+1]-zeros[i];gap=min(prev,nextgap) if prev is not None else nextgap
   gaps.append({'zero_index':i+1,'gamma':zeros[i],'previous_gap':prev,'next_gap':nextgap,'nearest_gap':gap,'normalized_nearest_gap':gap*L/(2*mp.pi),'normalized_gap_below_0p3':gap*L/(2*mp.pi)<mp.mpf('.3'),'weak_left_entry':weak[i],'weak_left_mass':mass[i]})
  ss=s[q-1]**2
  detail={**common,'row_norms':[mp.norm(E[i,:]) for i in range(q)],'adjacent_pair_row_normalized_correlation':abs(mp.fdot(E[pair,:],E[pair+1,:]))/(mp.norm(E[pair,:])*mp.norm(E[pair+1,:])),'raw_singular_values':list(s),'sigma_min_squared':ss,'twice_sigma_min_squared':2*ss,'twice_sigma_min_squared_over_lambda_r':2*ss/ae[r],'U_rowspace_basis':U,'F':F,'weak_left_vector':list(weak),'weak_right_vector':list(weakright),'top_adjacent_pair_indices':[pair+1,pair+2],'top_two_mass_indices':[i+1 for i in sorted(range(q),key=lambda i:mass[i],reverse=True)[:2]],'top_two_mass':sum(sorted(mass,reverse=True)[:2]),'top_adjacent_pair_signed_component_product':weak[pair]*weak[pair+1],'top_adjacent_pair_mass':mass[pair]+mass[pair+1],'top_adjacent_pair_gap':zeros[pair+1]-zeros[pair],'top_adjacent_pair_normalized_gap':(zeros[pair+1]-zeros[pair])*L/(2*mp.pi),'local_zero_gaps':gaps,'raw_E_kernel_residual':mp.norm(E*Q),'Q_orthogonality_residual':mp.norm(Q.T*Q-mp.eye(r)),'raw_SVD_residual':mp.norm(E-left*mp.diag(s)*right[:q,:])}
  passing.append(detail);print('passing',m,q,'ratio',mp.nstr(2*ss/ae[r],10),'pairmass',mp.nstr(mass[pair]+mass[pair+1],8),flush=True)
 result={'status':'DIAGNOSTIC_NEVER_A_PROOF','context_commit':'e724ae65','m':m,'N':m,'dps':dps,'order':order,'L':L,'Omega':Omega,'A_eigenvalues':ae,'matrix_mode':'saved quiet-space source and deltas' if quiet else ('saved core A and raw-SVD quiet kernel' if m==20 else 'fresh literal matrix and raw-SVD quiet kernel'),'normalization':'E is unweighted physical Fourier samples at positive zeros, no row normalization in conditioning calculation; F=E U','source_provenance':provenance,'zeros_sha256':hashlib.sha256(ZERO.read_bytes()).hexdigest(),'all_sectors':all_sectors,'passing_sectors':passing,'seconds':time.monotonic()-start}
 p=OUT/f'cell_m{m}_dps{dps}_gl{order}.json';p.write_text(json.dumps(serial(result,dps),indent=2)+'\n');print('COMPLETE',m,result['seconds'],flush=True);return result

def enrich_existing():
 for m in range(16,41):
  path=OUT/f'cell_m{m}_dps100_gl128.json';data=json.loads(path.read_text());mp.mp.dps=data['dps'];L=mp.log(m);Omega=2*mp.pi*m/L
  zeros=[mp.mpf(r['gamma']) for r in csv.DictReader(ZERO.open())];fmt=lambda x:mp.nstr(x,data['dps'])
  qlist=[r['q'] for r in data['all_sectors']];data['all_continuous_zero_count_sectors_covered']=qlist==list(range(min(qlist),max(qlist)+1))
  for row in data['all_sectors']+data['passing_sectors']:
   q=row['q'];row.update(continuous_kappa_left=fmt(max(mp.mpf(1),zeros[q-1]/Omega)),continuous_left_included=bool(zeros[q-1]<Omega),continuous_kappa_right=fmt(min(mp.mpf('1.4'),zeros[q]/Omega)),continuous_right_included=True)
  for row in data['passing_sectors']:
   q=row['q'];E=mp.matrix([Erow(g,m) for g in zeros[:q]]);norms=[mp.norm(E[i,:]) for i in range(q)];i=row['top_adjacent_pair_indices'][0]-1
   row['row_norms']=[fmt(x) for x in norms];row['adjacent_pair_row_normalized_correlation']=fmt(abs(mp.fdot(E[i,:],E[i+1,:]))/(norms[i]*norms[i+1]))
  if m==20:data['matrix_mode']='saved core A and raw-SVD quiet kernel'
  path.write_text(json.dumps(data,indent=2)+'\n')

def aggregate():
 rows=[];gaps=[];allrows=[];grid=[]
 for m in range(16,41):
  p=OUT/f'cell_m{m}_dps100_gl128.json';d=json.loads(p.read_text())
  for r in d['all_sectors']:
   allrows.append({k:v for k,v in r.items() if k!='kappas'}|{'kappas':','.join(r['kappas'])})
   for k in r['kappas']:grid.append({key:v for key,v in r.items() if key!='kappas'}|{'kappa':k})
  for r in d['passing_sectors']:
   drop={'U_rowspace_basis','F','weak_left_vector','weak_right_vector','local_zero_gaps','raw_singular_values','row_norms'}
   row={k:v for k,v in r.items() if k not in drop};row['kappas']=','.join(row['kappas']);row['top_adjacent_pair_indices']=','.join(map(str,row['top_adjacent_pair_indices']));rows.append(row)
   for g in r['local_zero_gaps']:gaps.append({'m':m,'q':r['q'],**g})
 for name,data in [('sectors.csv',allrows),('cases.csv',rows),('grid.csv',grid),('local_gaps.csv',gaps)]:
  with (OUT/name).open('w',newline='') as f:
   w=csv.DictWriter(f,fieldnames=data[0]);w.writeheader();w.writerows(data)
if __name__=='__main__':
 if sys.argv[1]=='aggregate':enrich_existing();aggregate()
 else:run(*map(int,sys.argv[1:]))
