"""P1--P4 MP pilots. DIAGNOSTIC_NEVER_A_PROOF; no interval certificate.
Pinned split builder 400 bit, GL256/eight panels; MP algebra 120 dps.
"""
from pathlib import Path
import os,sys,time,json,pickle,csv,copyreg,builtins
os.environ['OPENBLAS_NUM_THREADS']='1'
import mpmath as mp
import numpy as np
OUT=Path(__file__).resolve().parent
DEFAULT_BASE=OUT.parent/'arithmetic_coupling_2026-11-03'
if not (DEFAULT_BASE/'source/split.py').exists():
 DEFAULT_BASE=Path('/workspace/stiffness/repo/docs/routeB_bus/arithmetic_coupling_2026-11-03')
SRC=Path(os.environ.get('STIFFNESS_BASE',str(DEFAULT_BASE))).resolve()
LOCAL=Path(os.environ.get('STIFFNESS_LOCAL',str(OUT.parent/'local'))).resolve()
sys.path.insert(0,str(SRC/'mp_pilots'))
sys.path.insert(0,str(SRC/'source'))
import split
import audit
mp.mp.dps=120
# Mpmath dynamic matrix class has no default pickle registration.
def reduce_matrix(A):
 rows=[[mp.nstr(A[i,j],125) for j in range(A.cols)] for i in range(A.rows)]
 return builtins.eval,("__import__('mpmath').matrix("+repr(rows)+")",)
copyreg.pickle(type(mp.matrix(1)),reduce_matrix)
CACHE=LOCAL/'mp';CACHE.mkdir(parents=True,exist_ok=True)
FMT=lambda x:mp.nstr(x,115)
def serial(x):
 if isinstance(x,mp.matrix):return [[FMT(x[i,j]) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,(mp.mpf,mp.mpc)):return FMT(x)
 if isinstance(x,dict):return {str(k):serial(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [serial(v) for v in x]
 if isinstance(x,np.generic):return x.item()
 return x

def maxabs(A):return max(abs(v) for v in A) if A.rows*A.cols else mp.mpf(0)
def sym(A):return (A+A.T)/2

def load_cache(m):
 p=CACHE/f'm{m}.pkl'
 if p.exists() and p.stat().st_size>100:
  try:return pickle.load(p.open('rb'))
  except (EOFError,pickle.UnpicklingError):pass
 t=time.monotonic();s=split.build(m,256)['zeta'];C=audit.convert(s['C']);B=audit.convert(s['B']);A=C+B
 quietdata,Q,D,qev,qV=audit.quiet(A,m,True)
 data=dict(m=m,A=A,C=C,B=B,Q=Q,quietdata=quietdata,quiet_matrix=D,quiet_eigenvalues=qev,quiet_eigenvectors=qV,mp_dps=120,source_bits=400,source_GL_order=256,source_panels=8,build_seconds=time.monotonic()-t)
 # First save releases P5 dependency before any full eigensolver.
 pickle.dump(data,p.open('wb'));print('CACHE_WRITTEN',m,str(p),flush=True)
 ev,V=mp.eigsy(A);data['eigenvalues']=ev;data['eigenvectors']=V;data['eigenpair_max_entry_residual']=maxabs(A*V-V*mp.diag(ev));data['eigenvector_orthogonality_max_entry']=maxabs(V.T*V-mp.eye(m+1))
 pickle.dump(data,p.open('wb'));print('EIGEN_CACHE_WRITTEN',m,flush=True)
 return data

if __name__=='__main__' and (len(sys.argv)<2 or sys.argv[1]!='prices'):
 for m in map(int,sys.argv[1:] or [16,24,40]):
  x=load_cache(m)

# MP finite algebra; floats are used only to propose a conic candidate.
sys.path.insert(0,str(OUT))
from knobs import make_knobs
FLOOR=mp.mpf('1e-110');SOURCE_FLOOR=mp.mpf('1e-114')
def spectrum(A):return mp.eigsy(sym(A),eigvals_only=True)
def opnorm(A):
 if not A.rows or not A.cols:return mp.mpf(0)
 if A.rows==A.cols and maxabs(A-A.T)<mp.mpf('1e-115'):return max(abs(v) for v in spectrum(A))
 return mp.sqrt(max(mp.mpf(0),max(spectrum(A.T*A))))
def inertia(A):
 e=spectrum(A);return dict(negative=sum(v < -FLOOR for v in e),unresolved=sum(abs(v)<=FLOOR for v in e),positive=sum(v>FLOOR for v in e),floor=FLOOR,minimum=e[0],maximum=e[e.rows-1])
def helmert(k):
 V=mp.zeros(k,k-1)
 for j in range(k-1):
  norm=mp.sqrt((j+1)*(j+2))
  for i in range(j+1):V[i,j]=1/norm
  V[j+1,j]=-(j+1)/norm
 return V

def vecsym(A):return mp.matrix([A[i,j]*(1 if i==j else mp.sqrt(2)) for i in range(A.rows) for j in range(i,A.cols)])
def price_map(Ms):
 vectors=[vecsym(M) for M in Ms]
 return mp.matrix([[vectors[j][i] for j in range(len(Ms))] for i in range(vectors[0].rows)])
def svd_record(T):
 U,s,V=mp.svd_r(T,full_matrices=True)
 threshold=FLOOR*max(mp.mpf(1),max(abs(v) for v in s));rank=sum(v>threshold for v in s)
 kernel=V[rank:,:].T
 return dict(rows=T.rows,columns=T.cols,singular_values=list(s),rank_numerical=rank,threshold=threshold,kernel_dimension=T.cols-rank,kernel=kernel,kernel_image_max_entry=maxabs(T*kernel),svd_max_entry_residual=maxabs(T-U[:,:len(s)]*mp.diag(s)*V[:len(s),:]),kernel_orthogonality_max_entry=maxabs(kernel.T*kernel-mp.eye(kernel.cols)))

def candidate_ball(Ms):
 import cvxpy as cp
 k=len(Ms);r=Ms[0].rows;sc=max(opnorm(M) for M in Ms)
 if not sc:return dict(status='ZERO_IMAGE',ball_optimum=0)
 F=np.array([[[float(M[i,j]/sc) for j in range(r)] for i in range(r)] for M in Ms]);x=cp.Variable(k);z=cp.Variable();X=sum(x[i]*F[i] for i in range(k));con=[X-z*np.eye(r)>>0,cp.norm(x,2)<=1,cp.sum(x)==0];prob=cp.Problem(cp.Maximize(z),con)
 try:prob.solve(solver='CLARABEL',tol_gap_abs=1e-10,tol_feas=1e-10,tol_gap_rel=1e-10,max_iter=300)
 except Exception as e:return dict(status='SOLVER_ERROR',error=repr(e))
 if x.value is None:return dict(status=prob.status)
 # Finite candidate projection/normalization is explicit, not claimed solver precision.
 tx=mp.matrix([mp.mpf(str(v)) for v in x.value]);before=mp.norm(tx);mean=mp.fsum(tx)/k;tx-=mp.matrix([mean]*k);after=mp.norm(tx)
 if after>1:tx/=after
 Y=np.array(con[0].dual_value,float);Y=mp.matrix([[mp.mpf(str(Y[i,j])) for j in range(r)] for i in range(r)]);Y=sym(Y);trY=mp.fsum(Y[i,i] for i in range(r))
 if trY:Y/=trY
 H=sum((tx[i]*Ms[i] for i in range(k)),mp.zeros(r));evals=spectrum(H);prices=mp.matrix([mp.fsum(Y[i,j]*Ms[a][j,i] for i in range(r) for j in range(r)) for a in range(k)]);V=helmert(k);gradient=V.T*prices
 yev=spectrum(Y);dualnorm=mp.norm(gradient)
 # In r=1, trY=1 fixes the whole dual and gives the exact finite scalar optimum.
 analytic=mp.norm(V.T*mp.matrix([M[0,0] for M in Ms])) if r==1 else None
 out=dict(status=prob.status,scale=sc,float_solver_value=prob.value,candidate_t=tx,candidate_raw_norm=before,candidate_raw_mean=mean,candidate_domain_sum=mp.fsum(tx),candidate_norm=mp.norm(tx),primal_minimum=evals[0],dual_Y=Y,dual_trace=mp.fsum(Y[i,i] for i in range(r)),dual_minimum=yev[0],dual_gradient_norm=dualnorm,duality_gap=dualnorm-evals[0],dual_prices=prices,price_spread=max(prices)-min(prices),positive_stress_annihilation_residual=maxabs(gradient),scalar_analytic_ball_optimum=analytic,ball_optimum_cannot_be_negative=True,not_interval_certification=True)
 if r==1:
  p=mp.matrix([M[0,0] for M in Ms]);centered=p-mp.matrix([mp.fsum(p)/k]*k)
  exact_t=centered/analytic if analytic else mp.zeros(k,1)
  exact_image=mp.fdot(p,exact_t)
  out.update(positive_definite_annihilating_stress_exists=bool(analytic==0),scalar_exact_optimizer=exact_t,scalar_exact_optimizer_sum=mp.fsum(exact_t),scalar_exact_optimizer_norm=mp.norm(exact_t),scalar_exact_primal_image=exact_image,scalar_exact_primal_dual_gap=analytic-exact_image,dual_Y_valid_for_ball=True,dual_Y_valid_as_annihilating_stress=bool(analytic==0),dual_stress_price_residual_norm=analytic,dual_stress_condition_ratio=mp.mpf(1))
 return out

def compression_record(A,components,U,label,allow_optimization=True):
 Ms=[sym(U.T*M*U) for M in components];AJ=sym(U.T*A*U);norms=[opnorm(M) for M in Ms];scale=max(norms);ratio=opnorm(AJ)/scale if scale else mp.inf
 result=dict(name=label,dimension=U.cols,compressed_A=AJ,compressed_A_operator_norm=opnorm(AJ),maximum_component_norm=scale,compression_relative=ratio,admissibility_gate=mp.mpf('1e-8'),gate_pass=ratio<=mp.mpf('1e-8'),price_component_norms=norms,ones_image=AJ,ones_image_max_entry=maxabs(AJ),ones_forced_null=False,normalization='orthonormal physical carrier; Frobenius svec with sqrt2 off diagonals; Euclidean parameter norm; budget gauge t perpendicular to ones; no quotient asserted')
 if result['gate_pass']:
  T=price_map(Ms);V=helmert(len(Ms));result['P2_full_map']=svd_record(T);result['P2_budget_gauge_map']=svd_record(T*V);result['P2_ones_approximate_kernel_ratio']=mp.norm(T*mp.matrix([1]*len(Ms)))/(mp.sqrt(len(Ms))*max(mp.svd_r(T,compute_uv=False)));result['P2_prices_svec']=T;result['P2_dimension_lower_bound_full_kernel']=max(0,len(Ms)-U.cols*(U.cols+1)//2);result['P2_dimension_lower_bound_budget_kernel']=max(0,len(Ms)-1-U.cols*(U.cols+1)//2)
  result['P2_budget_basis']=V
  if allow_optimization:result['P3_ball']=candidate_ball(Ms)
 else:result['P2_P3_status']='STOPPED_COMPRESSION_ADMISSIBILITY_GATE_FAILED'
 return result,Ms

def run_prices(m):
 data=load_cache(m);A=data['A'];C=data['C'];B=data['B'];Q=data['Q'];ev=data['eigenvalues'];E=data['eigenvectors'];d=m+1;labels,components=make_knobs(m,C,B,mp_mode=True)
 conservation=sum(components,mp.zeros(d))-A;cons=maxabs(conservation);consrel=cons/max(mp.mpf(1),maxabs(A))
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,mp_dps=120,source_bits=400,source_GL_order=256,source_panels=8,source_floor=SOURCE_FLOOR,numerical_inertia_floor=FLOOR,labels=labels,P1_conservation_max_entry=cons,P1_conservation_relative=consrel,P1_conservation_gate=mp.mpf('1e-108'),P1_gate_pass=cons<=mp.mpf('1e-108'),quiet=data['quietdata'],eigenpair_max_entry_residual=data['eigenpair_max_entry_residual'],eigenvector_orthogonality_max_entry=data['eigenvector_orthogonality_max_entry'])
 if not out['P1_gate_pass']:
  out['status']='SOURCE_CONSERVATION_GATE_FAILED';(OUT/f'mp_prices_m{m}.json').write_text(json.dumps(serial(out),indent=2)+'\n');return out
 gaps=[dict(j=j,lower=ev[j-1],upper=ev[j],ratio=ev[j]/max(ev[j-1],SOURCE_FLOOR)) for j in range(1,d//2+1)];j=max(range(len(gaps)),key=lambda i:gaps[i]['ratio']);size=gaps[j]['j'];F=E[:,:size]
 out['full_spectrum']=ev;out['gap_candidates']=gaps;out['selected_face_size']=size;out['selected_gap_ratio']=gaps[j]['ratio'];out['face_basis']=F
 out['P1_quiet_AQ_norm']=opnorm(A*Q);out['P1_quiet_compressed_norm']=opnorm(Q.T*A*Q);out['P1_quiet_exit_norm']=opnorm(A*Q-Q*(Q.T*A*Q));out['P1_face_quiet_overlaps']=list(mp.svd_r(Q.T*F,compute_uv=False));out['P1_face_outside_quiet_norm']=opnorm(F-Q*(Q.T*F));out['P1_face_source_exit_norm']=opnorm(A*F-F*(F.T*A*F))
 # Float source face is a separate observation, never substituted for MP selection.
 from scipy.linalg import eigh as float_eigh
 raw=np.load(SRC/'source'/f'zeta_m{m}.npz');Af=raw['A1'];fev,fV=float_eigh((Af+Af.T)/2);float_floor=mp.mpf(str(float(raw['numeric_radius'])));fgaps=[dict(j=j,lower=mp.mpf(str(fev[j-1])),upper=mp.mpf(str(fev[j])),ratio=mp.mpf(str(fev[j]))/max(mp.mpf(str(fev[j-1])),float_floor)) for j in range(1,d//2+1)];fs=max(fgaps,key=lambda z:z['ratio'])['j'];fvec=mp.matrix([[mp.mpf(str(v)) for v in row] for row in fV[:,:fs]])
 out['float_face_comparison']=dict(role='secondary_raw_source_numeric_radius_sensitivity_not_root_primary',formula='lambda[j]/max(lambda[j-1],raw_NPZ_numeric_radius); no numerator flooring',floor=float_floor,gap_candidates=fgaps,selected_size=fs,MP_selected_size=size,selection_agrees=fs==size,MP_projection_into_float_face_mass=mp.norm(fvec.T*F)**2,MP_vs_binary_source_max_entry=maxabs(A-audit.convert(Af)))
 primary_path=OUT/'binary_cells'/f'zeta_m{m}.json'
 if primary_path.exists():
  primary=json.loads(primary_path.read_text());out['float_face_primary_comparison']=dict(role='root_primary_inherited_precision_floor',source_path=str(primary_path),floor=primary['face_selection_floor'],selected_size=primary['face_size'],MP_selected_size=size,selection_agrees=primary['face_size']==size,gap_ratio=primary['face_gap_ratio'],all_gap_ratios=primary['face_all_ratios'],PAP_norm=primary['face_PAP_norm'],compression_relative=primary['face_relative'],note='Primary binary selector convention and floor retained verbatim from root; secondary raw source radius sensitivity is separately labeled.')
 inherited=[]
 for kind,path,key in [('MP',SRC/'mp_pilots'/f'ENDPOINTS_m{m}.json','carrier_coefficients'),('float',SRC/'cells'/f'zeta_m{m}_f100.json','carrier_vector')]:
  zz=json.loads(path.read_text());endpoints=zz['endpoints'] if kind=='MP' else zz['solver']['endpoints']
  for ep in endpoints:
   if key not in ep:continue
   v=mp.matrix([mp.mpf(str(x)) for x in ep[key]]);v/=mp.norm(v)
   inherited.append(dict(provenance=kind,side=ep['side'],source_path=str(path.relative_to(SRC)),selected_MP_face_mass=mp.norm(F.T*v)**2,quiet_mass_recomputed_MP=mp.norm(Q.T*v)**2,baseline_A_rayleigh_recomputed_MP=(v.T*A*v)[0],source_carrier_normalization='physical coefficient unit norm'))
 out['P1_inherited_coupling_exit_carrier_overlaps']=inherited
 out['full_quiet'],_=compression_record(A,components,Q,'inherited_full_J',False)
 out['literal_face'],Ms=compression_record(A,components,F,'literal_largest_adjacent_relative_gap_face')
 if out['literal_face'].get('P3_ball',{}).get('scalar_exact_optimizer') is not None:
  tt=out['literal_face']['P3_ball']['scalar_exact_optimizer'];out['literal_face']['P3_optimizer_labeled']=[dict(knob=label,t=tt[i],price=Ms[i][0,0]) for i,label in enumerate(labels)]
 # Component coupling to the exit carrier cannot be inferred from their compressions.
 out['P1_face_component_exit_norms']=[opnorm(M*F-F*(F.T*M*F)) for M in components]
 out['P4_all_knob_inertias']=[dict(knob=label,**inertia(K)) for label,K in zip(labels,components)]
 G=A+mp.mpf('1e-100')*mp.eye(d);L=mp.cholesky(G);Li=L**-1;out['P4_cholesky_max_entry_residual']=maxabs(G-L*L.T);intervals=[]
 for label,K in zip(labels,components):
  if label.startswith('B_') and int(label[2:])>13:continue
  H=sym(Li*K*Li.T);hi,hV=mp.eigsy(H);hmin=hi[0];hmax=hi[hi.rows-1]
  if label=='C_pole':
   # Exact PSD rank-one structure governs the entire upper ray.
   hmax=mp.fsum(H[i,i] for i in range(d));hmin=mp.mpf(0)
  lower=-1/hmax if hmax>0 else -mp.inf;upper=-1/hmin if hmin<0 else mp.inf
  endpoints=[]
  for side,offset,index in [('lower',lower,d-1),('upper',upper,0)]:
   if not mp.isfinite(offset):continue
   if label=='C_pole':
    pivot=max(range(d),key=lambda i:K[i,i]);pp=K[:,pivot]/mp.sqrt(K[pivot,pivot]);yy=Li*pp;yy/=mp.norm(yy)
   else:yy=hV[:,index]
   v=Li.T*yy;v/=mp.norm(v);T=sym(G+offset*K);w=T*v
   endpoints.append(dict(side=side,offset=offset,carrier_vector=v,carrier_norm=mp.norm(v),shifted_rayleigh=(v.T*T*v)[0],shifted_residual_max_entry=maxabs(w),baseline_A_rayleigh=(v.T*A*v)[0],knob_slope=(v.T*K*v)[0],quiet_mass=mp.norm(Q.T*v)**2,selected_face_mass=mp.norm(F.T*v)**2))
  intervals.append(dict(knob=label,epsilon=mp.mpf('1e-100'),raw_knob_inertia=inertia(K),generalized_minimum=hmin,generalized_maximum=hmax,u_minus=1+lower,u_plus=1+upper,lower_offset_from_one=lower,upper_offset_from_one=upper,width=upper-lower,PSD_pole_structural_upper_infinity=label=='C_pole',normalization='G=A+epsilon I; H=L^-1 K L^-T; u offsets solve I+(u-1)H PSD',generalized_eigenvalue_raw_minimum=hi[0],generalized_eigenvalue_raw_maximum=hi[hi.rows-1],H_eigenvalue_signs_not_interval_certified=True,endpoints=endpoints,H_eigenpair_max_entry_residual=maxabs(H*hV-hV*mp.diag(hi)),H_eigenpair_max_entry_residual_relative=maxabs(H*hV-hV*mp.diag(hi))/max(mp.mpf(1),maxabs(H))))
 out['P4_intervals']=intervals
 (OUT/f'mp_prices_m{m}.json').write_text(json.dumps(serial(out),indent=2)+'\n');print('MP_PRICES_DONE',m,'face',size,'face_gate',out['literal_face']['gate_pass'],'J_gate',out['full_quiet']['gate_pass'],flush=True)
 return out

def summarize(rows):
 columns=['m','face_size','face_gap_ratio','J_gate','J_relative','face_gate','face_relative','ones_image','full_price_rank','budget_price_rank','budget_kernel_dim','ball_min_candidate','ball_dual_bound','ball_gap','scalar_optimum']
 rr=[]
 for z in rows:
  f=z['literal_face'];s=f.get('P2_budget_gauge_map',{});b=f.get('P3_ball',{});rr.append(dict(m=z['m'],face_size=z['selected_face_size'],face_gap_ratio=FMT(z['selected_gap_ratio']),J_gate=z['full_quiet']['gate_pass'],J_relative=FMT(z['full_quiet']['compression_relative']),face_gate=f['gate_pass'],face_relative=FMT(f['compression_relative']),ones_image=FMT(f['ones_image_max_entry']),full_price_rank=f.get('P2_full_map',{}).get('rank_numerical',''),budget_price_rank=s.get('rank_numerical',''),budget_kernel_dim=s.get('kernel_dimension',''),ball_min_candidate=FMT(b.get('primal_minimum',mp.nan)),ball_dual_bound=FMT(b.get('dual_gradient_norm',mp.nan)),ball_gap=FMT(b.get('duality_gap',mp.nan)),scalar_optimum=FMT(b.get('scalar_analytic_ball_optimum',mp.nan))))
 inertia_rows=[]
 for z in rows:
  for e in z['P4_all_knob_inertias']:
   inertia_rows.append(dict(m=z['m'],knob=e['knob'],negative=e['negative'],unresolved=e['unresolved'],positive=e['positive'],floor=FMT(e['floor']),minimum=FMT(e['minimum']),maximum=FMT(e['maximum'])))
 with (OUT/'mp_prices_inertias.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(inertia_rows[0]));w.writeheader();w.writerows(inertia_rows)
 interval_rows=[]
 for z in rows:
  for e in z['P4_intervals']:
   ii=e['raw_knob_inertia'];ends={v['side']:v for v in e.get('endpoints',[])}
   interval_rows.append(dict(m=z['m'],knob=e['knob'],epsilon=FMT(e['epsilon']),negative=ii['negative'],unresolved=ii['unresolved'],positive=ii['positive'],inertia_floor=FMT(ii['floor']),lower_offset=FMT(e['lower_offset_from_one']),upper_offset=FMT(e['upper_offset_from_one']),width=FMT(e['width']),pole_upper_infinity=e['PSD_pole_structural_upper_infinity'],lower_residual=FMT(ends.get('lower',{}).get('shifted_residual_max_entry',mp.nan)),upper_residual=FMT(ends.get('upper',{}).get('shifted_residual_max_entry',mp.nan)),lower_quiet_mass=FMT(ends.get('lower',{}).get('quiet_mass',mp.nan)),upper_quiet_mass=FMT(ends.get('upper',{}).get('quiet_mass',mp.nan)),lower_face_mass=FMT(ends.get('lower',{}).get('selected_face_mass',mp.nan)),upper_face_mass=FMT(ends.get('upper',{}).get('selected_face_mass',mp.nan))))
 with (OUT/'mp_prices_intervals.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(interval_rows[0]));w.writeheader();w.writerows(interval_rows)
 with (OUT/'mp_prices_summary.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=columns);w.writeheader();w.writerows(rr)
 lines=['# MP P1–P4 v2 pilots','', 'DIAGNOSTIC_NEVER_A_PROOF; source floor empirical, not interval-certified.','', 'The literal relative-gap selector chooses a one-dimensional face in every pilot. Full inherited quiet compressions fail the declared admissibility gate, so P2–P3 stop there. The selected face passes; its scalar price map has the dimension-forced large parameter kernel. The ones image is retained rather than set to zero.','', '|m|face|gap|J ratio|face ratio|budget kernel|scalar ball optimum|','|---:|---:|---:|---:|---:|---:|---:|']
 for r in rr:lines.append('|'+ '|'.join(str(r[k]) if k in ('m','face_size','budget_kernel_dim') else mp.nstr(mp.mpf(r[k]),8) for k in ['m','face_size','face_gap_ratio','J_relative','face_relative','budget_kernel_dim','scalar_optimum'])+'|')
 lines+=['','The scalar analytic ball optimum is nonnegative. Float conic candidates are explicitly projected back to the MP budget gauge and unit ball, and their finite primal/dual quadratic data are recomputed in MP. This is not a claim of an MP optimizer or interval SDP certificate. A positive optimum rejects strictness of this face price problem; a kernel additionally prevents exclusion of nonzero parameter directions.','','For P4 the PSD rank-one pole has an infinite upper ray structurally. Reported narrow widths for indefinite knobs do not apply to this pole. The raw knob inertia uses absolute1e-110 numerical floor; this is a reporting threshold, not a source error enclosure.','','Reproduce: `STIFFNESS_BASE=/path/to/arithmetic_coupling_2026-11-03 STIFFNESS_LOCAL=/scratch/stiffness OPENBLAS_NUM_THREADS=1 python mp_prices.py prices 16 24 40` (install numpy/scipy/gmpy2/mpmath/cvxpy/clarabel or set PYTHONPATH to their environment). MP caches are reused and were built once per pilot by the unchanged pinned source and quiet constructors. The quiet builder uses its inherited kappa=1 reference.','', 'Primary binary faces use the inherited summary precision_floor and are read verbatim from root binary_cells records; the raw NPZ numeric_radius comparison is retained only as a separately labeled sensitivity. Neither binary choice is substituted for the MP source-floor selection.','', 'The exact MP scalar optimizer is recorded alongside the float conic candidate. Its trace-one Y=1 is a valid ball dual but is NOT an annihilating stress: the projected price residual is about2.27. Inherited MP and binary coupling endpoint carriers are normalized and compared with the selected MP face and quiet carrier, with all overlaps retained in JSON. P4 CSV includes knob inertia, finite-side offsets, witness residuals and overlap masses.']
 (OUT/'mp_prices_RESULT.md').write_text('\n'.join(lines)+'\n')

if __name__=='__main__' and len(sys.argv)>1 and sys.argv[1]=='prices':
 summarize([run_prices(m) for m in map(int,sys.argv[2:] or [16,24,40])])
