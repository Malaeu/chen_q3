"""κ>=1 literal-even scan; global best-gap bounds retain pruned sectors."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import argparse,json,csv,time,hashlib
import numpy as np,scipy.linalg as la,gmpy2 as g
from native_frame import frame
P=Path(__file__).resolve().parent
def events(world):
 if world in ('zeta','plant'):
  ev=[(g.mpfr(x['gamma']),g.mpfr(0),1)for x in csv.DictReader((P/'zeta_zeros.csv').open())]
 else:
  z=json.loads((P/'dh_census/dh_zeros_900_200dps.json').read_text());ev=[(g.mpfr(x['gamma']),g.mpfr(0),1)for x in z['critical_line_zeros']];ev +=[(g.mpfr(x['gamma']),g.mpfr(x['sigma_right'])-g.mpfr('.5'),2)for x in z['off_line_pairs']]
 if world=='plant':ev.append((2*g.const_pi()/g.log(2),g.mpfr('.25'),2))
 return sorted(ev)
def last_null(ev,q,m,bits):
 """Exact rational-nullspace identity, no ill-conditioned Gram inverse."""
 d=m+1;r=d-q;L=g.log(m);scale=[g.mpfr(1)]+[g.sqrt(2)]*m
 fac=[g.mpfr(g.fac(k))for k in range(2*m+1)]
 weights=[(g.mpfr(-1)if m%2 else g.mpfr(1))/(fac[m]*fac[m])]
 weights +=[(g.mpfr(-1)if(m-j)%2 else g.mpfr(1))*2/(scale[j]*fac[m-j]*fac[m+j])for j in range(1,d)]
 n=0
 for h,im,mult in ev:
  if n>=q:break
  z=(g.mpc(h,im)*L/(2*g.const_pi()))**2
  for j in range(d):weights[j]*=(g.mpfr(j*j)-z.real)if mult==1 else abs(g.mpfr(j*j)-z)**2
  n+=mult
 assert n==q
 maxw=max(abs(x)for x in weights);weights=[x/maxw for x in weights]
 rows=[[weights[j]*(g.mpfr(j*j)/m**2)**k for j in range(d)]for k in range(r)]
 uf,_=frame(rows,bits);return uf.T
def run(task):
 world,m,bits=task;g.get_context().precision=bits;start=time.monotonic();d=m+1
 source=P/'matrices'/f'{world}_m{m}.npz';npz=np.load(source);A=npz['A'];ae=npz['eigenvalues'];norm=la.norm(A,2)
 guard=max(float(npz['numeric_radius']),1000*np.finfo(float).eps*d*max(1,norm));meta=json.loads(source.with_suffix('.json').read_text())
 meta.setdefault('guard','NOT_COMPUTED_NO_MP_INERTIA_REQUESTED');L=g.log(m);omega=2*g.const_pi()*m/L;ev=events(world);q=0;sectors=[]
 for i,(h,im,mult)in enumerate(ev):
  q+=mult
  if q>=d:break
  if i+1>=len(ev):raise ArithmeticError('census too short for next cutoff')
  hi=float(ev[i+1][0]/omega);lo=float(h/omega)
  if hi>=1:sectors.append(dict(q=q,r=d-q,kappa_left_open=lo,kappa_right_closed=hi,kappa_representative=max(1,(lo+hi)/2),lambda_r=float(ae[d-q])))
 assert sectors and q>=d,('census too short',world,m,q)
 last=sectors[-1];Qlast=last_null(ev,last['q'],m,bits);dl=la.norm(A@Qlast,2);last.update(delta=float(dl),gap=last['lambda_r']-float(dl),method='CAUCHY_NULL_POLYNOMIAL',status='UNRESOLVED_NUMERIC_FLOOR'if abs(last['lambda_r']-dl)<=guard else('PASS_NUMERIC'if last['lambda_r']>dl else'FAIL_NUMERIC'))
 best=dict(last);evaluated=[];needed=[];pruned=[];tail_q=set()
 # With multiple negative levels, r=1 can itself index a negative eigenvalue.
 # Seed the first few attainable indices above the resolved negative block.
 if world=='dh':
  nneg=meta['negative_count_range'][0]
  for s in sectors[:-1]:
   if nneg<=s['r']<=nneg+2:
    Q=last_null(ev,s['q'],m,bits);delta=float(la.norm(A@Q,2));gap=s['lambda_r']-delta
    s.update(delta=delta,gap=gap,method='CAUCHY_NULL_POLYNOMIAL',status='SPECTRAL_NECESSARY_FAIL'if s['lambda_r']+guard < -ae[0]-guard else('PASS_NUMERIC'if gap>guard else('FAIL_NUMERIC'if gap < -guard else'UNRESOLVED_NUMERIC_FLOOR')))
    evaluated.append(dict(s));tail_q.add(s['q'])
    if gap>best['gap']:best=dict(s)
 for s in sectors[:-1]:
  if s['q']in tail_q:continue
  lam=s['lambda_r'];neg=-float(ae[0]);necessary_fail=lam+guard<neg-guard or lam+guard<0
  if necessary_fail:pruned.append(dict(**s,method='SPECTRAL_NECESSARY_REJECTION',gap_upper_bound=0.0,status='NO_SEPARATOR_NUMERIC'));continue
  # ζ can stop once the monotonically decreasing λ_r is below its incumbent.
  if world=='zeta'and lam+guard<best['gap']-guard:
   pruned.append(dict(**s,method='BEST_GAP_UPPER_BOUND',gap_upper_bound=lam+guard,status='CANNOT_IMPROVE_INCUMBENT'));continue
  needed.append(s)
 # Build only the prefix needed for non-excluded, non-tiny levels. Tiny ζ
 # tail is subsequently bounded by λ_r once a positive incumbent is known.
 bulk=[s for s in needed if world!='zeta'or s['lambda_r']>guard]
 if bulk:
  qmax=max(s['q']for s in bulk);rows=[];freq=[(2*g.const_pi()*j/L)**2 for j in range(d)];ds=[g.mpfr(1)]+[g.sqrt(2)]*m
  for h,im,mult in ev:
   if len(rows)>=qmax:break
   t=g.mpc(h,im);fac=2*t*g.sin(t*L/2)/g.sqrt(L)if mult==2 else g.mpfr(1);row=[fac*ds[j]/(t*t-freq[j])for j in range(d)]
   rows.append([x.real for x in row])
   if mult==2:rows.append([x.imag for x in row])
  assert len(rows)==qmax
  uf,pivots=frame(rows,bits);frame_orth=float(la.norm(uf@uf.T-np.eye(qmax),2));whole,_=la.qr(uf.T,mode='full')
  for s in bulk:
   if s['lambda_r']+guard<best['gap']-guard:
    pruned.append(dict(**s,method='BEST_GAP_UPPER_BOUND',gap_upper_bound=s['lambda_r']+guard,status='CANNOT_IMPROVE_INCUMBENT'));continue
   Q=whole[:,s['q']:];delta=float(la.norm(A@Q,2));gap=s['lambda_r']-delta;s.update(delta=delta,gap=gap,method='MPFR_ORDERED_FRAME',status='PASS_NUMERIC'if gap>guard else('FAIL_NUMERIC'if gap < -guard else'UNRESOLVED_NUMERIC_FLOOR'));evaluated.append(dict(s))
   if gap>best['gap']:best=dict(s)
 else:frame_orth=None;pivots=[]
 for s in needed:
  if world=='zeta'and s['lambda_r']<=guard:
   if s['lambda_r']+guard<best['gap']-guard:pruned.append(dict(**s,method='BEST_GAP_UPPER_BOUND',gap_upper_bound=s['lambda_r']+guard,status='CANNOT_IMPROVE_INCUMBENT'))
   else:pruned.append(dict(**s,method='NUMERIC_FLOOR_UPPER_BOUND',gap_upper_bound=s['lambda_r']+guard,status='UNRESOLVED_TINY_SEPARATOR'))
 evaluated.append(dict(last));assert len(evaluated)+len(pruned)==len(sectors)
 # Last tiny residual is at the numerical floor. For a negative world, the
 # strong necessary test excludes it without resolving that displayed δ.
 if last['lambda_r']+guard < -ae[0]-guard:last['status']='SPECTRAL_NECESSARY_FAIL';evaluated[-1]['status']=last['status']
 passes=[s for s in evaluated if s['gap']>guard];uncertain=[s for s in evaluated if s['status']=='UNRESOLVED_NUMERIC_FLOOR']
 verdict='YES_NUMERIC'if passes else('UNRESOLVED'if uncertain or any(s['status']=='UNRESOLVED_TINY_SEPARATOR'for s in pruned)else'NO_NUMERIC')
 upper=max([s['gap']+guard for s in evaluated]+[s['gap_upper_bound']+guard for s in pruned]);lower=best['gap']-guard
 old4=4;offline_at1=sum(mult==2 for h,im,mult in ev if h<omega)
 summary=dict(world=world,m=m,dimension=d,n_minus_lower=meta['negative_count_range'][0],n_minus_upper=meta['negative_count_range'][1],source_zero_guard=meta['guard'],separator_kappa_ge1=verdict,best_delta=best['delta'],best_lambda_r=best['lambda_r'],best_gap=best['gap'],best_r=best['r'],best_q=best['q'],best_kappa=best['kappa_representative'],best_kappa_left_open=best['kappa_left_open'],best_kappa_right_closed=best['kappa_right_closed'],best_candidate_method=best['method'],max_gap_lower_bound=lower,max_gap_upper_bound=upper,numeric_guard=guard,best_gap_resolved=upper-lower<=4*guard,sector_count=len(sectors),evaluated_sectors=len(evaluated),bounded_sectors=len(pruned),passing_sectors=len(passes),passing_positive_below_C2=sum(0<s['lambda_r']<2 for s in passes),quartets_below_kappa1=offline_at1,frame_bits=bits,MP_frame_float_orthogonality=frame_orth,smallest_MGS_relative_pivot=float(min(pivots))if len(pivots)else None,last_quiet_r=last['r'],source_matrix_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),seconds=time.monotonic()-start)
 out=P/'scan_cells';out.mkdir(exist_ok=True);(out/f'{world}_m{m}.json').write_text(json.dumps(dict(summary=summary,evaluated=evaluated,bounded=pruned),indent=2,default=lambda x:x.item()if isinstance(x,np.generic)else str(x))+'\n');print(world,m,verdict,'gap',best['gap'],'sectors',len(sectors),'evaluated',len(evaluated),'seconds',round(time.monotonic()-start,2),flush=True)
 return summary
if __name__=='__main__':
 from concurrent.futures import ProcessPoolExecutor
 ap=argparse.ArgumentParser();ap.add_argument('--m',nargs='+',type=int,default=list(range(310,601,10)));ap.add_argument('--world',nargs='+',default=['zeta','plant','dh']);ap.add_argument('--bits',type=int,default=768);ap.add_argument('--workers',type=int,default=2);ap.add_argument('--skip-existing',action='store_true');a=ap.parse_args()
 tasks=[(w,m,a.bits)for m in a.m for w in a.world if not(a.skip_existing and(P/'scan_cells'/f'{w}_m{m}.json').exists())]
 with ProcessPoolExecutor(a.workers)as pool:list(pool.map(run,tasks))
