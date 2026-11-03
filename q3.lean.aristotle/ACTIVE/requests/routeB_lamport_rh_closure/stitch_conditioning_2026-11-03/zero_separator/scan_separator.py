"""All distinct cutoff sectors on frozen literal-even CCM matrices. Diagnostic only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,json,csv,hashlib,time,argparse,gzip
import numpy as np
import scipy.linalg as la
import gmpy2 as gp

def events(root,world):
 if world in ('zeta','plant'):
  out=[(gp.mpfr(x['gamma']),gp.mpfr(0),1) for x in csv.DictReader((root/'zeros.csv').open())]
 else:
  j=json.loads((root/'dh_zeros.json').read_text());out=[(gp.mpfr(x['gamma']),gp.mpfr(0),1)for x in j['critical_line_zeros']]
  out += [(gp.mpfr(x['gamma']),gp.mpfr(x['sigma_right'])-gp.mpfr('.5'),2)for x in j['off_line_pairs']]
 if world=='plant':out.append((2*gp.const_pi()/gp.log(2),gp.mpfr('.25'),2))
 return sorted(out)

def run(task):
 root,out,world,m,bits=task;root=Path(root);out=Path(out);gp.get_context().precision=bits
 start=time.monotonic();P=root/'C_conditioning';M=P/'matrices';d=m+1
 counts=list(csv.DictReader((out/'counts.csv').open()));c=next(x for x in counts if x['world']==world and int(x['m'])==m)
 sp=P/c['spectrum_file'];spec=json.loads(sp.read_text());vals=spec.get('eigenvalues',spec.get('mp_eigenvalues'));ev=np.array([float(x)for x in vals]);sg=float(c['roundoff_guard'])
 cell=np.load(M/f'cell_{world}_m{m}.npz');A=cell['A'];rad=float(cell['numeric_radius']);norm=la.norm(A,2);tol=max(rad,1000*np.finfo(float).eps*d*max(1,norm))
 all_events=events(root,world);L=gp.log(m);omega=2*gp.const_pi()*m/L;freq=[(2*gp.const_pi()*j/L)**2 for j in range(d)];scale=[gp.mpfr(1)]+[gp.sqrt(2)]*m
 basis=np.empty((d-1,d),object);n=0;prefix=[];smallest=gp.mpfr(1)
 for i,(height,imag,mult) in enumerate(all_events):
  if n+mult>=d:break
  t=gp.mpc(height,imag);fac=2*t*gp.sin(t*L/2)/gp.sqrt(L) if mult==2 else gp.mpfr(1)
  row=[fac*scale[j]/(t*t-freq[j])for j in range(d)]
  for component in range(mult):
   v=np.array([z.real if component==0 else z.imag for z in row],object);norm0=gp.sqrt(sum(x*x for x in v))
   for _ in range(2):
    if n:v=v-(basis[:n]@v)@basis[:n]
   nv=gp.sqrt(sum(x*x for x in v));smallest=min(smallest,nv/norm0)
   if nv<gp.mpfr('1e-190')*norm0:raise ArithmeticError(f'unresolved row rank {world} {m} {n}')
   basis[n]=v/nv;n+=1
  prefix.append((n,height,all_events[i+1][0]))
 if not prefix or prefix[-1][0]+all_events[len(prefix)][2]<d:
  raise ArithmeticError('zero census does not reach full rank')
 # A QR of the already MP-orthogonal frame preserves all ordered prefixes.
 uf=np.array(basis[:n].tolist(),float);orth=la.norm(uf@uf.T-np.eye(n),2);frame,_=la.qr(uf.T,mode='full');rows=[]
 for q,h,next_h in prefix:
  r=d-q;Q=frame[:,q:];delta=la.norm(A@Q,2);lam=ev[r];gap=lam-delta;guard=tol+sg
  excluded=lam+sg<0 or lam+sg<-ev[0]-sg
  status='PASS_NUMERIC' if gap>guard else ('FAIL_NUMERIC' if gap < -guard else 'UNRESOLVED_NUMERIC_FLOOR')
  if excluded:
   if status=='PASS_NUMERIC':raise ArithmeticError('separator violates singular-value minmax')
   status='SPECTRAL_NECESSARY_FAIL'
  lo=float(h/omega);hi=float(next_h/omega)
  rows.append(dict(world=world,m=m,q=q,r=r,kappa_left_open=lo,kappa_right_closed=hi,kappa_mid=(lo+hi)/2,intersects_kappa_ge1=int(hi>=1),delta=delta,lambda_r=lam,gap=gap,numeric_guard=guard,status=status,lambda_r_category='NONPOSITIVE' if lam<=0 else ('POSITIVE_BELOW_C2' if lam<2 else 'AT_OR_ABOVE_C2'),necessary_gap=lam-max(-ev[0],ev[r-1],0),source_matrix_sha256=hashlib.sha256((M/f'cell_{world}_m{m}.npz').read_bytes()).hexdigest()))
 best=max(rows,key=lambda r:r['gap']);passing=[r for r in rows if r['status']=='PASS_NUMERIC'];ge1=[r for r in rows if r['intersects_kappa_ge1']];pass_ge1=[r for r in passing if r['intersects_kappa_ge1']];unresolved=[r for r in rows if r['status']=='UNRESOLVED_NUMERIC_FLOOR'];best1=max(ge1,key=lambda r:r['gap']) if ge1 else None
 summary=dict(world=world,m=m,n_minus_lower=c['guarded_negative_lower'],n_minus_upper=c['guarded_negative_upper'],zero_sign_unresolved=c['unresolved_near_zero'],separator_any_kappa='YES_NUMERIC' if passing else ('UNRESOLVED' if unresolved else 'NO_NUMERIC'),separator_kappa_ge1='YES_NUMERIC' if pass_ge1 else ('UNRESOLVED' if any(r['status']=='UNRESOLVED_NUMERIC_FLOOR'for r in ge1)else'NO_NUMERIC'),sector_count=len(rows),pass_sectors=len(passing),pass_sectors_ge1=len(pass_ge1),unresolved_sectors=len(unresolved),best_kappa=best['kappa_mid'],best_kappa_left=best['kappa_left_open'],best_kappa_right=best['kappa_right_closed'],best_r=best['r'],best_delta=best['delta'],best_lambda_r=best['lambda_r'],best_gap=best['gap'],best_status=best['status'],best_ge1_gap=best1['gap'] if best1 else None,best_ge1_r=best1['r'] if best1 else None,passes_below_C2=sum(r['lambda_r_category']=='POSITIVE_BELOW_C2' for r in passing),MP_frame_float_orthogonality=orth,minimum_MGS_relative_pivot=str(smallest),bits=bits,seconds=time.monotonic()-start)
 (out/'cells').mkdir(exist_ok=True);(out/'cells'/f'{world}_m{m}.json').write_text(json.dumps(dict(summary=summary,sectors=rows),indent=2)+'\n');print(world,m,summary['separator_any_kappa'],'gap',best['gap'],'seconds',round(summary['seconds'],2),flush=True);return summary

if __name__=='__main__':
 from concurrent.futures import ProcessPoolExecutor
 ap=argparse.ArgumentParser();ap.add_argument('--input',default='/workspace/conditioning_input');ap.add_argument('--output',default=str(Path(__file__).resolve().parent));ap.add_argument('--m',nargs='+',type=int,default=list(range(16,121)));ap.add_argument('--world',nargs='+',default=['zeta','plant','dh']);ap.add_argument('--bits',type=int,default=768);ap.add_argument('--workers',type=int,default=3);a=ap.parse_args();tasks=[(a.input,a.output,w,m,a.bits)for w in a.world for m in a.m]
 with ProcessPoolExecutor(a.workers)as pool:list(pool.map(run,tasks))
