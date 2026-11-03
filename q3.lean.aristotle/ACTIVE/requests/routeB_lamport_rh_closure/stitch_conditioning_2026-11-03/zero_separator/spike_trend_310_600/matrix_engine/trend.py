"""Literal MP source, float spectra only; finite trend diagnostic."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import time,json,hashlib,argparse
import numpy as np
from scipy.linalg import eigvalsh
import source
P=Path(__file__).resolve().parent;O=P.parent/'matrices'
def run(m,compare=False):
 start=time.monotonic();A=source.build(m,256);buildsec=time.monotonic()-start;other=source.build(m,320) if compare else None;rows=[]
 for w,M in A.items():
  Af=np.array(M,float);ev=eigvalsh(Af);scale=max(1.,max(abs(ev)));rad=64*np.finfo(float).eps*(m+1)*scale;lo=int(sum(ev < -rad));hi=int(sum(ev < rad));diff=max(abs(v) for v in (M-other[w]).flat) if other is not None else None
  a=dict(status='DIAGNOSTIC_NEVER_A_PROOF',scope='TREND_ONLY_NO_NEW_MP_ZERO_THRESHOLD_COUNTS',source_ref='1d3818c',world=w,m=m,N=m,bits=400,GL_order=256,panels=8,source_build_seconds=buildsec,seconds=time.monotonic()-start,numeric_radius=rad,float_numeric_radius=rad,float_minimum=float(ev[0]),float_maximum=float(ev[-1]),negative_count_range=[lo,hi],resolved_negative_count=lo,uncertain_zero_sign_modes=hi-lo,zero_threshold_count_method='float64 eigenvalues outside conservative heuristic roundoff radius; NOT certified inertia',exact_inertia_claim=False,raw_zero_count_not_certified=True,paired_order=320 if compare else None,paired_order_entry_difference=str(diff) if diff is not None else None,source_quad_guard_status='Empirical paired-order pilots, not interval bound',source='literal even source arch+tail+signed atoms; zeta pole only; plant+4Re(eeT)')
  np.savez_compressed(O/f'{w}_m{m}.npz',A=Af,eigenvalues=ev,lambda_=ev,m=m,numeric_radius=rad);(O/f'{w}_m{m}.json').write_text(json.dumps(a,indent=2)+'\n');rows.append(dict(world=w,negative_range=[lo,hi],difference=str(diff)))
 print(json.dumps(dict(m=m,build_seconds=buildsec,total_seconds=time.monotonic()-start,worlds=rows)),flush=True)
 return rows
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');a=p.parse_args()
 if a.pilot:
  for m in [310,600]:run(m,True)
 else:
  from concurrent.futures import ProcessPoolExecutor
  with ProcessPoolExecutor(max_workers=2) as pool:list(pool.map(run,range(320,600,10)))
