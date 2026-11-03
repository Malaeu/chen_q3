import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import argparse,time,json,hashlib
import numpy as np
from scipy.linalg import eigvalsh
import split
P=Path(__file__).resolve().parent

def run(m,pilot=False):
 start=time.monotonic();a=split.build(m,192);other=split.build(m,256) if m in [16,300] and pilot else None;rows=[]
 for w,z in a.items():
  cf,bf,af,at=[np.array(z[k],float)for k in ['C','B','A1','atom2']];spectrum={name:eigvalsh(M) for name,M in [('C',cf),('B',bf),('A1',af)]};radius=64*np.finfo(float).eps*(m+1)*max(1.,max(abs(v) for ev in spectrum.values()for v in ev));diff=max(abs(v)for key in ['C','B','A1']for v in(z[key]-other[w][key]).flat)if other else None
  rec=float(np.max(abs(cf+bf-af)));original=None
  if w!='double2':
   paths=[Path(f'/workspace/zero_extension/matrices/{w}_m{m}.npz'),Path(f'/workspace/dh_existing/matched_cells/source_{w}_m{m}.json')]
   if w=='dh':paths.append(Path(f'/workspace/dh_inputs/matrix_cells/dh_float_m{m}.npz'))
   for path in paths:
    if path.exists():
     saved=np.load(path)['A']if path.suffix=='.npz'else np.array(json.loads(path.read_text())['A'],float);original=dict(path=str(path),max_abs_entry_difference=float(np.max(abs(af-saved))),sha256=hashlib.sha256(path.read_bytes()).hexdigest());break
  meta=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=w,m=m,N=m,bits=400,GL_order=192,panels=8,source_definition='A(u)=C+uB; C=archimedean gamma+tail+zeta pole; B=all negative-signed arithmetic atoms; double2 adds only the zeta integer n=2 atom to B',C_minimum=float(spectrum['C'][0]),B_minimum=float(spectrum['B'][0]),A1_minimum=float(spectrum['A1'][0]),numeric_radius=radius,float_C_plus_B_reconstruction=rec,sign_groups=z['sign_groups'],sign_conservation_max_entry=z['sign_conservation_max_entry'],paired_GL256_max_entry_difference=str(diff)if diff is not None else None,frozen_A_regression=original,seconds=time.monotonic()-start)
  np.savez_compressed(P/f'{w}_m{m}.npz',C=cf,B=bf,A1=af,A=af,atom2=at,C_eigenvalues=spectrum['C'],B_eigenvalues=spectrum['B'],eigenvalues=spectrum['A1'],m=m,numeric_radius=radius)
  (P/f'{w}_m{m}.json').write_text(json.dumps(meta,indent=2)+'\n');rows.append({k:meta[k]for k in ['world','C_minimum','B_minimum','A1_minimum']})
 print(json.dumps(dict(m=m,seconds=time.monotonic()-start,worlds=rows)),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');a=p.parse_args()
 if a.pilot:
  for m in [16,24,80,248,300]:run(m,True)
 else:
  from concurrent.futures import ProcessPoolExecutor
  todo=[m for m in range(16,301)if not all((P/f'{w}_m{m}.npz').exists()and(P/f'{w}_m{m}.json').exists()for w in ['zeta','dh','double2'])]
  print('MISSING',todo,flush=True)
  with ProcessPoolExecutor(max_workers=2)as pool:list(pool.map(run,todo))
