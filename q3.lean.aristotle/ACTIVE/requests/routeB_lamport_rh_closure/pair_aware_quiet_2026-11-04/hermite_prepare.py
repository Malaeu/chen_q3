"""Authorized local regeneration using unchanged high400bit/GL256 source."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,time
import numpy as np
import scipy.linalg as la
import baseline_replay as base

def prepare(m):
 if all((base.LOCAL/'matrices'/f'{w}_m{m}.npz').exists()for w in ['zeta','dh','plant']):return
 base.source.g.get_context().precision=400;t=time.monotonic();src=base.source.build(m,256)
 for w,M in src.items():
  A=np.array(M,float);ev=la.eigvalsh(A);radius=64*np.finfo(float).eps*(m+1)*max(1.,max(abs(ev)));path=base.LOCAL/'matrices'/f'{w}_m{m}.npz';np.savez_compressed(path,A=A,eigenvalues=ev,lambda_=ev,m=m,numeric_radius=radius)
  path.with_suffix('.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=w,m=m,source_py_sha256=base.sha(base.HIGH/'matrix_engine/source.py'),bits=400,GL_order=256,panels=8,numeric_radius=radius,source='unchanged pinned high builder; local only; no all-sector negative inertia claim'),indent=2)+'\n')
 print('HERMITE_SOURCE_READY',m,time.monotonic()-t,flush=True)
if __name__=='__main__':
 import sys
 for m in map(int,sys.argv[1:]):prepare(m)
