"""DIAGNOSTIC_NEVER_A_PROOF. Source even matrices; no PSD repair."""
from pathlib import Path
import os
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[key]='1'
import json,hashlib,importlib.util,time,re,sys
sys.dont_write_bytecode=True
import numpy as np
import mpmath as mp
from scipy.linalg import eigvalsh
from scipy.special import roots_legendre
OUT=Path(__file__).resolve().parent
BASE=OUT.parents[2]
PROTO=BASE/'suzuki_W_2026-11-02/W/prototype.py'
DH=BASE/'fake_worlds_2026-11-02/dh_matrix.py'
CAP=BASE/'capacity_matrix_2026-11-02/capacity.py'
def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);v=importlib.util.module_from_spec(s);s.loader.exec_module(v);return v
mod=load(PROTO,'source_prototype');dh=load(DH,'dh_source');cap=load(CAP,'capacity_source')
mp.mp.dps=80
_,b=dh.coeffs(120)
mod.B['dh']=np.array([float(x) for x in b]);mod.B['zeta']=mod.coefficients('zeta',120)
sourcehash={str(p.relative_to(BASE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [PROTO,DH,CAP]}
(OUT/'dh_coefficients_dps80.json').write_text(json.dumps(dict(dps=80,coefficients=[mp.nstr(x,80) for x in b],source_sha256=sourcehash[str(DH.relative_to(BASE))]),indent=2)+'\n')
def set_order(order):
 g,w=roots_legendre(order);mod.ys=np.concatenate([(p+(g+1)/2)/8 for p in range(8)]);mod.ws=np.tile(w/16,8)
 ns=np.arange(121);mod.COS=np.cos(2*np.pi*mod.ys[:,None]*ns);mod.SIN=np.sin(2*np.pi*mod.ys[:,None]*ns)
def source_cache(world,m):
 candidates=[]
 if world=='zeta':
  candidates.extend((BASE/'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local').glob(f'core_m{m}_dps*_gl*.json'))
  candidates.extend((BASE/'cluster_count_2026-11-02/level_zero_ladder').glob(f'cell_m{m}_dps*_gl*.json'))
 else:candidates.extend((BASE/'fake_worlds_2026-11-02/matrix_cells').glob(f'dh_m{m}_dps*_gl*.json'))
 def score(p):
  z=re.search(r'dps(\d+)_gl(\d+)',p.name);return tuple(map(int,z.groups())) if z else (0,0)
 candidates.sort(key=score,reverse=True)
 matches=BASE/f'fake_worlds_2026-11-02/ledger_diff/matched_cells/source_{world}_m{m}.json'
 if matches.exists():candidates.insert(0,matches)
 for p in candidates:
  z=json.loads(p.read_text())
  if 'A' in z:return p,z
 return None,None
def cached_eigenvalues(world,m,z,p):
 if z:
  for key in ['full_eigenvalues','lambda_','A_eigenvalues','lambda']:
   if key in z:return z[key],p
 if world=='zeta':
  c=sorted((BASE/'capacity_conditioning_2026-11-02').glob(f'cell_m{m}_dps*_gl*.json'))
  if c:
   f=c[-1];a=json.loads(f.read_text());return a['A_eigenvalues'],f
 return None,None
priority=[16,24,32,40,55,65]+list(range(70,86))+[120]
ms=priority+[m for m in range(16,121) if m not in priority]
set_order(96);summary=[];cached={};start=time.monotonic()
for m in ms:
 for world in ['zeta','dh']:
  AF,_,bound=mod.build(world,m)
  p,z=source_cache(world,m)
  A=np.array(z['A'],dtype=float) if z else AF
  ev=eigvalsh(A);fro=float(np.linalg.norm(A,'fro'));radius=128*np.finfo(float).eps*(m+1)*max(1.,fro)
  mp_evs,mp_path=cached_eigenvalues(world,m,z,p)
  delta=float(np.linalg.norm(A-AF,'fro')) if z else None
  if delta is not None and delta>radius:raise ArithmeticError(('cache discrepancy',world,m,delta,radius))
  meta=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,L=float(np.log(m)),N=m,dimension=m+1,basis='e0=1/sqrtL;en=sqrt(2/L)*(-1)^n*cos(2*pi*n*x/L),zero extension',quadrature_order=96,numeric_radius=radius,radius_status='DIAGNOSTIC_NOT_INTERVAL',radius_formula='128*eps64*(m+1)*max(1,Frobenius_norm(A))',source_sha256=sourcehash,coefficient_precision='mp80 DH coefficients converted once to float64',matrix_assembly='rounded_cached_MP_source' if z else 'float_source_prototype',matrix_cache=str(p.relative_to(BASE)) if p else None,matrix_cache_sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p else None,prototype_to_MP_cache_Frobenius_difference=delta,mp_eigenvalues=mp_evs,mp_eigenvalues_source=str(mp_path.relative_to(BASE)) if mp_path else None,mp_eigenvalues_source_sha256=hashlib.sha256(mp_path.read_bytes()).hexdigest() if mp_path else None,minimum_sign='UNRESOLVED' if abs(ev[0])<=radius else ('NEGATIVE_DIAGNOSTIC' if ev[0]<0 else 'POSITIVE_DIAGNOSTIC'),float_minimum=float(ev[0]),source_symbol_lower_bound=float(bound))
  np.savez_compressed(OUT/f'cell_{world}_m{m}.npz',A=A,eigenvalues=ev,L=np.log(m),m=m,numeric_radius=radius)
  (OUT/f'cell_{world}_m{m}.json').write_text(json.dumps(meta,indent=2)+'\n')
  cached[(world,m)]=A;summary.append({k:meta[k] for k in ['world','m','float_minimum','minimum_sign','numeric_radius','matrix_assembly']})
 # No extra sqrt2: Erow itself is the raw physical Fourier row.
 w=2*mp.pi/mp.log(2)+mp.j/4;raw=cap.Erow(w,m);E=np.array([complex(x) for x in raw])
 perturb=4*(np.outer(E.real,E.real)-np.outer(E.imag,E.imag));A=cached[('zeta',m)]+perturb
 ev=eigvalsh(A);radius=128*np.finfo(float).eps*(m+1)*max(1.,float(np.linalg.norm(A,'fro')))
 meta=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world='plant',m=m,N=m,L=float(np.log(m)),dimension=m+1,numeric_radius=radius,radius_status='DIAGNOSTIC_NOT_INTERVAL',radius_formula='128*eps64*(m+1)*max(1,Frobenius_norm(A))',source_sha256=sourcehash,plant_frequency=[mp.nstr(mp.re(w),80),mp.nstr(mp.im(w),80)],plant_update='A_zeta+4*(Re(E(w))*Re(E(w))^T-Im(E(w))*Im(E(w))^T)',physical_E_has_no_extra_sqrt2=True,plant_E_dps80=[[mp.nstr(mp.re(x),80),mp.nstr(mp.im(x),80)] for x in raw],mp_eigenvalues=None,minimum_sign='UNRESOLVED' if abs(ev[0])<=radius else ('NEGATIVE_DIAGNOSTIC' if ev[0]<0 else 'POSITIVE_DIAGNOSTIC'),float_minimum=float(ev[0]),plant_update_Frobenius_norm=float(np.linalg.norm(perturb,'fro')))
 np.savez_compressed(OUT/f'cell_plant_m{m}.npz',A=A,eigenvalues=ev,L=np.log(m),m=m,numeric_radius=radius,plant_E=E)
 (OUT/f'cell_plant_m{m}.json').write_text(json.dumps(meta,indent=2)+'\n');summary.append({k:meta[k] for k in ['world','m','float_minimum','minimum_sign','numeric_radius']})
 print('READY',m,'seconds',round(time.monotonic()-start,2),flush=True)
# Independent quadrature-order comparison against same-source precision-fixed coefficients.
set_order(192);checks=[]
for m in [16,24,40,55,65,70,75,80,85,120]:
 for world in ['zeta','dh']:
  A192,_,_=mod.build(world,m);A96=cached[(world,m)]
  error=float(np.linalg.norm(A192-A96,'fro'));meta=json.loads((OUT/f'cell_{world}_m{m}.json').read_text());radius=meta['numeric_radius']
  check=dict(world=world,m=m,comparison='quadrature192 source vs saved matrix (96 or rounded cached MP)',Frobenius_difference=error,numeric_radius=radius,within_radius=bool(error<radius));checks.append(check)
  if not error<radius:raise ArithmeticError(check)
(OUT/'quadrature_validation.json').write_text(json.dumps(checks,indent=2)+'\n')
(OUT/'summary.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',cell_count=len(summary),elapsed_seconds=time.monotonic()-start,rows=summary),indent=2)+'\n')
print('ALL_DONE',len(summary),'seconds',time.monotonic()-start,flush=True)
