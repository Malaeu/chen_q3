"""DIAGNOSTIC_NEVER_A_PROOF. Shared MP spectrum helper; all writes inside chosen output.
Default scope is explicitly provided via --ms and --worlds; no implicit broad sweep.
"""
from pathlib import Path
import sys,importlib.util,time,json,hashlib,argparse,re
sys.dont_write_bytecode=True
import mpmath as mp
import numpy as np
P=Path(__file__).resolve().parent;BASE=P.parents[3]
SOURCE=BASE/'lit_quickcheck_2026-11-03/Q2_simple_even/check.py'
spec=importlib.util.spec_from_file_location('q2_source',SOURCE);src=importlib.util.module_from_spec(spec);spec.loader.exec_module(src)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--ms',nargs='+',type=int,required=True);ap.add_argument('--worlds',nargs='+',choices=['zeta','plant','dh'],required=True);ap.add_argument('--dps',type=int,default=100);ap.add_argument('--order',type=int,default=128);ap.add_argument('--label',default='priority');ap.add_argument('--out',default=str(P));ap.add_argument('--cpu-budget',type=float,default=0);ap.add_argument('--eig-backend',choices=['mpmath','acb400'],default='mpmath');a=ap.parse_args();out=Path(a.out);out.mkdir(exist_ok=True,parents=True);mp.mp.dps=a.dps
 if a.eig_backend=='acb400':
  sys.path.insert(0,'/tmp/litdeps')
  from flint import acb_mat,arb,ctx
  ctx.prec=400
 cache={w:src.coeffs(120,w) for w in ['zeta','dh']};src.coeffs=lambda M,w:cache[w][:M+1]
 coeff_payload=json.dumps({w:[mp.nstr(x,a.dps) for x in b] for w,b in cache.items()},sort_keys=True,separators=(',',':'))+'\n'
 (out/f'{a.label}_coefficients_dps{a.dps}.json').write_text(coeff_payload)
 start_all=time.perf_counter();cpu_start=time.process_time();records=[]
 for m in a.ms:
  matrices={};meta_src={}
  for underlying in (['zeta'] if any(w in a.worlds for w in ['zeta','plant']) else [])+(['dh'] if 'dh' in a.worlds else []):
   t=time.perf_counter();c=time.process_time();meta=json.loads((P.parent/f'cell_{underlying}_m{m}.json').read_text());path=BASE/meta['matrix_cache'] if meta.get('matrix_cache') else None
   pilot=P/f'pilot_zeta_m{m}_dps100_GL160.json'
   if underlying=='zeta' and pilot.exists():
    z=json.loads(pilot.read_text());A=mp.matrix(z['A']);origin=dict(kind='pilot_GL160_cache',path=str(pilot.relative_to(BASE)),sha256=hashlib.sha256(pilot.read_bytes()).hexdigest(),input_dps=100)
   elif path and path.exists():
    z=json.loads(path.read_text());A=mp.matrix(z['A']);origin=dict(kind='inherited_MP_source_cache',path=str(path.relative_to(BASE)),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),original_provenance=z.get('provenance',{}),input_dps=z.get('dps','see source provenance'))
   else:
    A,_=src.build(m,m,underlying,a.order);origin=dict(kind='fresh_MP_source_build',path=str(SOURCE.relative_to(BASE)),sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),input_dps=a.dps,GL=a.order)
   matrices[underlying]=A;meta_src[underlying]=dict(build_wall_seconds=time.perf_counter()-t,build_cpu_seconds=time.process_time()-c,origin=origin)
  for world in a.worlds:
   origin=meta_src['dh' if world=='dh' else 'zeta'];A=matrices['dh' if world=='dh' else 'zeta'].copy()
   if world=='plant':
    L=mp.log(m);w=2*mp.pi/mp.log(2)+mp.j/4
    row=[2*mp.sin(w*L/2)/(mp.sqrt(L)*w)]+[mp.sqrt(2/L)*2*w*mp.sin(w*L/2)/(w*w-(2*mp.pi*n/L)**2) for n in range(1,m+1)]
    A+=mp.matrix([[4*mp.re(x*y) for y in row] for x in row])
   t=time.perf_counter();c=time.process_time();reuse=None
   base_meta=json.loads((P.parent/f'cell_{world}_m{m}.json').read_text())
   pilot_file=P/f'pilot_zeta_m{m}_dps100_GL160.json'
   if world=='zeta' and pilot_file.exists():reuse=json.loads(pilot_file.read_text())['eigenvalues']
   elif base_meta.get('mp_eigenvalues') is not None:reuse=base_meta['mp_eigenvalues']
   imaginary_part=mp.mpf(0)
   if reuse is not None:e=list(map(mp.mpf,reuse))
   elif a.eig_backend=='acb400':
    ZA=acb_mat([[arb(mp.nstr(A[i,j],a.dps)) for j in range(A.cols)] for i in range(A.rows)])
    ZE=ZA.eig(algorithm='approx')
    def to_mp(v):
     man,exponent=v.mid().man_exp();return mp.ldexp(mp.mpf(int(man)),int(exponent))
    imaginary_part=max(abs(to_mp(v.imag)) for v in ZE);e=sorted(to_mp(v.real) for v in ZE)
    assert imaginary_part<mp.mpf(10)**(-a.dps+15)*max(1,mp.norm(A))
   else:e=mp.eigsy(A,eigvals_only=True)
   et=time.perf_counter()-t;ec=time.process_time()-c
   f=np.load(P.parent/f'cell_{world}_m{m}.npz');delta=float(np.linalg.norm(np.array(A.tolist(),dtype=float)-f['A'],'fro'));radius=float(f['numeric_radius']);assert delta<radius,(world,m,delta,radius)
   inherited_precision=origin['origin'].get('input_dps')
   if not isinstance(inherited_precision,int):
    hits=re.findall(r'dps(\d+)',json.dumps(origin));inherited_precision=min(map(int,hits)) if hits else a.dps
   effective_dps=min(a.dps,inherited_precision)
   round_guard=mp.mpf(10)**(-effective_dps+15)*max(1,mp.norm(A))
   payload=json.dumps([[mp.nstr(x,a.dps) for x in A[i,:]] for i in range(A.rows)],separators=(',',':'))
   z=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,N=m,dps=a.dps,GL=a.order,GL_scope='requested order for fresh source builds; inherited cache order in source_metadata',eigenvalue_method='reused_MP_spectrum' if reuse is not None else ('flint_acb_approx_no_interval_bounds' if a.eig_backend=='acb400' else 'mpmath_eigsy'),eigen_solver_bits=400 if a.eig_backend=='acb400' and reuse is None else None,eigen_max_imaginary_part=mp.nstr(imaginary_part,30),eigenvalues=[mp.nstr(x,a.dps) for x in e],roundoff_heuristic=mp.nstr(round_guard,30),effective_source_dps=effective_dps,quadrature_status=f'requested fresh-source Gauss order{a.order}; inherited cache provenance in source_metadata; selected separate128→160 pilot; not an interval bound',matrix_decimal_sha256=hashlib.sha256(payload.encode()).hexdigest(),source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),coefficient_sha256=hashlib.sha256(coeff_payload.encode()).hexdigest(),source_metadata=origin,eig_wall_seconds=et,eig_cpu_seconds=ec,float_matrix_difference_Frobenius=delta,float_numeric_radius=radius,plant_E_no_extra_sqrt2=True if world=='plant' else None)
   file=out/f'mp_cell_{world}_m{m}_dps{a.dps}_GL{a.order}.json';temp=file.with_suffix('.json.tmp');temp.write_text(json.dumps(z,indent=2)+'\n');temp.replace(file);brief={k:z[k] for k in ['world','m','dps','eig_wall_seconds','eig_cpu_seconds','float_matrix_difference_Frobenius']};records.append(brief);print('READY',file.name,json.dumps(brief),flush=True)
  (out/f'{a.label}_timings.json').write_text(json.dumps(dict(elapsed_wall_seconds=time.perf_counter()-start_all,elapsed_cpu_seconds=time.process_time()-cpu_start,rows=records),indent=2)+'\n')
  if a.cpu_budget and time.process_time()-cpu_start>a.cpu_budget:
   print('CPU_BUDGET_STOP',a.cpu_budget,flush=True);break
 (out/f'{a.label}_complete.json').write_text(json.dumps(dict(complete=len(records)==len(a.ms)*len(a.worlds),cells=len(records),requested_cells=len(a.ms)*len(a.worlds),elapsed_wall_seconds=time.perf_counter()-start_all,elapsed_cpu_seconds=time.process_time()-cpu_start),indent=2)+'\n')
if __name__=='__main__':main()
