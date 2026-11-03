"""Single missing DH119 completion with validated approximate400bit backend."""
from pathlib import Path
import sys,time,json,hashlib,threading,os,importlib.util
sys.path.insert(0,'/tmp/litdeps')
import mpmath as mp
import numpy as np
from flint import acb_mat,ctx,arb
P=Path(__file__).resolve().parent;HELPER=P.parent/'batch_mp.py';MATS=P.parents[1];BASE=P.parents[4];SOURCE=BASE/'lit_quickcheck_2026-11-03/Q2_simple_even/check.py'
def main():
 file=P/'mp_cell_dh_m119_dps100_GL160.json'
 if file.exists():print('NOOP completed119alreadyexists');return
 start=time.perf_counter();cpu=time.process_time();timer=threading.Timer(30,lambda:os._exit(124));timer.daemon=True;timer.start();mp.mp.dps=100;ctx.prec=400
 spec=importlib.util.spec_from_file_location('q2_final_source',SOURCE);src=importlib.util.module_from_spec(spec);spec.loader.exec_module(src)
 coeff={w:src.coeffs(120,w) for w in ['zeta','dh']};src.coeffs=lambda M,w:coeff[w][:M+1]
 cp=json.dumps({w:[mp.nstr(x,100) for x in b] for w,b in coeff.items()},sort_keys=True,separators=(',',':'))+'\n';(P/'DH_final_coefficients_dps100.json').write_text(cp)
 t=time.process_time();A,_=src.build(119,119,'dh',160);buildcpu=time.process_time()-t
 t=time.process_time();AA=acb_mat([[arb(mp.nstr(x,100)) for x in A[i,:]] for i in range(A.rows)]);ee=AA.eig(algorithm='approx');eigcpu=time.process_time()-t
 def cv(x):
  a,b=x.mid().man_exp();return mp.ldexp(mp.mpf(int(a)),int(b))
 vals=sorted(cv(x.real) for x in ee);imag=max(abs(cv(x.imag)) for x in ee);guard=mp.mpf('1e-85')*max(1,mp.norm(A));assert imag<guard/100
 f=np.load(MATS/'cell_dh_m119.npz');diff=float(np.linalg.norm(np.array(A.tolist(),float)-f['A'],'fro'));rad=float(f['numeric_radius']);assert diff<rad
 payload=json.dumps([[mp.nstr(x,100) for x in A[i,:]] for i in range(A.rows)],separators=(',',':'))
 z=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world='dh',m=119,N=119,dps=100,GL=160,eigenvalues=[mp.nstr(x,100) for x in vals],roundoff_heuristic=mp.nstr(guard,30),quadrature_status='Fresh MP100 DH source, GL160; diagnostic quadrature, not an interval certificate',matrix_decimal_sha256=hashlib.sha256(payload.encode()).hexdigest(),source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),coefficient_sha256=hashlib.sha256(cp.encode()).hexdigest(),source_metadata=dict(build_cpu_seconds=buildcpu,origin=dict(kind='fresh_MP_source_build',path=str(SOURCE.relative_to(BASE)),input_dps=100,GL=160)),eig_cpu_seconds=eigcpu,eig_method='flint acb_mat.eig algorithm approx at400bits; independently benchmarked, NOT interval bounds',eig_bits=400,max_imaginary_part=mp.nstr(imag,40),float_matrix_difference_Frobenius=diff,float_numeric_radius=rad,plant_E_no_extra_sqrt2=None)
 file.write_text(json.dumps(z,indent=2)+'\n');timer.cancel()
 receipt=dict(status='COMPLETE',only_missing_m=119,wall_limit_seconds=30,wall_seconds=time.perf_counter()-start,CPU_seconds=time.process_time()-cpu,build_CPU=buildcpu,eig_CPU=eigcpu,method=z['eig_method'],source_file_sha256=hashlib.sha256(file.read_bytes()).hexdigest(),max_imaginary_part=z['max_imaginary_part']);(P/'FINAL119_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
