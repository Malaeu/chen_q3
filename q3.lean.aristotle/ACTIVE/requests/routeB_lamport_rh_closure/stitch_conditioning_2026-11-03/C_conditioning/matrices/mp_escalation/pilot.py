"""DIAGNOSTIC_NEVER_A_PROOF. MP source/eigenvalue timing and validation pilot."""
from pathlib import Path
import sys,importlib.util,time,json,hashlib
sys.dont_write_bytecode=True
import mpmath as mp
import numpy as np
P=Path(__file__).resolve().parent;BASE=P.parents[3]
SOURCE=BASE/'lit_quickcheck_2026-11-03/Q2_simple_even/check.py'
spec=importlib.util.spec_from_file_location('q2_source',SOURCE);source=importlib.util.module_from_spec(spec);spec.loader.exec_module(source)
mp.mp.dps=100
rows=[];matrices={}
for order in [128,160]:
 start=time.perf_counter();cpu=time.process_time();A,_=source.build(65,65,'zeta',order)
 bt=time.perf_counter()-start;bc=time.process_time()-cpu
 start=time.perf_counter();cpu=time.process_time();ev=mp.eigsy(A,eigvals_only=True)
 et=time.perf_counter()-start;ec=time.process_time()-cpu
 f=np.load(P.parent/'cell_zeta_m65.npz');delta=float(np.linalg.norm(np.array(A.tolist(),dtype=float)-f['A'],'fro'))
 row=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world='zeta',m=65,N=65,dps=100,GL=order,source=str(SOURCE.relative_to(BASE)),source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),build_wall_seconds=bt,build_cpu_seconds=bc,eig_wall_seconds=et,eig_cpu_seconds=ec,float_matrix_difference_Frobenius=delta,float_numeric_radius=float(f['numeric_radius']),float_comparison_pass=delta<float(f['numeric_radius']),A=[[mp.nstr(x,100) for x in A[i,:]] for i in range(A.rows)],eigenvalues=[mp.nstr(x,100) for x in ev])
 (P/f'pilot_zeta_m65_dps100_GL{order}.json').write_text(json.dumps(row,indent=2)+'\n');rows.append({k:v for k,v in row.items() if k not in ('A','eigenvalues')});matrices[order]=(A,ev)
 print(json.dumps(rows[-1]),flush=True)
A,e=matrices[128];B,d=matrices[160]
error=mp.norm(A-B);eigerror=max(abs(x-y) for x,y in zip(e,d))
summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',runs=rows,matrix_refinement_Frobenius=mp.nstr(error,80),maximum_eigenvalue_refinement_difference=mp.nstr(eigerror,80),eigenvalue_relative_changes=[mp.nstr(abs(x-y)/abs(y),50) if y else None for x,y in zip(e,d)])
(P/'pilot_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('VALIDATION',summary['matrix_refinement_Frobenius'],summary['maximum_eigenvalue_refinement_difference'],flush=True)
