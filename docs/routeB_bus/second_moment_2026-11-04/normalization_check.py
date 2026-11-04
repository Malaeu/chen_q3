"""Independent even-source normalization check; no eigenproblem or zero Gram."""
import importlib.util,json,hashlib,csv
from pathlib import Path
import numpy as np
ROOT=Path('/workspace/stiffness/repo/docs/routeB_bus/ground_state_zeros_2026-11-03')
OUT=Path(__file__).resolve().parent
p=ROOT/'inputs/analytic_source.py'
s=importlib.util.spec_from_file_location('independent_ground_source',p);mod=importlib.util.module_from_spec(s);s.loader.exec_module(mod)
a,meta=mod.build(16,400)
f=Path('/workspace/second_moment/local/source/m16_q192.npz');b=np.load(f)
rows=[]
for w in ['zeta','dh','plant']:
 x=np.array(a[w][0],float);y=b[w+'_A'];tr=float(np.trace(x));f2=float(np.sum(x*x));err=float(np.max(abs(x-y)))
 rows.append(dict(world=w,m=16,dimension=17,analytic_trace=tr,arithmetic_trace=float(np.trace(y)),analytic_F2=f2,arithmetic_F2=float(np.sum(y*y)),max_entry_error=err,trace_error=float(abs(tr-np.trace(y))),F2_error=float(abs(f2-np.sum(y*y))),gate_allowance=1e-11,pass_gate=bool(err<1e-11 and abs(f2-np.sum(y*y))<1e-11)))
with (OUT/'normalization_check.csv').open('w')as h:
 wr=csv.DictWriter(h,fieldnames=list(rows[0]));wr.writeheader();wr.writerows(rows)
r=dict(status='PASS'if all(q['pass_gate']for q in rows)else'FAIL',scope='independent analytic versus arithmetic even physical matrix m16 only; not eigenpair validation',source_bits=400,analytic_metadata=meta,analytic_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),normalization_sha256=hashlib.sha256((ROOT/'NORMALIZATION.md').read_bytes()).hexdigest(),arithmetic_cache_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),rows=rows)
(OUT/'normalization_check.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
