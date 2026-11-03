"""Performance-only alternative MP eigensolver validation; NOT interval certification."""
from pathlib import Path
import sys,json,time,hashlib
sys.path.insert(0,'/tmp/litdeps')
import mpmath as mp
from flint import acb_mat,ctx,arb
mp.mp.dps=110;ctx.prec=400
P=Path(__file__).resolve().parent;BASE=P.parents[3]
cases=[P/'pilot_zeta_m65_dps100_GL160.json',BASE/'fake_worlds_2026-11-02/ledger_diff/matched_cells/source_zeta_m120.json']
rows=[]
for path in cases:
 z=json.loads(path.read_text());A=acb_mat([[arb(x) for x in row] for row in z['A']]);m=int(z['m']);target=list(map(mp.mpf,z.get('eigenvalues',z.get('full_eigenvalues'))))
 t=time.perf_counter();c=time.process_time();ev=A.eig(algorithm='approx');wall=time.perf_counter()-t;cpu=time.process_time()-c
 def cv(x):
  a,b=x.mid().man_exp();return mp.ldexp(mp.mpf(int(a)),int(b))
 got=sorted(cv(x.real) for x in ev);imag=max(abs(cv(x.imag)) for x in ev);error=max(abs(x-y) for x,y in zip(got,target))
 row=dict(status='DIAGNOSTIC_NEVER_A_PROOF',algorithm='flint acb eig approx, no interval bounds',m=m,bits=400,wall_seconds=wall,cpu_seconds=cpu,max_absolute_spectrum_difference=mp.nstr(error,80),max_imaginary_part=mp.nstr(imag,80),source_path=str(path),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),eigenvalues=[mp.nstr(x,100) for x in got]);rows.append(row);print({k:v for k,v in row.items() if k!='eigenvalues'},flush=True)
(P/'fast_eigen_pilot.json').write_text(json.dumps(rows,indent=2)+'\n')
