"""Numerical critical-line xi'_s bracket roots, not a completeness certificate."""
from pathlib import Path
import csv,hashlib,json,time
import mpmath as mp
mp.mp.dps=50
P=Path(__file__).resolve().parent;Z=P.parents[1]/'capacity_matrix_2026-11-02/zeros.csv'
zs=[mp.mpf(x['gamma']) for x in csv.DictReader(Z.open())];rows=[];start=time.monotonic()
# Xi(t)=−A(t)Z(t), A(t)>0, A'/A=2t/(t²+1/4)−Im psi(1/4+it/2)/2.
# Thus Xi'(t)=0 iff the following unscaled-sized function vanishes.
def scaled_derivative(t):
 return mp.siegelz(t,derivative=1)+(2*t/(t*t+mp.mpf('.25'))-mp.im(mp.digamma(mp.mpf('.25')+mp.j*t/2))/2)*mp.siegelz(t)
fmt=lambda x:mp.nstr(x,48)
rows.append(dict(index=0,t='0',left_zeta_zero='',right_zeta_zero='',scaled_derivative_residual=fmt(scaled_derivative(mp.mpf(0))),kind='symmetry_origin',scope='NUMERICAL_REFERENCE_NOT_COMPLETENESS'))
for i,(lo,hi) in enumerate(zip(zs,zs[1:]),1):
 if lo>220:break
 try:r=mp.findroot(scaled_derivative,(lo,hi),solver='anderson',tol=mp.mpf('1e-45'),maxsteps=100)
 except (ValueError,ZeroDivisionError):r=mp.findroot(scaled_derivative,(lo,hi),solver='bisect',tol=mp.mpf('1e-45'),maxsteps=180)
 assert lo<r<hi and abs(scaled_derivative(r))<mp.mpf('1e-40')
 if r>220:break
 rows.append(dict(index=i,t=fmt(r),left_zeta_zero=fmt(lo),right_zeta_zero=fmt(hi),scaled_derivative_residual=fmt(abs(scaled_derivative(r))),kind='one_root_in_known_zeta_bracket',scope='NUMERICAL_REFERENCE_NOT_COMPLETENESS'))
 print(i,fmt(r),flush=True)
with (P/'xi_prime_zeros.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
(P/'xi_prime_zeros_provenance.json').write_text(json.dumps(dict(status='NUMERICAL_CRITICAL_LINE_BRACKET_ROOTS_NOT_COMPLETENESS',dps=50,max_height=220,positive_roots=len(rows)-1,includes_origin=True,zero_table_sha256=hashlib.sha256(Z.read_bytes()).hexdigest(),code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),definition='xi_prime_s(1/2−it)=0 iff Xi_prime_t(t)=0; positive amplitude factored out using HardyZ',scope='One numerical derivative root per consecutive known positive zeta-zero bracket, through220. Does not exclude additional roots within a bracket, roots outside these brackets, multiplicities, or off-critical-line xi_prime roots.',seconds=time.monotonic()-start),indent=2)+'\n')
