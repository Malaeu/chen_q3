"""Independent exact SymPy rational LDL and integer determinant verification.
Imports no generator and consumes only the published-format dyadic payload.
"""
from pathlib import Path
import hashlib,json,time
import sympy as s
ROOT=Path(__file__).resolve().parent
expected='8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0'
p1=ROOT/'run_iv70_Q40/rational_certificate.json';p2=ROOT/'run_iv90_Q48/rational_certificate.json'
a=p1.read_bytes();b=p2.read_bytes();assert a==b
sha=hashlib.sha256(a).hexdigest();assert sha==expected,(sha,expected)
z=json.loads(a);scale=1<<z['matrix_dyadic_bits'];rows=[]
for key in ['even','odd']:
 start=time.monotonic();M=s.Matrix(z[key]);I=s.eye(M.rows);H=M-(1<<(z['matrix_dyadic_bits']-29))*I;R=H/scale
 LL,DD=R.LDLdecomposition(hermitian=False)
 assert all(DD[i,i]>0 for i in range(M.rows))
 error=LL*DD*LL.T-R;assert error==s.zeros(M.rows)
 det=H.det(method='domain-ge');assert det>0
 detsha=hashlib.sha256(str(det).encode()).hexdigest()
 claimed={'even':'d1fd3e6a268b545d0c672d6bc64ac84c9be08ec6b6368c4a74d848319f998967','odd':'5895d0a4661b117dadfbd979a6bfd4e474d8c21d1b29b368486e47d53c84362d'}[key]
 assert detsha==claimed
 rows.append(dict(parity=key,dimension=M.rows,all_positive_rational_pivots=True,exact_LDL_reconstruction=True,minimum_pivot=str(s.N(min(DD[i,i] for i in range(M.rows)),70)),integer_determinant_sha256=detsha,seconds=time.monotonic()-start))
 print(rows[-1],flush=True)
out=dict(iv70_Q40_sha256=sha,iv90_Q48_sha256=hashlib.sha256(b).hexdigest(),byte_identical=True,canonical_payload_match=True,sympy_version=s.__version__,blocks=rows)
(ROOT/'independent_exact_ldl.json').write_text(json.dumps(out,indent=2)+'\n')
