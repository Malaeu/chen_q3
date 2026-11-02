"""Independent mpmath source, Householder rowspace and query solves.
Fixed native cells20/55 only; no replacement or spectral scan.
"""
from pathlib import Path
from curve import Source
import mpmath as mp,json,csv,sys,importlib.util
P=Path(__file__).resolve().parent;IN=Path(sys.argv[1]);mp.mp.dps=145
# Load the separately implemented source builder retained from EDGE_LAW_RELLICH.
helper=Path(sys.argv[2]) if len(sys.argv)>2 else P/'independent_source.py';spec=importlib.util.spec_from_file_location('independent_source',helper);src=importlib.util.module_from_spec(spec);spec.loader.exec_module(src);mp.mp.dps=145
zeros=[mp.mpf(r['gamma']) for r in csv.DictReader((IN/'zeros.csv').open())];dz=json.loads((IN/'dh_zeros_extended.json').read_text())
def erow(z,m):
 L=mp.log(m);return [2*(1 if n==0 else mp.sqrt(2))*z*mp.sin(z*L/2)/(mp.sqrt(L)*(z*z-(2*mp.pi*n/L)**2)) for n in range(m+1)]
rows=[]
for m in [20,55]:
 for world in ['zeta','dh']:
  L=mp.log(m);T=mp.mpf('1.1')*2*mp.pi*m/L;A,*_=src.build(m,world,160);E=[]
  if world=='zeta':E=[erow(z,m) for z in zeros if z<T]
  else:
   events=sorted([(mp.mpf(a['gamma']),0) for a in dz['critical_line_zeros']]+[(mp.mpf(a['gamma']),mp.mpf(a['sigma_right'])-mp.mpf('.5')) for a in dz['off_line_pairs']])
   for gamma,eta in events:
    if gamma>=T:continue
    ev=erow(gamma+mp.j*eta,m)
    if not eta:E.append([mp.re(v) for v in ev])
    else:E.extend([[mp.sqrt(2)*mp.re(v) for v in ev],[mp.sqrt(2)*mp.im(v) for v in ev]])
  E=mp.matrix(E)
  for i in range(E.rows):E[i,:]/=mp.norm(E[i,:])
  Q,R=mp.qr(E.T);U=Q[:,:E.rows];C=U.T*A*U
  queries=[mp.matrix([(1 if n==0 else mp.sqrt(2))/mp.sqrt(L) for n in range(m+1)])]+[mp.matrix(erow(mp.j*y,m)).apply(mp.re) for y in [mp.mpf('.5'),mp.mpf(1),mp.mpf(2)]]
  kval=[]
  for v in queries:
   rhs=U.T*v;x=mp.lu_solve(C,rhs);kval.append(mp.fdot(rhs,x))
  base=json.loads((P/'native_cells'/f'{world}_m{m}_dps220_gl256.json').read_text());v=mp.matrix([mp.mpf((-1)**n)/(n+1) for n in range(m+1)]);v/=mp.norm(v);ray=mp.fdot(v,A*v)
  rows.append({'world':world,'m':m,'dps':145,'order':160,'independent_K':[mp.nstr(x,130) for x in kval],'relative_K_errors':[mp.nstr(abs(x-mp.mpf(y))/abs(x),100) for x,y in zip(kval,base['K'])],'source_probe_relative_error':mp.nstr(abs(ray-mp.mpf(base['source_probe_Rayleigh']))/max(abs(ray),1),100),'constant_derivative_measure_pullback_error':mp.nstr(abs(A[0,0]-2*Source(world,300).psi(L)/L),100),'A00_nonzero_endpoint_mass_witness':mp.nstr(A[0,0],100),'U_orthogonality':mp.nstr(mp.norm(U.T*U-mp.eye(U.cols)),100)})
  print(world,m,'validated',flush=True)
assert max(mp.mpf(e) for d in rows for e in d['relative_K_errors'])<mp.mpf('1e-70')
(P/'PYTHON_NATIVE_VALIDATION.json').write_text(json.dumps({'status':'PASS','scope':'independent source/Householder/LU versus GMP MGS/LDL','rows':rows},indent=2)+'\n')
