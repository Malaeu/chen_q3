"""One frozen m300 DH stale-census discriminator; numerical only."""
from pathlib import Path
import sys,json,csv,hashlib
import numpy as np, scipy.linalg as la,gmpy2 as g
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent))
from native_frame import frame
from scan_extended import events

g.get_context().precision=768;m=300;d=m+1;L=g.log(m);omega=2*g.const_pi()*m/L
oldpath=Path('/workspace/conditioning_input/dh_zeros.json');old=json.loads(oldpath.read_text());ev=[(g.mpfr(z['gamma']),g.mpfr(0),1) for z in old['critical_line_zeros']];ev += [(g.mpfr(z['gamma']),g.mpfr(z['sigma_right'])-g.mpfr('.5'),2) for z in old['off_line_pairs']];ev.sort()
rows=[];freq=[(2*g.const_pi()*j/L)**2 for j in range(d)];ds=[g.mpfr(1)]+[g.sqrt(2)]*m
for h,im,mul in ev:
 if not h<omega:continue
 t=g.mpc(h,im);fac=2*t*g.sin(t*L/2)/g.sqrt(L) if mul==2 else g.mpfr(1);raw=[fac*ds[j]/(t*t-freq[j]) for j in range(d)];rows.append([x.real for x in raw])
 if mul==2:rows.append([x.imag for x in raw])
uf,piv=frame(rows,768);W,_=la.qr(uf.T,mode='full');q=len(rows);Q=W[:,q:]
source=P.parent/'matrices/dh_m300.npz';a=np.load(source);A=a['A'];ee=a['eigenvalues'];delta=float(la.norm(A@Q,2));lam=float(ee[d-q]);guard=max(float(a['numeric_radius']),1000*np.finfo(float).eps*d*max(1,la.norm(A,2)))
qn=sum(mul for h,im,mul in events('dh') if h<omega);ln=float(ee[d-qn]);neg=-float(ee[0])
r=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,kappa=1,dimension=d,omega=str(omega),old_census_sha256=hashlib.sha256(oldpath.read_bytes()).hexdigest(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),old=dict(q=q,r=d-q,delta=delta,lambda_r=lam,gap=lam-delta,numeric_guard=guard,pass_numeric=bool(lam-delta>guard),frame_float_orthogonality=float(la.norm(uf@uf.T-np.eye(q),2)),minimum_MGS_relative_pivot=float(min(piv))),new=dict(q=qn,r=d-qn,lambda_r=ln,negative_ground_magnitude=neg,necessary_rejection=bool(ln+guard<neg-guard),delta_not_computed=True),scope='Old incomplete zero census tested as supplied; new census scalar necessary exclusion only. Numerical diagnostic, not interval bound.')
(P/'STALE_CENSUS_300.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
