"""MP endpoint carriers at epsilon1e-100 only, three fixed windows."""
from pathlib import Path
import json,hashlib
import mpmath as mp
import audit
P=Path(__file__).resolve().parent;mp.mp.dps=120;fmt=audit.fmt
for m in [16,24,40]:
 s=audit.split.build(m,256)['zeta'];C=audit.convert(s['C']);B=audit.convert(s['B']);A=C+B;eps=mp.mpf('1e-100');L=mp.cholesky(A+eps*mp.eye(m+1));Li=L**-1;H=Li*B*Li.T;H=(H+H.T)/2;he,hv=mp.eigsy(H);qmeta,Q,D,de,dv=audit.quiet(A,m,True);rows=[]
 for side,index in [('lower',he.rows-1),('upper',0)]:
  h=he[index];offset=-1/h;x=Li.T*hv[:,index];x/=mp.norm(x);y=Q.T*x;quietmass=mp.fdot(y,y);qn=mp.sqrt(quietmass);p=Q*y;amps=dv.T*y;weights=[abs(v)**2 for v in amps];order=sorted(range(len(weights)),key=lambda k:weights[k],reverse=True);top=[dict(index0=k,index1=k+1,quiet_lambda=fmt(de[k]),carrier_overlap_squared=fmt(weights[k]),fraction_of_quiet_mass=fmt(weights[k]/quietmass))for k in order[:5]];a_ray=mp.fdot(x,A*x);b_ray=mp.fdot(x,B*x);dp_ray=mp.fdot(y,D*y)/quietmass;res=(A+eps*mp.eye(m+1)+offset*B)*x
  rows.append(dict(side=side,epsilon=fmt(eps),offset=fmt(offset),whitened_eigenvalue=fmt(h),quiet_mass=fmt(quietmass),complement_mass=fmt(1-quietmass),baseline_full_A_rayleigh=fmt(a_ray),baseline_projected_D_rayleigh=fmt(dp_ray),arithmetic_B_slope=fmt(b_ray),endpoint_rayleigh=fmt(a_ray+eps+offset*b_ray),endpoint_residual_max_entry=fmt(max(abs(v)for v in res)),upper_offset_over_quiet_min=fmt(offset/de[0])if side=='upper'else None,quiet_eigenmode_overlaps=top,carrier_coefficients=[fmt(v)for v in x],quiet_coefficients=[fmt(v)for v in y]))
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,epsilon=fmt(eps),quiet=qmeta,quiet_minimum=fmt(de[0]),quiet_eigenvalues=[fmt(v)for v in de],endpoints=rows)
 (P/f'ENDPOINTS_m{m}.json').write_text(json.dumps(out,indent=2)+'\n');print(m,[(r['side'],r['quiet_mass'],r['quiet_eigenmode_overlaps'][0]['index1'],r['quiet_eigenmode_overlaps'][0]['fraction_of_quiet_mass'],r['arithmetic_B_slope'])for r in rows],flush=True)
