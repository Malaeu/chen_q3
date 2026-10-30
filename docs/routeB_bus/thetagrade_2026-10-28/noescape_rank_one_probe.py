"""Finite floating diagnostic only: explicit pole-orthogonal competitor."""
import json
from pathlib import Path
records=[]
import noescape_resistance_probe as p
mp=p.mp;mp.mp.dps=90
for m in [4,8,16]:
 L=mp.log(m);K=p.full_probe.matrix_K(m);E,_=p.parity_bases(m);A=E.T*K*E
 u=mp.matrix([4*mp.sqrt(2)*(1 if i==0 else mp.sqrt(2))*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*i*i) for i in range(m+1)])
 # Scalar C shifts all J eigenvalues; diagonalize B=J-CI=A-uuT instead.
 nu,V=mp.eigsy(A-u*u.T);av,cv=mp.eigsy(A)
 e1=V[:,0];e2=V[:,1];b1=mp.fdot(u,e1);b2=mp.fdot(u,e2)
 g=(b2*e1-b1*e2)/mp.sqrt(b1*b1+b2*b2)
 rg=mp.fdot(g,A*g);gap=nu[1]-nu[0]
 records.append(dict(m=m, pole_norm_squared=mp.nstr(mp.fdot(u,u),40), gap_J=mp.nstr(gap,40), competitor_energy=mp.nstr(rg,40), bottom_energy=mp.nstr(av[0],40), excited_energy=mp.nstr(av[1],40), competitor_norm=mp.nstr(mp.norm(g),20), pole_residual=mp.nstr(mp.fdot(u,g),10), bottom_pole_moment_over_gap=mp.nstr(mp.fdot(u,cv[:,0])**2/gap,30)))
result=dict(status="FINITE_FLOATING_DIAGNOSTIC_NOT_PROOF",dps=90,records=records)
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
