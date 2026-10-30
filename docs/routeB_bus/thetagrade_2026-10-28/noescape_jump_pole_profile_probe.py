"""Finite floating jump/pole profile diagnostic only."""
import json
import noescape_resistance_probe as p
mp=p.mp; mp.mp.dps=90
out=[]
for m in (4,8,16):
 L=mp.log(m);K=p.full_probe.matrix_K(m);E,_=p.parity_bases(m);A=E.T*K*E
 u=mp.matrix([4*mp.sqrt(2)*(1 if i==0 else mp.sqrt(2))*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*i*i) for i in range(m+1)])
 nu,V=mp.eigsy(A-u*u.T);av,cv=mp.eigsy(A);lam=av[0]
 b=V.T*u;f=V.T*cv[:,0];S=sum(b[j]**2/(nu[j]-lam) for j in range(1,m+1));T=sum(b[j]**2/(nu[j]-lam)**2 for j in range(1,m+1))
 pred=1/(1+b[0]**2*T/(1+S)**2)
 out.append(dict(m=m,complement_gap=mp.nstr(nu[1]-lam,35),upshift=mp.nstr(lam-nu[0],35),j_ground_overlap=mp.nstr(f[0]**2,35),j_pole_overlap=mp.nstr(b[0]**2/mp.fdot(u,u),35),A_norm_over_pole2=mp.nstr(max(abs(x) for x in av)/mp.fdot(u,u),35),prediction_error=mp.nstr(abs(pred-f[0]**2),8),S=mp.nstr(S,35),tail_ratio=mp.nstr(b[0]**2*T/(1+S)**2,35)))
print(json.dumps(out,indent=2))
