import numpy as np,json
from pathlib import Path
z=.25+.75j; eps=1/40
rows=[]
for L in [128.,192.,256.,384.]:
 M=int(np.exp(eps*L)); w=2*np.pi*np.arange(-M,M+1)/L
 def coef(t):
  return (np.exp((t-abs(t.real))*L/2)-np.exp((-t-abs(t.real))*L/2))/(np.sqrt(L)*(t-1j*w))
 v=coef(z); C=np.column_stack([np.ones(len(w))/np.sqrt(len(w)),coef(.5+0j),coef(-.5+0j)])
 Q,_=np.linalg.qr(C); p=v-Q@(Q.conj().T@v)
 rows.append(dict(L=L,M=M,scaled_projected_norm2=float(np.vdot(p,p).real),constraint_residual=float(np.linalg.norm(Q.conj().T@p))))
out={'status':'NONINTERVAL_PROJECTION_DIAGNOSTIC_NOT_CCM','epsilon':eps,'z':[z.real,z.imag],'predicted_limit':1/(2*z.real)-1/abs(z+.5)**2,'rows':rows}
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
