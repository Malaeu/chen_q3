"""Independent quiet-space kernel from polynomial divisibility and modal residues."""
from pathlib import Path
import json,csv,sys,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;BUS=P.parent

def poly_kernel(m,q,zeros):
 L=mp.log(m);omega=2*mp.pi/L;y=[mp.mpf(n*n)/(m*m) for n in range(m+1)];z=[(t/(m*omega))**2 for t in zeros[:q]];columns=[]
 for j in range(m+1-q):
  c=[]
  for n,yn in enumerate(y):
   numerator=mp.fprod(yn-v for v in z);denominator=mp.fprod(yn-v for k,v in enumerate(y) if k!=n)
   value=numerator/denominator*mp.chebyt(j,2*yn-1)/(1 if n==0 else mp.sqrt(2));c.append(value)
  v=mp.matrix(c);v/=mp.norm(v)
  for repeat in range(2):
   for u in columns:v-=u*mp.fdot(u,v)
  v/=mp.norm(v);columns.append(v)
 Q=mp.matrix(m+1,m+1-q)
 for j,v in enumerate(columns):Q[:,j]=v
 return Q

def run(m,qs):
 mp.mp.dps=220
 source=BUS/'cluster_count_2026-11-02/level_zero_ladder'/f'cell_m{m}_dps{180 if m!=32 else 160}_gl{160 if m!=32 else 128}.json'
 data=json.loads(source.read_text());A=mp.matrix(data['A']);L=mp.log(m);omega=2*mp.pi/L
 zeros=[mp.mpf(r['gamma']) for r in csv.DictReader((BUS/'capacity_matrix_2026-11-02/zeros.csv').open())]
 rows=[]
 for q in qs:
  Q=poly_kernel(m,q,zeros);AQ=A*Q;compressed=Q.T*AQ;ce=mp.eigsy(compressed,eigvals_only=True);ae=mp.eigsy(AQ.T*AQ,eigvals_only=True)
  E=mp.matrix(q,m+1)
  for j,t in enumerate(zeros[:q]):
   for n in range(m+1):E[j,n]=2*(1 if n==0 else mp.sqrt(2))*t*mp.sin(t*L/2)/(mp.sqrt(L)*(t*t-(n*omega)**2))
  result=dict(m=m,q=q,dimension=Q.cols,dps=220,kernel_residual=mp.nstr(mp.norm(E*Q),100),orthogonality_residual=mp.nstr(mp.norm(Q.T*Q-mp.eye(Q.cols)),100),full_AQ_operator_norm=mp.nstr(mp.sqrt(ae[ae.rows-1]),150),compressed_operator_norm=mp.nstr(max(abs(v) for v in ce),150),compressed_eigenvalues=[mp.nstr(v,150) for v in ce],Q=[[mp.nstr(v,210) for v in Q[i,:]] for i in range(Q.rows)],source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),scope='Algorithm validation of rounded source A; independent polynomial kernel, no exact spectral enclosure')
  rows.append(result);(P/f'validation_m{m}.json').write_text(json.dumps(rows,indent=2)+'\n');print(m,q,result['full_AQ_operator_norm'][:20],result['kernel_residual'][:20],flush=True)
if __name__=='__main__':run(int(sys.argv[1]),list(map(int,sys.argv[2:])))
