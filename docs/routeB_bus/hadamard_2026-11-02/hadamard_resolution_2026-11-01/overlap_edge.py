"""Finite high-resolution ground-edge and theta-overlap diagnostics."""
import sys,json,time,csv
from pathlib import Path
import mpmath as mp
OUT=Path(__file__).resolve().parent
BASE=OUT.parent/'hadamard_convergence_2026-11-01'
sys.path.insert(0,str(BASE))
# Set precision/order before convergence module creates quadrature nodes.
import convergence as p
ORDER=p.ORDER;DPS=mp.mp.dps
def fmt(v):return mp.nstr(v,DPS)
def theta(x):
 x=abs(x);u=mp.exp(2*x);s=mp.mpf(0);n=1
 while mp.pi*n*n*u<=mp.mpf('2.4')*mp.mp.prec:
  s+=(16*mp.pi**2*n**4*u**2-24*mp.pi*n*n*u)*mp.exp(-mp.pi*n*n*u);n+=1
 return mp.exp(x/2)*s
def projection(L):
 hh=[theta(L*(y-mp.mpf('.5'))) for y,w in p.nodes]
 return mp.matrix([(mp.sqrt(2) if n else 1)*mp.sqrt(L)*mp.fsum(w*hh[i]*p.trig[n][i][1] for i,(y,w) in enumerate(p.nodes)) for n in range(45)])
def main():
 validation='--validation' in sys.argv
 Ns=(40,44) if validation else range(8,45)
 rows=[];start=time.monotonic()
 name=f'overlap_edge_dps{DPS}_gl{ORDER}'
 for m in(8,12,16):
  L=mp.log(m);K,D=p.matrices(L,44,'right',m);E=p.even(K,44,44);coef=projection(L)
  requests=sorted(set(Ns)|{m})
  for N in requests:
   B=E[:N+1,:N+1];ev,V=mp.eigsy(B);v=V[:,0];lam=ev[0]
   fedge=mp.fsum((mp.sqrt(2) if n else 1)*v[n] for n in range(N+1))/mp.sqrt(L)
   c=coef[:N+1,:];norm2=(c.T*c)[0];dot=(v.T*c)[0];w0=dot**2/norm2
   pedge=mp.fsum((mp.sqrt(2) if n else 1)*c[n] for n in range(N+1))/mp.sqrt(L)
   rr=dict(m=m,L=fmt(L),N=N,dps=DPS,order=ORDER,literal=N==m,lambda0=fmt(lam),ground_edge_squared=fmt(fedge**2),ground_edge_squared_over_lambda=fmt(fedge**2/lam),ground_edge_squared_over_Llambda=fmt(fedge**2/(L*lam)),w0=fmt(w0),one_minus_w0=fmt(1-w0),projection_h_norm_squared=fmt(norm2),projection_h_edge_squared_over_lambda=fmt(pedge**2/lam),eigenpair_residual=fmt(mp.norm(B*v-lam*v)),gap=fmt(ev[1]-ev[0]))
   rows.append(rr);print(json.dumps(rr),flush=True)
   (OUT/(name+'.json')).write_text(json.dumps(rows,indent=2)+'\n')
  print('DONE',m,'elapsed',round(time.monotonic()-start,2),file=sys.stderr,flush=True)
 with (OUT/(name+'.csv')).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
if __name__=='__main__':main()
