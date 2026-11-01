"""Finite 80-dps diagnostics of HADAMARD_CCM (4.5),(5.3), literal edges."""
import sys,json,csv,time
from pathlib import Path
import mpmath as mp
import probe as p
mp.mp.dps=80
OUT=p.OUT
# probe's original scan was bounded by16; extend locally without editing it.
for n in range(17,21):p.trig[n]=[(mp.sin(2*mp.pi*n*y),mp.cos(2*mp.pi*n*y)) for y,w in p.nodes]
p.atoms=[(k,mp.log(k),p.mang(k)/mp.sqrt(k)) for k in range(2,21) if p.mang(k)]
def fmt(x):return mp.nstr(x,50)
def basisvector(c,N):
 return [c[abs(n)]/(mp.sqrt(2) if n else 1) for n in range(-N,N+1)]
def scalars(c,N,L):
 f=basisvector(c,N);F=mp.fsum(f)/mp.sqrt(L)
 C=[];S=[]
 for n in range(-N,N+1):
  fn=f[n+N]
  C.append(-2*fn**2-4*n*fn*mp.fsum(f[j+N]/(n-j) for j in range(-N,N+1) if j!=n))
  S.append(-4*mp.pi*n*fn**2)
 def values(r,ni=None):
  cs=[];ss=[]
  for n in range(-N,N+1):
   if ni is None:sn=mp.sin(2*mp.pi*n*r);co=mp.cos(2*mp.pi*n*r)
   else:
    sn,co=p.trig[abs(n)][ni]
    if n<0:sn=-sn
   cs.append(co);ss.append(sn)
  edge=mp.fsum(f[n+N]*cs[n+N] for n in range(-N,N+1))/mp.sqrt(L)
  qp=mp.fsum(C[n+N]*cs[n+N]+S[n+N]*(1-r)*ss[n+N] for n in range(-N,N+1))
  return edge,qp
 return F,values
def five(L,N,side=None,k=None):
 NN=max(N,12)
 K,D=p.matrices(L,NN,side,k);lam,c,gap=p.eig(K,N,NN,True)
 HF=(c.T*p.even(D,N,NN)*c)[0];F,values=scalars(c,N,L)
 uu=[];up=[]
 for j in range(N+1):
  dj=mp.sqrt(2) if j else 1
  v=4*mp.sqrt(2)*dj*L**mp.mpf('1.5')*mp.sinh(L/4)/(L**2+16*mp.pi**2*j*j)
  uu.append(v);up.append(v*(mp.mpf('1.5')/L+mp.coth(L/4)/4-2*L/(L**2+16*mp.pi**2*j*j)))
 pole=2*mp.fsum(c[j]*uu[j] for j in range(N+1))*mp.fsum(c[j]*up[j] for j in range(N+1))
 arch=mp.mpf(0);ab=mp.mpf(0)
 for ni,(r,w) in enumerate(p.nodes):
  edge,qp=values(r,ni);j=mp.exp(-L*r/2)/(-mp.expm1(-2*L*r))
  arch+=w*r*j*qp
  ab+=w*r*j*edge
 ab*=-2*F*L
 prime=mp.mpf(0);pb=mp.mpf(0)
 for atom,x,omega in p.atoms:
  include=x<L
  if atom==k:include=side=='right'
  if include:
   edge,qp=values(x/L);prime+=omega*x/L**2*qp;pb+=omega*x*edge
 pb*=-2*F/L
 terms=[pole,arch-ab,ab,prime-pb,pb];total=mp.fsum(terms)
 return dict(L=fmt(L),N=N,side=side,threshold=k,lambda0=fmt(lam),edge_squared=fmt(F**2),pole=fmt(terms[0]),arch_interior=fmt(terms[1]),arch_boundary=fmt(terms[2]),old_atom_interior=fmt(terms[3]),atom_boundary=fmt(terms[4]),sum_five=fmt(total),derivative_HF=fmt(HF),sum_minus_HF=fmt(total-HF),relative_sum_error=fmt(abs(total-HF)/abs(HF)),gap=fmt(gap))
def theta(x):
 x=abs(x);u=mp.exp(2*x);s=mp.mpf(0);n=1
 while mp.pi*n*n*u<=mp.mpf('2.4')*mp.mp.prec:
  s+=(16*mp.pi**2*n**4*u**2-24*mp.pi*n*n*u)*mp.exp(-mp.pi*n*n*u);n+=1
 return mp.exp(x/2)*s
def edge(m):
 L=mp.log(m);K,D=p.matrices(L,m,'right',m);lam,c,gap=p.eig(K,m,m,True)
 before=p.eig(K,m-1,m);F=mp.fsum((mp.sqrt(2) if j else 1)*c[j] for j in range(m+1))/mp.sqrt(L)
 # Literal L2 projection of the unnormalized h from HARDBREAK.
 weighted=[(w,theta(L*(y-mp.mpf('.5')))) for y,w in p.nodes]
 coeff=[(mp.sqrt(2) if j else 1)*mp.sqrt(L)*mp.fsum(w*h*p.trig[j][ni][1] for ni,(w,h) in enumerate(weighted)) for j in range(m+1)]
 projected_edge=mp.fsum((mp.sqrt(2) if j else 1)*coeff[j] for j in range(m+1))/mp.sqrt(L)
 return dict(m=m,L=fmt(L),lambda_m=fmt(lam),lambda_before_mode=fmt(before),ground_edge_squared=fmt(F**2),ground_edge_squared_over_lambda=fmt(F**2/lam),projected_h_edge=fmt(projected_edge),projected_h_edge_squared_over_lambda=fmt(projected_edge**2/lam),mode_jump=fmt(lam-before),mode_jump_over_lambda_right=fmt((lam-before)/lam),gap=fmt(gap))
def savecsv(path,rows):
 with path.open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
def main():
 start=time.monotonic();old=[json.loads(s) for s in (OUT/'hadamard_results.jsonl').read_text().splitlines()]
 unique={(r['L'],r['N'],r['side']):r for r in old if r['N'] in(8,12)}
 resultpath=OUT/'five_terms.jsonl'
 rows=[json.loads(s) for s in resultpath.read_text().splitlines()] if resultpath.exists() else []
 done={(r['L'],r['N'],r['side'],r['threshold']) for r in rows}
 with resultpath.open('a') as out:
  for r in sorted(unique.values(),key=lambda r:(mp.mpf(r['L']),r['N'],str(r['side']))):
   L=mp.log(r['threshold']) if r['threshold'] is not None else mp.mpf(r['L'])
   if (fmt(L),r['N'],r['side'],r['threshold']) in done:continue
   rr=five(L,r['N'],r['side'],r['threshold']);rr['derivative_FD']=r['derivative_FD'];rows.append(rr);out.write(json.dumps(rr)+'\n');out.flush()
   print('FIVE',r['L'],r['N'],r['side'],round(time.monotonic()-start,1),flush=True)
 savecsv(OUT/'five_terms.csv',rows)
 edges=[]
 with (OUT/'edge_ratios.jsonl').open('w') as out:
  for m in range(4,21):
   rr=edge(m);edges.append(rr);out.write(json.dumps(rr)+'\n');out.flush();print('EDGE',m,round(time.monotonic()-start,1),flush=True)
 savecsv(OUT/'edge_ratios.csv',edges)
 jumps=[]
 for k in range(8,17):
  for N in(8,12):
   a=[r for r in rows if r['threshold']==k and r['N']==N and r['side']=='left'][0]
   b=[r for r in rows if r['threshold']==k and r['N']==N and r['side']=='right'][0]
   predicted=-2*p.mang(k)/mp.sqrt(k)*mp.mpf(a['edge_squared'])
   hf=mp.mpf(b['derivative_HF'])-mp.mpf(a['derivative_HF']);fd=mp.mpf(b['derivative_FD'])-mp.mpf(a['derivative_FD'])
   jumps.append(dict(k=k,N=N,predicted_jump=fmt(predicted),measured_HF_jump=fmt(hf),measured_FD_jump=fmt(fd),HF_jump_abs_error=fmt(abs(hf-predicted)),FD_jump_abs_error=fmt(abs(fd-predicted)),FD_jump_relative_error=fmt(abs(fd-predicted)/abs(predicted)) if predicted else None))
 savecsv(OUT/'five_term_jumps.csv',jumps)
 (OUT/'decomposition_summary.json').write_text(json.dumps({'dps':80,'quadrature_order':p.ORDER,'five_rows':len(rows),'max_relative_five_sum_error':max(rows,key=lambda r:mp.mpf(r['relative_sum_error'])),'edges':edges,'jumps':jumps},indent=2)+'\n')
if __name__=='__main__':main()
