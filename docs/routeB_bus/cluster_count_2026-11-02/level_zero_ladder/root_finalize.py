"""Merge physical roots and validate m40 roots against independent precision source."""
from pathlib import Path
import json,csv,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent
rows=[];checks=[]
for m,dps in [(16,180),(24,180),(32,160),(40,180)]:
 rows+=list(csv.DictReader((P/f'root_results_m{m}_dps{dps}.csv').open()));checks+=json.loads((P/f'root_results_m{m}_dps{dps}.json').read_text())
mp.mp.dps=180;m=40;L=mp.log(m);b=L/2;omega=2*mp.pi/L
p=P/'cell_m40_dps160_gl128.json';d=json.loads(p.read_text());V=mp.matrix(d['V']);comparisons=[]
def sp(z):return (z*mp.cos(z)-mp.sin(z))/(z*z) if z else mp.mpf(0)
for r in rows:
 if int(r['m'])!=40 or r['kind']!='off_lattice':continue
 i=int(r['i']);c=[V[n,i]*(1 if n==0 else mp.sqrt(2)) for n in range(m+1)]
 def F(t):return mp.fsum(c[n]*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-n*omega)*b)+mp.sinc((t+n*omega)*b)) for n in range(m+1))
 def D(t):return mp.fsum(c[n]*(-1)**n*b*b/mp.sqrt(L)*(sp((t-n*omega)*b)+sp((t+n*omega)*b)) for n in range(m+1))
 t=mp.mpf(r['t_root']);u=mp.findroot(F,t,df=D,solver='newton',tol=mp.mpf('1e-125'),maxsteps=20)
 comparisons.append(dict(i=i,root180=r['t_root'],root160=mp.nstr(u,125),absolute_difference=mp.nstr(abs(u-t),60),direct_residual160=mp.nstr(abs(F(u)),40)))
(P/'root_validation_m40.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),comparisons=comparisons,max_absolute_root_difference=mp.nstr(max(mp.mpf(x['absolute_difference']) for x in comparisons),60)),indent=2)+'\n')
summary=dict(root_rows=len(rows),profiles=len(checks),unmatched_sign_brackets=sum(len(x['unmatched_sign_brackets']) for x in checks),max_direct_residual=mp.nstr(max(mp.mpf(r['direct_F_residual']) for r in rows),40),m40_root_comparisons=len(comparisons),m40_max_root_difference=mp.nstr(max(mp.mpf(x['absolute_difference']) for x in comparisons),60))
(P/'root_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))

# Derivative and position residual at every stored root, direct sinc off-lattice.
for m,dps,order in [(16,180,160),(24,180,160),(32,160,128),(40,180,160)]:
 mp.mp.dps=180;d=json.loads((P/f'cell_m{m}_dps{dps}_gl{order}.json').read_text());L=mp.log(m);b=L/2;omega=2*mp.pi/L;V=mp.matrix(d['V'])
 for r in rows:
  if int(r['m'])!=m:continue
  i=int(r['i']);t=mp.mpf(r['t_root']);c=[V[n,i]*(1 if n==0 else mp.sqrt(2)) for n in range(m+1)]
  derivative=mp.fsum(c[n]*(-1)**n*b*b/mp.sqrt(L)*(sp((t-n*omega)*b)+sp((t+n*omega)*b)) for n in range(m+1))
  r['direct_Fprime']=mp.nstr(derivative,70);r['estimated_position_residual']=mp.nstr(mp.mpf(r['direct_F_residual'])/abs(derivative),50) if derivative else 'undefined'
with (P/'roots.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
