"""Fixed-history one-sided Schur slopes, finite differences versus exact jump formula."""
from scan import *
def run_hinges(world,hstr='.1',dps=80,only=None):
 mp.mp.dps=dps;g,atoms=g_function(world);h=mp.mpf(hstr);data=json.loads((OUT/f'{world}_h{hstr}_dps80.json').read_text());gs=list(map(mp.mpf,data['g_values']));n=len(gs)-1;LL=mp.eye(n);D=[]
 for i in range(n):
  for j in range(i):LL[i,j]=(gs[i-j]-gs[i+1]-gs[j+1]-mp.fsum(LL[i,k]*D[k]*LL[j,k] for k in range(j)))/D[j]
  D.append(-2*gs[i+1]-mp.fsum(LL[i,k]**2*D[k] for k in range(i)))
 # Probe every prime-power hinge through6, retaining every DH coefficient in g.
 ns={n for x,c,n in arithmetic('zeta')};rows=[];eps=mp.mpf('1e-6')
 for a,c,integer in atoms:
  if integer not in ns or (only is not None and integer!=only):continue
  eps=mp.mpf("1e-7") if integer==331 else mp.mpf("1e-6")
  q=int(mp.floor((a-eps)/h))
  def defect(t,alpha=False):
   gt=g(t);b=[g(t-(i+1)*h)-gt-gs[i+1] for i in range(q)];y=[]
   for i in range(q):y.append(b[i]-mp.fsum(LL[i,k]*y[k] for k in range(i)))
   val=-2*g(t)-mp.fsum(y[i]**2/D[i] for i in range(q))
   if not alpha:return val
   z=[mp.mpf(0)]*q
   for i in range(q-1,-1,-1):z[i]=y[i]/D[i]-mp.fsum(LL[k,i]*z[k] for k in range(i+1,q))
   return val,z
  at,alpha=defect(a,True);pred=-2*c+2*c*mp.fsum(alpha)
  for e in (eps,eps/2):
   left=defect(a-e);right=defect(a+e);sl=(at-left)/e;sr=(right-at)/e
   rows.append({'world':world,'h':hstr,'n':integer,'threshold':mp.nstr(a,25),'fixed_history_count':q,'epsilon':str(e),'schur_left':mp.nstr(left,35),'schur_at':mp.nstr(at,35),'schur_right':mp.nstr(right,35),'left_slope':mp.nstr(sl,25),'right_slope':mp.nstr(sr,25),'measured_jump':mp.nstr(sr-sl,25),'predicted_jump':mp.nstr(pred,25),'absolute_jump_error':mp.nstr(abs(sr-sl-pred),20)})
  if integer in (2,16,64,256):print('HINGE',world,integer,flush=True)
 if only is not None:
  rows=[r for r in csv.DictReader((OUT/f'{world}_hinges.csv').open()) if int(r['n'])!=only]+rows
  rows.sort(key=lambda r:(int(r['n']),-float(r['epsilon'])))
 with (OUT/f'{world}_hinges.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 print('HINGES DONE',world,len(rows),flush=True)
if __name__=='__main__':run_hinges(sys.argv[1],only=int(sys.argv[2]) if len(sys.argv)>2 else None)
